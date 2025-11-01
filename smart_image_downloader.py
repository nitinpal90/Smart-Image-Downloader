"""
SmartImageDownloader.py
A friendly GUI tool to download product images into folder-per-row.
First column = folder path/name (absolute or relative), remaining columns = image URLs.

Features:
- Paste tabular data (copy from Excel) OR upload Excel (.xlsx/.xls) OR CSV.
- Heuristics to try to get higher-quality images (e.g. strip thumbnail query, swap "thumb" -> "large", try drive/dropbox conversion).
- Concurrency with progress bar and retries.
- Options for naming files (original filename, barcode+index, numeric index).
- Save/Load session (JSON) so multiple people can reuse configurations.
- Nice ttk interface, logs, and report at finish.
"""

import os
import re
import json
import csv
import threading
import queue
import time
from urllib.parse import urlparse, urlunparse, parse_qs, urlencode, urlsplit, urljoin
from concurrent.futures import ThreadPoolExecutor, as_completed

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText

import requests

# optional pandas for Excel support
try:
    import pandas as pd
    PANDAS_AVAILABLE = True
except Exception:
    PANDAS_AVAILABLE = False

APP_NAME = "Smart Image Downloader"
VERSION = "1.2"

# -------------------- Utilities -------------------- #
def sanitize_folder_name(name):
    # keep cross-platform safe characters
    return re.sub(r'[<>:"/\\|?*\n\r]+', "_", name).strip() or "untitled"

def try_drive_direct(url):
    # convert share link to direct download where possible
    if "drive.google.com" in url:
        m = re.search(r'/d/([a-zA-Z0-9_-]+)', url)
        if m:
            return f"https://drive.google.com/uc?export=download&id={m.group(1)}"
        # also handle id= style
        m2 = re.search(r'id=([a-zA-Z0-9_-]+)', url)
        if m2:
            return f"https://drive.google.com/uc?export=download&id={m2.group(1)}"
    if "dropbox.com" in url:
        return url.replace("?dl=0", "?dl=1").replace("?dl=1?dl=0", "?dl=1")
    return url

def quality_variants(url):
    """
    Yield a sequence of candidate URLs to try, starting with the original,
    then some heuristic modifications that often produce higher-quality images.
    This is heuristic — safe to try since we simply attempt HTTP GET.
    """
    url = url.strip()
    yield url

    # Drive/Dropbox conversion
    d = try_drive_direct(url)
    if d != url:
        yield d

    # Remove query strings (sometimes they force small size)
    parsed = urlsplit(url)
    if parsed.query:
        noq = urlunparse((parsed.scheme, parsed.netloc, parsed.path, "", "", ""))
        yield noq

    # Replace common thumbnail tokens with 'large' / remove size constraints
    replacements = [
        (r"/thumbs?/", "/"),
        (r"/thumbnail/", "/"),
        (r"/small/", "/"),
        (r"=s\d+$", "=s0"),  # googleusercontent size param, s0 often gives full size
        (r"=s\d+-c$", "=s0"),
        (r"_[0-9]{2,4}x[0-9]{2,4}", ""),  # file_200x200
        (r"w_\d+,h_\d+,c_fill", "w_0,h_0"),  # cloudinary style
        (r"w_\d+", "w_0"),
        (r"q_\d+,", ""),  # quality param removal
    ]
    candidate = url
    for pattern, repl in replacements:
        new = re.sub(pattern, repl, candidate)
        if new != candidate:
            candidate = new
            yield candidate

    # Some hosts use /_m/ or /m/ for medium. Try removing /m/ or /_m/
    yield re.sub(r"/(_?m|_?s)/", "/", url)

    # If path contains 'thumb' or 'small' replace with 'orig' or 'large'
    p = parsed.path
    if "thumb" in p or "small" in p:
        yield url.replace("thumb", "large").replace("small", "large").replace("_thumb", "")

    # last fallback: strip fragment & params
    yield url.split("?", 1)[0].split("#", 1)[0]

def detect_extension(url, headers=None):
    # Attempt extension from url path
    parsed = urlsplit(url)
    path = parsed.path
    ext = os.path.splitext(path)[1]
    if ext and len(ext) <= 6:
        return ext
    # Try content type
    if headers:
        ct = headers.get("Content-Type", "")
        if "png" in ct:
            return ".png"
        if "webp" in ct:
            return ".webp"
        if "jpeg" in ct or "jpg" in ct:
            return ".jpg"
        if "gif" in ct:
            return ".gif"
    return ".jpg"

def safe_filename_from_url(url):
    parsed = urlsplit(url)
    base = os.path.basename(parsed.path) or "image"
    base = re.sub(r'[^A-Za-z0-9._-]', '_', base)
    return base

# -------------------- Downloader Worker -------------------- #
class Downloader:
    def __init__(self, base_folder, rows, options, log_fn, progress_fn):
        """
        rows: list of lists (first col=folder, other cols=image urls)
        options: dict of settings (workers, retries, timeout, naming, save_overwrite)
        """
        self.base_folder = base_folder
        self.rows = rows
        self.options = options
        self.log = log_fn
        self.progress = progress_fn

        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "SmartImageDownloader/1.0 (+https://example.com)"
        })

    def _prepare_links(self, row):
        # row is list of cells
        # If only one column but contains newline-separated URLs, try that
        if len(row) == 1 and "\n" in row[0]:
            parts = [p.strip() for p in row[0].splitlines() if p.strip()]
            if len(parts) >= 2:
                # first is folder, others links
                return parts[0], parts[1:]
        folder = str(row[0]).strip()
        links = []
        for c in row[1:]:
            if c is None:
                continue
            s = str(c).strip()
            if s:
                links.append(s)
        return folder, links

    def _attempt_download(self, url, dest, index):
        retries = self.options.get("retries", 2)
        timeout = self.options.get("timeout", 18)
        for attempt in range(1, retries + 2):
            try:
                resp = self.session.get(url, stream=True, timeout=timeout, allow_redirects=True)
                if resp.status_code != 200:
                    raise Exception(f"HTTP {resp.status_code}")
                # simple check for HTML content (often means a landing page)
                ct = resp.headers.get("Content-Type", "")
                if "text/html" in ct:
                    raise Exception("Returned HTML (not image)")
                ext = detect_extension(url, resp.headers)
                # choose destination path
                if dest.endswith(os.sep):
                    filename = f"image_{index}{ext}"
                    dest_path = os.path.join(dest, filename)
                else:
                    dest_path = dest

                # if we only have directory, build path
                os.makedirs(os.path.dirname(dest_path) or ".", exist_ok=True)

                # avoid overwriting unless requested
                if not self.options.get("overwrite", False) and os.path.exists(dest_path):
                    # append suffix
                    base, ext0 = os.path.splitext(dest_path)
                    i = 1
                    while os.path.exists(dest_path):
                        dest_path = f"{base}_{i}{ext0}"
                        i += 1

                with open(dest_path, "wb") as f:
                    for chunk in resp.iter_content(1024 * 64):
                        if chunk:
                            f.write(chunk)
                return True, dest_path
            except Exception as e:
                last_err = str(e)
                time.sleep(0.6)  # small backoff
                continue
        return False, last_err

    def run(self):
        total_links = 0
        # expand rows into list of tasks: (folder_path, url, naming_hint)
        tasks = []
        for row_idx, row in enumerate(self.rows, start=1):
            folder_raw, links = self._prepare_links(row)
            if not folder_raw:
                folder_raw = f"row_{row_idx}"
            # allow absolute path: if folder contains os.sep at start or drive letter
            if os.path.isabs(folder_raw):
                folder_path = folder_raw
            else:
                safe = sanitize_folder_name(folder_raw)
                folder_path = os.path.join(self.base_folder, safe)
            for url in links:
                tasks.append((folder_path, url, folder_raw))
                total_links += 1

        if total_links == 0:
            self.log("⚠️ No links to download.")
            return {"success": 0, "failed": 0, "total": 0}

        max_workers = max(1, int(self.options.get("workers", 6)))
        successes = 0
        failures = 0
        self.log(f"Starting downloads: {total_links} images across {len(set([t[0] for t in tasks]))} folders.")
        progress_count = 0
        self.progress(0, total_links)

        # use thread pool
        with ThreadPoolExecutor(max_workers=max_workers) as ex:
            future_to_task = {}
            for t in tasks:
                folder_path, url, naming = t
                os.makedirs(folder_path, exist_ok=True)

                # build candidate filenames according to naming option
                naming_opt = self.options.get("naming", "auto")  # auto, original, baseindex
                if naming_opt == "original":
                    # attempt to use original filename
                    fname = safe_filename_from_url(url)
                    dest = os.path.join(folder_path, fname)
                    # submit worker that tries quality variants
                    future_to_task[ex.submit(self._download_with_variants, url, dest)] = (folder_path, url)
                elif naming_opt == "barcode_index":
                    # use sanitized folder name (assuming barcode) + index
                    # index will be assigned in worker
                    # pass folder only and worker will generate numbered names
                    future_to_task[ex.submit(self._download_with_variants_to_folder, url, folder_path)] = (folder_path, url)
                else:
                    # auto: try original filename and numeric fallback
                    fname = safe_filename_from_url(url)
                    dest = os.path.join(folder_path, fname)
                    future_to_task[ex.submit(self._download_with_variants, url, dest)] = (folder_path, url)

            # collect results as they finish
            for fut in as_completed(future_to_task):
                folder_path, url = future_to_task[fut]
                try:
                    ok, info = fut.result()
                except Exception as e:
                    ok = False
                    info = str(e)
                progress_count += 1
                if ok:
                    successes += 1
                    self.log(f"✅ {os.path.basename(info)}  (folder: {folder_path})")
                else:
                    failures += 1
                    self.log(f"❌ Failed: {url}  —  {info}")
                self.progress(progress_count, total_links)

        self.log(f"\nDone. Success: {successes}  Failed: {failures}")
        return {"success": successes, "failed": failures, "total": total_links}

    def _download_with_variants(self, url, dest):
        """
        Try candidate URL variants in order; return (True, saved_path) or (False, error)
        """
        for candidate in quality_variants(url):
            ok, info = self._attempt_download(candidate, dest, index=1)
            if ok:
                return True, info
        return False, info

    def _download_with_variants_to_folder(self, url, folder):
        """
        Save into folder with sequential numbering image_1.jpg, image_2 etc.
        """
        # Count existing images to generate index
        existing = [f for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]
        idx = len(existing) + 1
        for candidate in quality_variants(url):
            ok, info = self._attempt_download(candidate, folder + os.sep, index=idx)
            if ok:
                return True, info
        return False, info

# -------------------- Parsing inputs -------------------- #
def parse_pasted_text(text):
    """Return list of rows (list of cells). Accepts tab-separated, comma-separated, or line-per-item."""
    text = text.strip("\n\r ")
    if not text:
        return []
    # detect tabs
    lines = text.splitlines()
    # if first line contains tabs, parse as TSV
    if any("\t" in ln for ln in lines):
        reader = csv.reader(lines, delimiter="\t")
        return [[c.strip() for c in row] for row in reader]
    # if lines contain commas parse as CSV
    if any("," in ln for ln in lines):
        reader = csv.reader(lines)
        return [[c.strip() for c in row] for row in reader]
    # otherwise, treat each line as a single column
    return [[ln.strip()] for ln in lines if ln.strip()]

def parse_csv(path):
    with open(path, newline="", encoding="utf-8") as fh:
        reader = csv.reader(fh)
        rows = []
        for row in reader:
            rows.append([c.strip() for c in row])
        return rows

def parse_excel(path):
    if not PANDAS_AVAILABLE:
        raise RuntimeError("pandas/openpyxl required for Excel import.")
    df = pd.read_excel(path, engine="openpyxl")
    rows = []
    for _, row in df.iterrows():
        cells = []
        for v in row.tolist():
            if pd.isna(v):
                cells.append("")
            else:
                cells.append(str(v).strip())
        rows.append(cells)
    # drop empty rows
    rows = [r for r in rows if any(c for c in r)]
    return rows

# -------------------- GUI -------------------- #
class App:
    def __init__(self, root):
        self.root = root
        root.title(f"{APP_NAME} — v{VERSION}")
        self._make_style()
        self._build_ui()

        self.rows = None
        self.session_path = None

        # log queue to ensure thread safe updates
        self.log_queue = queue.Queue()
        self.root.after(100, self._process_log_queue)

    def _make_style(self):
        style = ttk.Style(self.root)
        # use default theme but configure some
        try:
            style.theme_use('clam')
        except Exception:
            pass
        style.configure("TButton", padding=6)
        style.configure("Header.TLabel", font=("Segoe UI", 11, "bold"))
        style.configure("Small.TLabel", font=("Segoe UI", 9))

    def _build_ui(self):
        # Top frame: base folder and session
        top = ttk.Frame(self.root, padding=(10,10))
        top.pack(fill="x")

        ttk.Label(top, text="Output Base Folder:", style="Header.TLabel").grid(row=0, column=0, sticky="w")
        self.base_var = tk.StringVar()
        self.base_entry = ttk.Entry(top, textvariable=self.base_var, width=60)
        self.base_entry.grid(row=0, column=1, sticky="we", padx=6)
        ttk.Button(top, text="Browse", command=self.choose_base).grid(row=0, column=2, sticky="e", padx=6)
        ttk.Button(top, text="Open Folder", command=self.open_base).grid(row=0, column=3, sticky="e")

        # Session buttons
        ttk.Button(top, text="Save Session", command=self.save_session).grid(row=1, column=2, pady=(8,0))
        ttk.Button(top, text="Load Session", command=self.load_session).grid(row=1, column=3, pady=(8,0))

        # Middle frame: Paste / Upload
        mid = ttk.LabelFrame(self.root, text="Input Data (First col = folder, other cols = image URLs)", padding=(10,10))
        mid.pack(fill="both", expand=True, padx=10, pady=10)

        self.paste_text = ScrolledText(mid, height=12)
        self.paste_text.pack(fill="both", expand=True)

        btnrow = ttk.Frame(mid)
        btnrow.pack(fill="x", pady=(8,0))
        ttk.Button(btnrow, text="Load Excel/CSV", command=self.load_table_file).pack(side="left")
        ttk.Button(btnrow, text="Paste Example", command=self.insert_example).pack(side="left", padx=6)
        ttk.Button(btnrow, text="Clear", command=lambda: self.paste_text.delete("1.0", "end")).pack(side="left", padx=6)

        # Options panel
        opts = ttk.LabelFrame(self.root, text="Options", padding=(10,10))
        opts.pack(fill="x", padx=10, pady=(0,10))

        self.workers_var = tk.IntVar(value=6)
        self.retries_var = tk.IntVar(value=2)
        self.timeout_var = tk.IntVar(value=18)
        self.overwrite_var = tk.BooleanVar(value=False)
        self.naming_var = tk.StringVar(value="auto")

        ttk.Label(opts, text="Workers:").grid(row=0, column=0, sticky="w")
        ttk.Spinbox(opts, from_=1, to=32, textvariable=self.workers_var, width=5).grid(row=0, column=1, sticky="w", padx=6)
        ttk.Label(opts, text="Retries:").grid(row=0, column=2, sticky="w")
        ttk.Spinbox(opts, from_=0, to=6, textvariable=self.retries_var, width=5).grid(row=0, column=3, sticky="w", padx=6)
        ttk.Label(opts, text="Timeout (s):").grid(row=0, column=4, sticky="w")
        ttk.Spinbox(opts, from_=5, to=60, textvariable=self.timeout_var, width=5).grid(row=0, column=5, sticky="w", padx=6)
        ttk.Checkbutton(opts, text="Overwrite files", variable=self.overwrite_var).grid(row=0, column=6, sticky="w", padx=10)

        ttk.Label(opts, text="Filename mode:").grid(row=1, column=0, sticky="w", pady=(8,0))
        ttk.Radiobutton(opts, text="Auto (try original)", variable=self.naming_var, value="auto").grid(row=1, column=1, sticky="w", pady=(8,0))
        ttk.Radiobutton(opts, text="Original name", variable=self.naming_var, value="original").grid(row=1, column=2, sticky="w", pady=(8,0))
        ttk.Radiobutton(opts, text="FolderName_index (good for barcode)", variable=self.naming_var, value="barcode_index").grid(row=1, column=3, columnspan=3, sticky="w", pady=(8,0))

        # Actions
        action = ttk.Frame(self.root)
        action.pack(fill="x", padx=10, pady=(0,10))
        self.start_btn = ttk.Button(action, text="Start Download", command=self.start_download)
        self.start_btn.pack(side="left")
        ttk.Button(action, text="Load Demo Data", command=self.load_demo).pack(side="left", padx=6)
        ttk.Button(action, text="Open Output", command=self.open_base).pack(side="left", padx=6)

        # Progress & log
        prog_frame = ttk.Frame(self.root)
        prog_frame.pack(fill="both", expand=True, padx=10, pady=(0,10))

        self.progress = ttk.Progressbar(prog_frame, orient="horizontal", mode="determinate")
        self.progress.pack(fill="x", padx=4, pady=6)
        self.status_var = tk.StringVar(value="Idle")
        ttk.Label(prog_frame, textvariable=self.status_var, style="Small.TLabel").pack(anchor="w")

        self.logbox = ScrolledText(prog_frame, height=10, state="disabled")
        self.logbox.pack(fill="both", expand=True, pady=(6,0))

    # ---------- UI helpers ----------
    def choose_base(self):
        folder = filedialog.askdirectory()
        if folder:
            self.base_var.set(folder)

    def open_base(self):
        path = self.base_var.get().strip()
        if not path:
            messagebox.showinfo("No folder", "Choose an output base folder first.")
            return
        if os.path.exists(path):
            try:
                if os.name == "nt":
                    os.startfile(path)
                elif os.name == "posix":
                    os.system(f'xdg-open "{path}" >/dev/null 2>&1 &')
                else:
                    messagebox.showinfo("Open folder", f"Open: {path}")
            except Exception:
                messagebox.showinfo("Open folder", f"Open: {path}")
        else:
            messagebox.showerror("Missing", "Selected base folder does not exist.")

    def insert_example(self):
        example = (
            "FolderA\thttps://example.com/img1.jpg\thttps://example.com/img2.jpg\n"
            "1234567890123\thttps://media.example.com/thumbnail/123.jpg\thttps://drive.google.com/file/d/ID/view?usp=sharing\n"
            "C:\\absolute\\path\\FolderZ\thttps://example.com/product_small.jpg\n"
        )
        self.paste_text.delete("1.0", "end")
        self.paste_text.insert("1.0", example)

    def load_table_file(self):
        path = filedialog.askopenfilename(filetypes=[("Excel and CSV", "*.xlsx *.xls *.csv"), ("All files", "*.*")])
        if not path:
            return
        try:
            if path.lower().endswith(".csv"):
                rows = parse_csv(path)
            else:
                rows = parse_excel(path)
            if not rows:
                messagebox.showwarning("Empty", "No data found in file.")
                return
            # show preview in paste box
            preview = "\n".join(["\t".join(r) for r in rows[:200]])
            self.paste_text.delete("1.0", "end")
            self.paste_text.insert("1.0", preview)
            self.rows = rows
            messagebox.showinfo("Loaded", f"Loaded {len(rows)} rows. Preview shown in box.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load file: {e}")

    def load_demo(self):
        self.insert_example()

    def save_session(self):
        # save config and pasted text
        path = filedialog.asksaveasfilename(defaultextension=".sid", filetypes=[("Smart Downloader Session", "*.sid"), ("JSON", "*.json")])
        if not path:
            return
        data = {
            "base": self.base_var.get(),
            "pasted": self.paste_text.get("1.0", "end"),
            "workers": self.workers_var.get(),
            "retries": self.retries_var.get(),
            "timeout": self.timeout_var.get(),
            "overwrite": self.overwrite_var.get(),
            "naming": self.naming_var.get()
        }
        try:
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(data, fh, indent=2)
            messagebox.showinfo("Saved", f"Session saved to {path}")
        except Exception as e:
            messagebox.showerror("Error", f"Could not save: {e}")

    def load_session(self):
        path = filedialog.askopenfilename(filetypes=[("Smart Downloader Session", "*.sid *.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            self.base_var.set(data.get("base", ""))
            self.paste_text.delete("1.0", "end")
            self.paste_text.insert("1.0", data.get("pasted", ""))
            self.workers_var.set(data.get("workers", 6))
            self.retries_var.set(data.get("retries", 2))
            self.timeout_var.set(data.get("timeout", 18))
            self.overwrite_var.set(data.get("overwrite", False))
            self.naming_var.set(data.get("naming", "auto"))
            messagebox.showinfo("Loaded", "Session loaded.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load: {e}")

    def _log(self, msg):
        # thread-safe enqueue
        self.log_queue.put(msg)

    def _process_log_queue(self):
        while True:
            try:
                msg = self.log_queue.get_nowait()
            except queue.Empty:
                break
            self.logbox.configure(state="normal")
            self.logbox.insert("end", msg + "\n")
            self.logbox.see("end")
            self.logbox.configure(state="disabled")
        self.root.after(150, self._process_log_queue)

    def start_download(self):
        base = self.base_var.get().strip()
        if not base:
            messagebox.showerror("Choose output", "Choose an Output Base Folder first.")
            return
        os.makedirs(base, exist_ok=True)
        text = self.paste_text.get("1.0", "end").strip()
        if not text and not self.rows:
            messagebox.showerror("No data", "Paste table data or load Excel/CSV first.")
            return
        rows = self.rows if self.rows else parse_pasted_text(text)
        if not rows:
            messagebox.showerror("No rows", "No rows found in input.")
            return

        # Confirm start
        if not messagebox.askyesno("Start", f"Start downloading {len(rows)} rows into\n{base} ?"):
            return

        # prepare options
        options = {
            "workers": self.workers_var.get(),
            "retries": self.retries_var.get(),
            "timeout": self.timeout_var.get(),
            "overwrite": self.overwrite_var.get(),
            "naming": self.naming_var.get()
        }

        # disable UI while running
        self.start_btn.config(state="disabled")
        self.status_var.set("Starting...")
        self.progress["value"] = 0
        self.logbox.configure(state="normal")
        self.logbox.delete("1.0", "end")
        self.logbox.configure(state="disabled")

        # run in background thread
        threading.Thread(target=self._run_downloader, args=(base, rows, options), daemon=True).start()

    def _run_downloader(self, base, rows, options):
        def logfn(msg):
            self._log(msg)
        def progfn(done, total):
            # update progressbar in main thread
            try:
                percent = int(done / total * 100) if total else 0
            except Exception:
                percent = 0
            self.root.after(10, lambda: self.progress.configure(value=percent))
            self.root.after(10, lambda: self.status_var.set(f"Progress: {done}/{total}"))
        dl = Downloader(base, rows, options, logfn, progfn)
        result = dl.run()
        # finish UI updates
        self.root.after(100, lambda: self.start_btn.config(state="normal"))
        self.root.after(100, lambda: self.status_var.set(f"Finished — {result['success']} success, {result['failed']} failed"))
        # small summary dialog
        self._log("\nSession summary:")
        self._log(json.dumps(result, indent=2))

# ---------- Run ----------
def main():
    root = tk.Tk()
    app = App(root)
    # set a minimum size
    root.minsize(900, 700)
    root.mainloop()

if __name__ == "__main__":
    main()
