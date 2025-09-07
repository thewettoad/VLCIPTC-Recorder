# vlciptv_recorder.py
# VLCIPTV Recorder — Windowed, custom buffers (checkbox + minutes), safe-stop,
# fragmented MP4 option, EPG (future-only) with lookahead bound, weekly scheduler wrapper,
# multi-stream recording, kbps/fps progress, quality explainer, widened listboxes,
# background schtasks with timeout + force overwrite, scheduled list (multi-select) + cancel,
# and a Series Info pane that shows all tasks belonging to the same series.

import os, re, sys, io, json, gzip, time, threading, subprocess, urllib.request, datetime as dt
import shutil, zipfile, tempfile
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import xml.etree.ElementTree as ET
from difflib import get_close_matches
from csv import reader as csv_reader
from io import StringIO

APP_TITLE = "VLCIPTV Recorder"

# Correctly define the configuration file location in a user-writable folder
CONFIG_DIR = os.path.join(os.environ.get("LOCALAPPDATA", os.getcwd()), "VLCIPTVRecorder")
CONFIG_FILE = os.path.join(CONFIG_DIR, "vlciptv_recorder_config.json")

DEFAULTS = {
    "m3u_url": "",
    "epg_url": "",
    "out_dir": r"D:\DVR Recordings",
    "quality": "High",
    "last_filename": "",
    "series_days": 30,
    "crash_safe_mp4": False,
    "buf_start_enabled": True,
    "buf_end_enabled": True,
    "buf_start_min": 5,
    "buf_end_min": 5,
}

UA = "VLC/3.0.20"

QUALITY_OPTS = {
    "High":   {"mode": "copy"},  # stream copy
    "Medium": {"mode": "trans", "v_bitrate": "4500k", "a_bitrate": "128k"},
    "Low":    {"mode": "trans", "v_bitrate": "2500k", "a_bitrate": "96k"},
}

ASCII_ART = r"""
████████╗██╗  ██╗███████╗██╗    ██╗███████╗████████╗████████╗ ███████╗ █████╗ ██████╗ 
╚══██╔══╝██║  ██║██╔════╝██║    ██║██╔════╝╚══██╔══╝╚══██╔══╝██╔═══██║██╔══██╗██╔══██╗
   ██║   ███████║█████╗  ██║ █╗ ██║█████╗     ██║      ██║   ██║   ██║███████║██║  ██║
   ██║   ██╔══██║██╔══╝  ██║███╗██║██╔══╝     ██║      ██║   ██║   ██║██╔══██║██║  ██║
   ██║   ██║  ██║███████╗╚███╔███╔╝███████╗   ██║      ██║   ╚██████╔╝██║  ██║██████╔╝
   ╚═╝   ╚═╝  ╚═╝╚══════╝ ╚══╝╚══╝ ╚══════╝   ╚═╝      ╚═╝    ╚═════╝ ╚═╝  ╚═╝╚═════╝ 

                  THEWETTOAD CREATIONS PRESENTS:  VLCIPTV RECORDER
"""

# ---------- theme ----------
BG       = "#0b1220"
CARD_BG  = "#0f172a"
TXT      = "#e5e7eb"
SUBTXT   = "#93a4bd"
LOG_BG   = "#0b1220"
LOG_TXT  = "#d1d5db"

# ------------------- config helpers -------------------
def load_cfg():
    try:
        if os.path.exists(CONFIG_FILE):
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                d = json.load(f)
            for k,v in DEFAULTS.items(): d.setdefault(k, v)
            return d
    except Exception:
        pass
    return DEFAULTS.copy()

def save_cfg(cfg):
    try:
        ensure_dir(CONFIG_DIR)
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2)
    except Exception:
        pass

def ensure_dir(p): os.makedirs(p, exist_ok=True)

# ------------------- net helpers -------------------
def fetch_bytes(url, timeout=60):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()

def fetch_text(url, timeout=60, fallback="utf-8"):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        ct = r.headers.get("Content-Type","")
        enc = fallback
        m = re.search(r"charset=([\w\-]+)", ct)
        if m: enc = m.group(1)
        data = r.read()
    try:
        return data.decode(enc, errors="replace")
    except Exception:
        return data.decode(fallback, errors="replace")

# ------------------- playlist / epg -------------------
def parse_m3u(txt):
    lines = [ln.strip() for ln in txt.splitlines()]
    out = []
    ext = None
    for ln in lines:
        if ln.startswith("#EXTINF"): ext = ln
        elif ln and not ln.startswith("#"):
            if ext:
                name = ext.split(",",1)[-1].strip()
                tvg = ""
                grp = ""
                m = re.search(r'tvg-id="([^"]+)"', ext)
                if m: tvg = m.group(1)
                m = re.search(r'group-title="([^"]+)"', ext)
                if m: grp = m.group(1)
                out.append({"name":name, "tvg_id":tvg, "group":grp, "url":ln, "ext":ext})
                ext = None
    return out

def tokenscore(hay, q):
    hay = hay.lower(); q = q.lower().strip()
    score = 0
    if q in hay: score += 40
    for t in q.split():
        if t in hay: score += 10
    return score

def parse_duration(s):
    s = s.strip().lower()
    if re.fullmatch(r"\d+:\d{2}:\d{2}", s):
        h,m,sec = map(int, s.split(":")); return h*3600 + m*60 + sec
    m = re.fullmatch(r"(?:(\d+)h)?(?:(\d+)m)?(?:(\d+)s)?", s)
    if m and any(m.groups()):
        h = int(m.group(1) or 0); mi = int(m.group(2) or 0); se = int(m.group(3) or 0)
        return h*3600 + mi*60 + se
    if s.isdigit(): return int(s)*60
    raise ValueError("Use 02:05:00, 125, or 2h5m")

def xmltv_load(epg_url):
    raw = fetch_bytes(epg_url)
    if epg_url.lower().endswith(".gz") or (len(raw)>2 and raw[:2]==b"\x1f\x8b"):
        raw = gzip.decompress(raw)
    root = ET.parse(io.BytesIO(raw)).getroot()
    chmap = {}
    for ch in root.findall("channel"):
        cid = ch.get("id") or ""
        names = [dn.text for dn in ch.findall("display-name") if dn.text]
        chmap[cid] = {"id":cid, "names":names}
    progs = []
    for pr in root.findall("programme"):
        cid = pr.get("channel") or ""
        st  = pr.get("start") or ""
        en  = pr.get("stop") or ""
        title = (pr.findtext("title") or "").strip()
        desc  = (pr.findtext("desc") or "").strip()
        progs.append({"channel":cid, "start":st, "stop":en, "title":title, "desc":desc})
    return chmap, progs

def xmltv_to_local(ts):
    ts = ts.replace(" ","")
    m = re.match(r"(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})([+\-]\d{4}|Z)?", ts)
    if not m: return None
    y,M,d,h,mi,s = map(int, m.groups()[:6]); tz = m.group(7)
    base = dt.datetime(y,M,d,h,mi,s)
    if tz and tz.upper()!="Z":
        sign = 1 if tz[0]=="+" else -1
        offh = int(tz[1:3]); offm = int(tz[3:5])
        return (base - dt.timedelta(hours=sign*offh, minutes=sign*offm)).replace(tzinfo=dt.timezone.utc).astimezone().replace(tzinfo=None)
    return base.replace(tzinfo=dt.timezone.utc).astimezone().replace(tzinfo=None)

def fmt_bytes(n):
    return f"{n/1024/1024/1024:.2f} GB" if n>=1024**3 else f"{n/1024/1024:.1f} MB"

def fmt_hms(total_sec):
    s = max(0, int(total_sec))
    h = s // 3600
    m = (s % 3600) // 60
    ss = s % 60
    return f"{h:01d}:{m:02d}:{ss:02d}"

# ------------------- FFmpeg bootstrap -------------------
def try_ffmpeg_in_path():
    try:
        subprocess.run(["ffmpeg","-version"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        return "ffmpeg"
    except Exception:
        return None

def ffmpeg_default_locations():
    locs = [r"C:\FFmpeg\bin\ffmpeg.exe"]
    local = os.environ.get("LOCALAPPDATA")
    if local:
        locs.append(os.path.join(local, "FFmpeg", "bin", "ffmpeg.exe"))
    return locs

def ffmpeg_exists_here():
    for p in ffmpeg_default_locations():
        if os.path.exists(p):
            return p
    return None

def ensure_writable_dir(path):
    try:
        os.makedirs(path, exist_ok=True)
        testfile = os.path.join(path, ".__wtest")
        with open(testfile, "wb") as f: f.write(b"x")
        os.remove(testfile)
        return True
    except Exception:
        return False

def install_ffmpeg_silently(status_callback=None):
    def say(msg):
        if status_callback: status_callback(msg)
    base_candidates = [r"C:\FFmpeg"]
    local = os.environ.get("LOCALAPPDATA")
    if local:
        base_candidates.append(os.path.join(local, "FFmpeg"))
    target_base = None
    for base in base_candidates:
        if ensure_writable_dir(base):
            target_base = base; break
    if not target_base:
        raise RuntimeError("No writable location for FFmpeg install.")
    say(f"Installing FFmpeg to {target_base} …")
    tmpdir = tempfile.mkdtemp(prefix="ffmzip_")
    zpath = os.path.join(tmpdir, "ffmpeg-release-essentials.zip")
    url = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"
    say("Downloading FFmpeg…")
    with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": UA}), timeout=180) as r:
        with open(zpath, "wb") as f: shutil.copyfileobj(r, f)
    say("Extracting…")
    with zipfile.ZipFile(zpath, "r") as z:
        z.extractall(tmpdir)
    extracted_root = None
    for name in os.listdir(tmpdir):
        p = os.path.join(tmpdir, name)
        if os.path.isdir(p) and name.startswith("ffmpeg-") and name.endswith("essentials_build"):
            extracted_root = p; break
    if not extracted_root:
        raise RuntimeError("Could not locate extracted FFmpeg folder.")
    for item in os.listdir(extracted_root):
        src = os.path.join(extracted_root, item)
        dst = os.path.join(target_base, item)
        if os.path.exists(dst):
            if os.path.isdir(dst): shutil.rmtree(dst, ignore_errors=True)
            else:
                try: os.remove(dst)
                except Exception: pass
        shutil.move(src, dst)
    shutil.rmtree(tmpdir, ignore_errors=True)
    ffmpeg_path = os.path.join(target_base, "bin", "ffmpeg.exe")
    if not os.path.exists(ffmpeg_path):
        raise RuntimeError("FFmpeg install incomplete.")
    say("FFmpeg installed.")
    return ffmpeg_path

def ensure_ffmpeg(status_callback=None):
    path_ff = try_ffmpeg_in_path()
    if path_ff: return path_ff
    here = ffmpeg_exists_here()
    if here: return here
    return install_ffmpeg_silently(status_callback=status_callback)

# ------------------- threading helper -------------------
class Worker(threading.Thread):
    def __init__(self, fn, *args, done=None):
        super().__init__(daemon=True)
        self.fn=fn; self.args=args; self.err=None; self.result=None; self.done=done
    def run(self):
        try:
            self.result = self.fn(*self.args)
        except Exception as e:
            self.err = e
        finally:
            if callable(self.done):
                try: self.done(self)
                except Exception: pass

# ------------------- ffmpeg command builder -------------------
def build_ffmpeg_cmd(ffmpeg, stream_url, out_path, duration_s, qopt, crash_safe=False):
    base = [ffmpeg, "-hide_banner", "-loglevel", "info", "-stats",
            "-user_agent", UA,
            "-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_at_eof", "1",
            "-i", stream_url, "-t", str(int(duration_s))]
    if qopt["mode"] == "copy":
        mov = "+faststart"
        if crash_safe:
            mov += "+frag_keyframe+empty_moov+default_base_moof"
        base += ["-c","copy","-movflags",mov, out_path]
    else:
        mov = "+faststart"
        if crash_safe:
            mov = "+faststart+frag_keyframe+empty_moov+default_base_moof"
        base += ["-map","0:v:0?","-map","0:a:0?",
                 "-c:v","libx264","-preset","veryfast","-b:v",qopt["v_bitrate"], "-maxrate",qopt["v_bitrate"], "-bufsize","2M",
                 "-c:a","aac","-b:a",qopt["a_bitrate"], "-movflags", mov, out_path]
    return base

# ------------------- safe finalize -------------------
def finalize_recording(ffmpeg_path, file_path):
    if not os.path.exists(file_path):
        return
    try:
        fixed_path = file_path + ".fixed.mp4"
        cmd = [ffmpeg_path or "ffmpeg", "-y", "-i", file_path, "-c", "copy", "-movflags", "+faststart", fixed_path]
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False, timeout=30)
        if os.path.exists(fixed_path):
            os.replace(fixed_path, file_path)
    except Exception:
        pass

# ------------------- schtasks helpers -------------------
def run_schtasks(args, timeout=15):
    try:
        proc = subprocess.run(args, capture_output=True, text=True, shell=False, timeout=timeout)
        return proc.returncode, proc.stdout, proc.stderr
    except subprocess.TimeoutExpired:
        return 124, "", "ERROR: schtasks timed out."
    except Exception as e:
        return 125, "", f"ERROR: {e}"

def parse_schtasks_csv(csv_text):
    rows = []
    try:
        if isinstance(csv_text, bytes):
            try:
                csv_text = csv_text.decode("utf-16le")
            except Exception:
                csv_text = csv_text.decode("utf-8", errors="replace")
        f = StringIO(csv_text)
        rdr = list(csv_reader(f))
        if not rdr: return rows
        headers = [h.strip() for h in rdr[0]]
        for r in rdr[1:]:
            if len(r) != len(headers): continue
            rows.append({headers[i]: r[i] for i in range(len(headers))})
    except Exception:
        pass
    return rows

# ------------------- Scrollable container -------------------
class ScrollableFrame(ttk.Frame):
    def __init__(self, parent):
        super().__init__(parent)
        self.canvas = tk.Canvas(self, highlightthickness=0, bg=BG)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.vsb.grid(row=0, column=1, sticky="ns")
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)
        self.body = ttk.Frame(self.canvas, style="Card.TFrame")
        self.body_id = self.canvas.create_window((0,0), window=self.body, anchor="nw")
        self.body.bind("<Configure>", self._on_body_configure)
        self.canvas.bind("<Configure>", self._on_canvas_configure)
        self.canvas.bind_all("<MouseWheel>", self._on_mousewheel)
    def _on_body_configure(self, _): self.canvas.configure(scrollregion=self.canvas.bbox("all"))
    def _on_canvas_configure(self, event): self.canvas.itemconfigure(self.body_id, width=event.width)
    def _on_mousewheel(self, event): self.canvas.yview_scroll(int(-1*(event.delta/120)), "units")

# ------------------- GUI app -------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.withdraw()
        self.title(APP_TITLE)
        self.geometry("1400x980")
        self.configure(bg=BG)
        self.protocol("WM_DELETE_WINDOW", self.on_app_close)
        self.show_splash(self._finish_init)

    def _finish_init(self):
        style = ttk.Style(self); style.theme_use("default")
        style.configure("TLabel", background=BG, foreground=TXT, font=("Segoe UI",10))
        style.configure("Small.TLabel", background=BG, foreground=SUBTXT, font=("Segoe UI",9))
        style.configure("TButton", font=("Segoe UI",10,"bold"))
        style.configure("Card.TFrame", background=CARD_BG, relief="ridge", borderwidth=1)
        style.configure("Header.TLabel", background=BG, foreground=TXT, font=("Segoe UI Semibold",14))

        self.cfg = load_cfg(); ensure_dir(self.cfg["out_dir"])
        self.ffmpeg_path = None
        self.m3u_entries = []
        self.chmap, self.progs = {}, []
        self.epg_ready = False
        self.tasks_index = []  # [(name, next_run, schedule, status)]

        self.scroll = ScrollableFrame(self)
        self.scroll.pack(fill="both", expand=True)
        self.build_ui(self.scroll.body)

        self.deiconify(); self.update_idletasks()
        w,h = self.winfo_width(), self.winfo_height()
        x = (self.winfo_screenwidth()-w)//2; y = (self.winfo_screenheight()-h)//2
        self.geometry(f"{w}x{h}+{x}+{y}")
        self.lift(); self.focus_force()

        self.bootstrap_ffmpeg()
        self.load_playlist()
        self.load_epg()
        self.refresh_tasks_async()

    # --- Splash window ---
    def show_splash(self, on_close_callback):
        splash = tk.Toplevel(self)
        splash.overrideredirect(True)
        splash.configure(bg=BG)
        splash.attributes("-topmost", True)

        art_lines = ASCII_ART.strip("\n").splitlines()
        art_width = max(len(line) for line in art_lines)
        char_w, char_h = 8, 18
        w = min(art_width * char_w + 60, self.winfo_screenwidth() - 100)
        h = min(len(art_lines) * char_h + 120, self.winfo_screenheight() - 100)

        self.update_idletasks()
        x = (self.winfo_screenwidth()-w)//2
        y = (self.winfo_screenheight()-h)//3
        splash.geometry(f"{w}x{h}+{x}+{y}")

        tk.Label(splash, text="VLCIPTV Recorder", fg=TXT, bg=BG, font=("Segoe UI Semibold", 16)).pack(pady=(12, 6))
        txt = tk.Text(splash, bg=BG, fg="#93c5fd", bd=0, relief="flat", font=("Consolas", 10))
        txt.insert("1.0", ASCII_ART.strip("\n")); txt.config(state="disabled")
        txt.pack(fill="both", expand=True, padx=16, pady=(0, 6))
        tk.Label(splash, text="Launching…", fg=SUBTXT, bg=BG, font=("Segoe UI", 10)).pack(pady=(0, 12))

        def close_splash():
            if splash.winfo_exists(): splash.destroy()
            try: on_close_callback()
            except Exception: pass
        splash.bind("<Button-1>", lambda e: close_splash())
        self.after(3500, close_splash)

    def on_app_close(self):
        """Saves the configuration and destroys the window when the app is closed."""
        self.cfg["m3u_url"] = self.m3u_var.get().strip()
        self.cfg["epg_url"] = self.epg_var.get().strip()
        self.cfg["out_dir"] = self.outdir_var.get().strip()
        self.cfg["quality"] = self.quality_var.get()
        self.cfg["crash_safe_mp4"] = self.crash_safe_var.get()
        self.cfg["buf_start_enabled"] = self.buf_start_var.get()
        self.cfg["buf_end_enabled"] = self.buf_end_var.get()
        self.cfg["buf_start_min"] = self.buf_start_min.get()
        self.cfg["buf_end_min"] = self.buf_end_min.get()
        
        save_cfg(self.cfg)
        self.destroy()

    def build_ui(self, root):
        for c in (0,1): root.grid_columnconfigure(c, weight=1)
        root.grid_rowconfigure(5, weight=1)

        ttk.Label(root, text="VLCIPTV Recorder", style="Header.TLabel").grid(row=0, column=0, sticky="w", padx=16, pady=(16,8), columnspan=2)

        # Top settings
        top = ttk.Frame(root, style="Card.TFrame"); top.grid(row=1, column=0, columnspan=2, sticky="ew", padx=16, pady=8)
        for c in range(4): top.grid_columnconfigure(c, weight=1 if c==1 else 0)

        ttk.Label(top, text="M3U URL:").grid(row=0, column=0, sticky="w", padx=8, pady=6)
        self.m3u_var = tk.StringVar(value=self.cfg["m3u_url"])
        self.e_m3u = ttk.Entry(top, textvariable=self.m3u_var)
        self.e_m3u.grid(row=0, column=1, sticky="ew", padx=8)
        self.e_m3u.bind("<Return>", lambda e: self.load_playlist())
        self.btn_reload_m3u = ttk.Button(top, text="Reload", command=self.load_playlist)
        self.btn_reload_m3u.grid(row=0, column=2, padx=8)

        ttk.Label(top, text="EPG XMLTV URL (.xml/.gz):").grid(row=1, column=0, sticky="w", padx=8, pady=6)
        self.epg_var = tk.StringVar(value=self.cfg["epg_url"])
        self.e_epg = ttk.Entry(top, textvariable=self.epg_var) # Corrected to be enabled by default
        self.e_epg.grid(row=1, column=1, sticky="ew", padx=8)
        self.btn_reload_epg = ttk.Button(top, text="Reload EPG", command=self.load_epg)
        self.btn_reload_epg.grid(row=1, column=2, padx=8)

        ttk.Label(top, text="Quality:").grid(row=2, column=0, sticky="w", padx=8, pady=6)
        self.quality_var = tk.StringVar(value=self.cfg["quality"])
        qcb = ttk.Combobox(top, values=list(QUALITY_OPTS.keys()), textvariable=self.quality_var, width=10, state="readonly")
        qcb.grid(row=2, column=1, sticky="w", padx=8)
        self.quality_help = ttk.Label(top, text="", style="Small.TLabel")
        self.quality_help.grid(row=2, column=2, columnspan=2, sticky="w", padx=8)
        def _update_qhelp(*_):
            q = self.quality_var.get()
            if q == "High":
                msg = "High: Stream copy (no re-encode). Best quality, lowest CPU, largest file."
            elif q == "Medium":
                msg = "Medium: Transcode ~4.5 Mbps video / 128 kbps audio. Smaller file, some CPU."
            else:
                msg = "Low: Transcode ~2.5 Mbps video / 96 kbps audio. Smallest file, most CPU."
            self.quality_help.configure(text=msg)
        self.quality_var.trace_add("write", _update_qhelp); _update_qhelp()

        # Output & Naming
        outf = ttk.Frame(root, style="Card.TFrame"); outf.grid(row=2, column=0, columnspan=2, sticky="ew", padx=16, pady=8)
        outf.grid_columnconfigure(1, weight=1)
        ttk.Label(outf, text="Output folder:").grid(row=0, column=0, sticky="w", padx=8, pady=(10,6))
        self.outdir_var = tk.StringVar(value=self.cfg["out_dir"])
        ttk.Entry(outf, textvariable=self.outdir_var).grid(row=0, column=1, sticky="ew", padx=8, pady=(10,6))
        ttk.Button(outf, text="Browse…", command=self.pick_folder).grid(row=0, column=2, padx=8, pady=(10,6))

        ttk.Label(outf, text="Custom filename (optional; .mp4 added):").grid(row=1, column=0, sticky="w", padx=8, pady=6)
        self.filename_var = tk.StringVar(value=self.cfg.get("last_filename",""))
        self.filename_entry = ttk.Entry(outf, textvariable=self.filename_var, width=40)
        self.filename_entry.grid(row=1, column=1, sticky="w", padx=8, pady=6)

        # Crash-safe MP4 (fragmented)
        self.crash_safe_var = tk.BooleanVar(value=bool(self.cfg.get("crash_safe_mp4", False)))
        ttk.Checkbutton(outf, text="Crash-safe MP4 (fragmented)", variable=self.crash_safe_var).grid(row=1, column=2, sticky="w", padx=8)

        self.preview_lbl = ttk.Label(outf, text="Will save as: …", style="Small.TLabel")
        self.preview_lbl.grid(row=2, column=0, columnspan=3, sticky="w", padx=8, pady=(2,10))

        # Series Options (only lookahead)
        so = ttk.Frame(root, style="Card.TFrame"); so.grid(row=3, column=0, sticky="ew", padx=16, pady=8)
        for c in (0,1): so.grid_columnconfigure(c, weight=1 if c==1 else 0)
        ttk.Label(so, text="Lookahead (days):").grid(row=0, column=0, sticky="e", padx=8, pady=(10,6))
        self.series_days_var = tk.IntVar(value=int(self.cfg.get("series_days", 30)))
        ttk.Entry(so, textvariable=self.series_days_var, width=8).grid(row=0, column=1, sticky="w", padx=(0,8), pady=(10,6))

        # EPG Search (left)
        showf = ttk.Frame(root, style="Card.TFrame"); showf.grid(row=4, column=0, sticky="nsew", padx=16, pady=8)
        showf.grid_columnconfigure(1, weight=1)
        showf.grid_columnconfigure(3, weight=3)
        ttk.Label(showf, text="Show title (EPG search):").grid(row=0, column=0, sticky="e", padx=(8,4), pady=(8,2))
        self.show_var = tk.StringVar()
        self.entry_show = ttk.Entry(showf, textvariable=self.show_var)
        self.entry_show.grid(row=0, column=1, sticky="ew", padx=(0,8), pady=(8,2))
        self.entry_show.bind("<Return>", lambda e: self.search_show())
        self.btn_find_epg = ttk.Button(showf, text="Find", command=self.search_show)
        self.btn_find_epg.grid(row=0, column=2, padx=(0,8), pady=(8,2))
        self.btn_clear_epg = ttk.Button(showf, text="Clear", command=self.clear_epg_search)
        self.btn_clear_epg.grid(row=0, column=3, sticky="w", pady=(8,2))
        self.btn_use_show = ttk.Button(showf, text="Use selected (auto-fill)", command=self.use_show_pick)
        self.btn_use_show.grid(row=1, column=1, sticky="w", padx=(0,8), pady=(0,8))

        show_list_frame = ttk.Frame(showf, style="Card.TFrame")
        show_list_frame.grid(row=1, column=3, rowspan=2, sticky="nsew", padx=8, pady=8)
        show_list_frame.grid_rowconfigure(0, weight=1)
        show_list_frame.grid_columnconfigure(0, weight=1)
        self.show_list = tk.Listbox(show_list_frame, height=22, width=60)
        self.show_list.grid(row=0, column=0, sticky="nsew")
        sb1y = ttk.Scrollbar(show_list_frame, orient="vertical", command=self.show_list.yview)
        sb1x = ttk.Scrollbar(show_list_frame, orient="horizontal", command=self.show_list.xview)
        self.show_list.configure(yscrollcommand=sb1y.set, xscrollcommand=sb1x.set)
        sb1y.grid(row=0, column=1, sticky="ns")
        sb1x.grid(row=1, column=0, sticky="ew")
        self.show_list.bind("<Double-1>", self.on_show_double_click)

        # Channel Search (right)
        manual = ttk.Frame(root, style="Card.TFrame"); manual.grid(row=4, column=1, sticky="nsew", padx=16, pady=8)
        manual.grid_columnconfigure(1, weight=1)
        manual.grid_columnconfigure(3, weight=3)
        ttk.Label(manual, text="Channel search:").grid(row=0, column=0, sticky="e", padx=(8,4), pady=(8,2))
        self.search_var = tk.StringVar()
        self.entry_channel = ttk.Entry(manual, textvariable=self.search_var)
        self.entry_channel.grid(row=0, column=1, sticky="ew", padx=(0,8), pady=(8,2))
        self.entry_channel.bind("<Return>", lambda e: self.search_channels())
        self.btn_find_channel = ttk.Button(manual, text="Find", command=self.search_channels)
        self.btn_find_channel.grid(row=0, column=2, padx=(0,8), pady=(8,2))
        self.btn_clear_channel = ttk.Button(manual, text="Clear", command=self.clear_channel_search)
        self.btn_clear_channel.grid(row=0, column=3, sticky="w", pady=(8,2))

        chan_list_frame = ttk.Frame(manual, style="Card.TFrame")
        chan_list_frame.grid(row=1, column=3, rowspan=6, sticky="nsew", padx=8, pady=8)
        chan_list_frame.grid_rowconfigure(0, weight=1)
        chan_list_frame.grid_columnconfigure(0, weight=1)
        self.chan_list = tk.Listbox(chan_list_frame, height=22, width=48)
        self.chan_list.grid(row=0, column=0, sticky="nsew")
        sb2y = ttk.Scrollbar(chan_list_frame, orient="vertical", command=self.chan_list.yview)
        sb2x = ttk.Scrollbar(chan_list_frame, orient="horizontal", command=self.chan_list.xview)
        self.chan_list.configure(yscrollcommand=sb2y.set, xscrollcommand=sb2x.set)
        sb2y.grid(row=0, column=1, sticky="ns")
        sb2x.grid(row=1, column=0, sticky="ew")
        self.chan_list.bind("<<ListboxSelect>>", lambda e: self.update_output_preview())

        ttk.Label(manual, text="Day (today / tomorrow / YYYY-MM-DD):").grid(row=1, column=0, sticky="e", padx=8)
        self.day_var = tk.StringVar(value="today")
        ttk.Entry(manual, textvariable=self.day_var, width=18).grid(row=1, column=1, sticky="w", padx=8)

        ttk.Label(manual, text="Time (e.g., 20:00 or 8:00 pm):").grid(row=2, column=0, sticky="e", padx=8)
        self.time_var = tk.StringVar(value="20:00")
        ttk.Entry(manual, textvariable=self.time_var, width=18).grid(row=2, column=1, sticky="w", padx=8)

        ttk.Label(manual, text="Duration (02:05:00, 125, or 2h5m):").grid(row=3, column=0, sticky="e", padx=8)
        self.dur_var = tk.StringVar(value="")
        ttk.Entry(manual, textvariable=self.dur_var, width=18).grid(row=3, column=1, sticky="w", padx=8)

        # Buffers (checkbox + minutes)
        bufrow = ttk.Frame(manual, style="Card.TFrame")
        bufrow.grid(row=4, column=0, columnspan=3, sticky="w", padx=8, pady=(4,8))
        self.buf_start_var = tk.BooleanVar(value=bool(self.cfg.get("buf_start_enabled", True)))
        self.buf_end_var   = tk.BooleanVar(value=bool(self.cfg.get("buf_end_enabled", True)))
        self.buf_start_min = tk.IntVar(value=int(self.cfg.get("buf_start_min", 5)))
        self.buf_end_min   = tk.IntVar(value=int(self.cfg.get("buf_end_min", 5)))

        ttk.Checkbutton(bufrow, text="Start buffer", variable=self.buf_start_var,
                          command=self.update_output_preview).grid(row=0, column=0, sticky="w", padx=(0,6))
        tk.Spinbox(bufrow, from_=0, to=120, width=4, textvariable=self.buf_start_min,
                       command=self.update_output_preview).grid(row=0, column=1, sticky="w")
        ttk.Label(bufrow, text="min").grid(row=0, column=2, sticky="w", padx=(4,16))

        ttk.Checkbutton(bufrow, text="End buffer", variable=self.buf_end_var,
                          command=self.update_output_preview).grid(row=0, column=3, sticky="w", padx=(0,6))
        tk.Spinbox(bufrow, from_=0, to=120, width=4, textvariable=self.buf_end_min,
                       command=self.update_output_preview).grid(row=0, column=4, sticky="w")
        ttk.Label(bufrow, text="min").grid(row=0, column=5, sticky="w")

        # Actions
        actions = ttk.Frame(root); actions.grid(row=5, column=0, columnspan=2, sticky="ew", padx=16, pady=8)
        ttk.Button(actions, text="Arm & Record (Add to Schedule)", command=self.arm_record).pack(side="left", padx=6)
        ttk.Button(actions, text="Schedule Weekly", command=lambda: self.schedule_task_async(recurring=True)).pack(side="left", padx=6)
        ttk.Button(actions, text="Series Record (schedule upcoming)", command=self.series_record_async).pack(side="left", padx=6)
        ttk.Button(actions, text="Exit", command=self.destroy).pack(side="right", padx=6)

        self.status = ttk.Label(root, text="Initializing…", style="Small.TLabel")
        self.status.grid(row=6, column=0, columnspan=2, sticky="w", padx=16, pady=(0,6))

        # Scheduled Records panel (bottom)
        tasksf = ttk.Frame(root, style="Card.TFrame"); tasksf.grid(row=7, column=0, columnspan=2, sticky="nsew", padx=16, pady=(4,12))
        tasksf.grid_columnconfigure(0, weight=3)
        tasksf.grid_columnconfigure(1, weight=2)

        ttk.Label(tasksf, text="Scheduled Records").grid(row=0, column=0, sticky="w", padx=8, pady=(8,2))
        self.tasks_list = tk.Listbox(tasksf, height=8, selectmode=tk.EXTENDED)
        self.tasks_list.grid(row=1, column=0, sticky="nsew", padx=8)
        self.tasks_list.bind("<Double-1>", self.on_task_double_click)
        self.tasks_list.bind("<<ListboxSelect>>", self.on_task_select)

        side = ttk.Frame(tasksf, style="Card.TFrame")
        side.grid(row=1, column=1, sticky="nsew", padx=8)
        side.grid_rowconfigure(3, weight=1)
        ttk.Button(side, text="Refresh", command=self.refresh_tasks_async).grid(row=0, column=0, sticky="ew", padx=6, pady=(8,4))
        ttk.Button(side, text="Cancel Selected", command=self.cancel_task_async).grid(row=1, column=0, sticky="ew", padx=6, pady=4)
        ttk.Label(side, text="Series Info (select one series task)").grid(row=2, column=0, sticky="w", padx=6, pady=(10,2))
        self.series_info = tk.Listbox(side, height=6)
        self.series_info.grid(row=3, column=0, sticky="nsew", padx=6, pady=(0,8))

        self._set_epg_controls_enabled(False)
        self._bind_preview_updates()
        self.update_output_preview()

    def _bind_preview_updates(self):
        for var in (self.outdir_var, self.filename_var, self.day_var, self.time_var, self.buf_start_min, self.buf_end_min):
            try: var.trace_add("write", lambda *args: self.update_output_preview())
            except Exception: pass

    def _set_epg_controls_enabled(self, enabled: bool):
        state = ("normal" if enabled else "disabled")
        for w in (self.e_epg, self.btn_reload_epg, getattr(self, "entry_show", None), getattr(self, "btn_find_epg", None),
                  getattr(self, "btn_clear_epg", None), getattr(self, "btn_use_show", None)):
            try:
                if w: w.configure(state=state)
            except Exception:
                pass

    def _auto_filename(self, ch_name: str, start_at: dt.datetime) -> str:
        safe = re.sub(r"[^A-Za-z0-9._-]+","_", ch_name)[:60]
        base = f"{safe}_{start_at.strftime('%Y-%m-%d_%H-%M')}.mp4"
        return re.sub(r"\.+(?=\.mp4$)", "", base, flags=re.I)

    def _current_channel_name(self) -> str:
        idx = self.chan_list.curselection()
        if not idx: return "Recording"
        return self.chan_list.get(idx[0]) or "Recording"

    def _preview_start_time(self):
        try:
            base = self._parse_when()
        except Exception:
            return None
        if self.buf_start_var.get():
            try: mins = max(0, int(self.buf_start_min.get()))
            except Exception: mins = 0
            base = base - dt.timedelta(minutes=mins)
        return base

    def update_output_preview(self):
        out_dir = (self.outdir_var.get() or "").strip() or self.cfg.get("out_dir","")
        start_at = self._preview_start_time()
        ch_name = self._current_channel_name()
        fname = (self.filename_var.get() or "").strip()
        if not fname:
            fname = self._auto_filename(ch_name, start_at or dt.datetime.now())
        if not fname.lower().endswith(".mp4"): fname += ".mp4"
        path = os.path.join(out_dir, fname) if out_dir else fname
        self.preview_lbl.configure(text=f"Will save as: {path}")

    def bootstrap_ffmpeg(self):
        self.status["text"] = "Checking FFmpeg…"
        def work():
            try:
                return ensure_ffmpeg(status_callback=lambda msg: self.status.configure(text=msg))
            except Exception as e:
                return ("ERR", str(e))
        w = Worker(work, done=self._after_ffmpeg); w.start()

    def _after_ffmpeg(self, w):
        if isinstance(w.result, tuple) and w.result and w.result[0] == "ERR":
            self.status["text"] = f"FFmpeg setup failed: {w.result[1]}"
        else:
            self.ffmpeg_path = w.result
            self.status["text"] = f"FFmpeg ready: {self.ffmpeg_path}"

    def load_playlist(self):
        url = self.m3u_var.get().strip()
        self.status["text"] = "Loading playlist…"
        self.btn_reload_m3u.configure(state="disabled")
        def work():
            try:
                return parse_m3u(fetch_text(url))
            except Exception as e:
                return ("ERR", str(e))
        Worker(work, done=self._after_playlist).start()

    def _after_playlist(self, w):
        self.btn_reload_m3u.configure(state="normal")
        if isinstance(w.result, list):
            self.m3u_entries = w.result
            self.status["text"] = f"Playlist loaded: {len(self.m3u_entries)} channels."
            self.fill_channels(self.m3u_entries[:200])
        else:
            self.status["text"] = f"Failed to load M3U: {w.result[1] if w.result else 'unknown error'}"

    def load_epg(self):
        url = self.epg_var.get().strip()
        if not url:
            self.status["text"] = "EPG URL missing."
            return
        self.status["text"] = "Loading EPG…"
        self.e_epg.configure(state="disabled")
        self.btn_reload_epg.configure(state="disabled")
        def work():
            try:
                return xmltv_load(url)
            except Exception as e:
                return ("ERR", str(e))
        Worker(work, done=self._after_epg).start()

    def _after_epg(self, w):
        self.e_epg.configure(state="normal")
        self.btn_reload_epg.configure(state="normal")
        if isinstance(w.result, tuple) and len(w.result)==2:
            self.chmap, self.progs = w.result
            self.status["text"] = f"EPG loaded: {len(self.chmap)} channels, {len(self.progs)} programmes."
            self.epg_ready = True
            self._set_epg_controls_enabled(True)
        else:
            self.status["text"] = f"Failed to load EPG: {w.result[1] if w.result else 'unknown error'}"
            self.epg_ready = False
            self._set_epg_controls_enabled(False)

    def pick_folder(self):
        d = filedialog.askdirectory(initialdir=self.outdir_var.get())
        if d:
            self.outdir_var.set(d)

    def fill_channels(self, entries):
        self.chan_list.delete(0, tk.END)
        for e in entries:
            self.chan_list.insert(tk.END, e['name'])
        self.update_output_preview()

    def clear_channel_search(self):
        self.search_var.set("")
        self.fill_channels(self.m3u_entries[:200])

    def search_channels(self):
        q = self.search_var.get().strip()
        if not q:
            self.fill_channels(self.m3u_entries[:200]); return
        scored = []
        for e in self.m3u_entries:
            hay = f"{e['name']} {e['tvg_id']} {e['group']} {e['ext']}"
            s = tokenscore(hay, q)
            if s>0: scored.append((s,e))
        scored.sort(key=lambda x:x[0], reverse=True)
        self.fill_channels([e for _,e in scored[:200]])

    def get_selected_channel(self):
        idx = self.chan_list.curselection()
        if not idx: return None
        visible_name = self.chan_list.get(idx[0])
        for e in self.m3u_entries:
            if e["name"] == visible_name: return e
        for e in self.m3u_entries:
            if e["name"].startswith(visible_name): return e
        return None

    def clear_epg_search(self):
        self.show_var.set("")
        self.show_list.delete(0, tk.END)

    def search_show(self):
        if not self.epg_ready:
            messagebox.showinfo(APP_TITLE, "EPG not loaded yet."); return
        q = self.show_var.get().strip()
        self.show_list.delete(0, tk.END)
        if not q: return
        lookahead_days = max(1, int(self.series_days_var.get()))
        cutoff = dt.datetime.now() + dt.timedelta(days=lookahead_days)
        rows = epg_search_rows(self.progs, self.chmap, q, cutoff_dt=cutoff)
        if not rows:
            suggestions = epg_title_suggestions(self.progs, q, k=8)
            if suggestions:
                self.show_list.insert(tk.END, "No exact matches. Try:")
                for s in suggestions:
                    self.show_list.insert(tk.END, f">> {s}")
            else:
                self.show_list.insert(tk.END, "No matches.")
            return
        for row in rows:
            self.show_list.insert(tk.END, row)

    def on_show_double_click(self, event):
        try:
            if not self.show_list.curselection():
                return
            row = self.show_list.get(self.show_list.curselection()[0]).strip()
            m = re.match(r"^>>\s+(.+)$", row)
            if m:
                self.show_var.set(m.group(1))
                self.search_show()
                return
            self.use_show_pick()
        except Exception as e:
            messagebox.showwarning(APP_TITLE, f"Could not use the selected show.\n\nReason: {e}")

    def use_show_pick(self):
        def _norm(s: str) -> str:
            return re.sub(r'[^a-z0-9]+', '', (s or '').lower())

        idx = self.show_list.curselection()
        if not idx:
            messagebox.showwarning(APP_TITLE, "Select a show first.")
            return

        row = self.show_list.get(idx[0]).strip()
        if not row or row.startswith("No exact") or row.startswith("Try") or row.startswith(">>"):
            return

        try:
            parts = [p.strip() for p in row.split("|")]
            if len(parts) < 3:
                raise ValueError("Unexpected row format. Try clicking a result line, not a header/suggestion.")

            when_part = parts[0]
            chname    = parts[1]
            if " - " not in when_part:
                raise ValueError("Missing time range in the EPG row.")

            start_str = when_part.split(" - ", 1)[0].strip()
            end_str   = when_part.split(" - ", 1)[1].strip()

            day_part, time_part = start_str.split(" ", 1)
            self.day_var.set(day_part)
            self.time_var.set(time_part)

            best, best_s = None, -1
            ch_norm = _norm(chname)
            for e in self.m3u_entries:
                s = tokenscore(e["name"], chname)
                if e["name"] == chname:
                    s += 100
                elif _norm(e["name"]) == ch_norm:
                    s += 70
                elif e.get("tvg_id") and _norm(e["tvg_id"]) == ch_norm:
                    s += 50
                if s > best_s:
                    best_s, best = s, e

            if best:
                self.search_var.set(chname)
                self.search_channels()
                for i in range(self.chan_list.size()):
                    if self.chan_list.get(i) == best["name"]:
                        self.chan_list.selection_clear(0, tk.END)
                        self.chan_list.selection_set(i)
                        self.chan_list.see(i)
                        break

            m = re.fullmatch(r"(\d{2}):(\d{2})", end_str.split()[0])
            if m:
                eh, em = int(m.group(1)), int(m.group(2))
                start_dt = dt.datetime.strptime(start_str, "%Y-%m-%d %H:%M")
                end_dt = start_dt.replace(hour=eh, minute=em)
                if end_dt < start_dt:
                    end_dt += dt.timedelta(days=1)
                dur = int((end_dt - start_dt).total_seconds())
                self.dur_var.set(f"{dur//3600:02d}:{(dur%3600)//60:02d}:{dur%60:02d}")

            self.update_output_preview()
        except Exception as e:
            messagebox.showwarning(APP_TITLE, f"Could not use the selected show.\n\nReason: {e}")

    def _parse_when(self):
        day = self.day_var.get().strip().lower()
        now = dt.datetime.now()
        if day in ("","today"): base = now
        elif day == "tomorrow": base = now + dt.timedelta(days=1)
        else: base = dt.datetime.strptime(day, "%Y-%m-%d")
        m = re.fullmatch(r"(\d{1,2}):(\d{2})(?:\s*(am|pm))?", self.time_var.get().strip().lower())
        if not m: raise ValueError("Time examples: 20:00 or 8:00 pm")
        hh,mm = int(m.group(1)), int(m.group(2)); ap=m.group(3)
        if ap == "pm" and hh!=12: hh+=12
        if ap == "am" and hh==12: hh=0
        return base.replace(hour=hh, minute=mm, second=0, microsecond=0)

    def _ensure_future_start(self, start_at: dt.datetime):
        now = dt.datetime.now()
        day_raw = (self.day_var.get() or "").strip().lower()
        if start_at > now:
            return start_at
        if day_raw in ("", "today"):
            bumped = start_at + dt.timedelta(days=1)
            self.day_var.set(bumped.strftime("%Y-%m-%d"))
            self.time_var.set(bumped.strftime("%H:%M"))
            messagebox.showinfo(APP_TITLE, f"The selected time was in the past. Moved to {bumped.strftime('%Y-%m-%d %H:%M')}.")
            return bumped
        messagebox.showerror(APP_TITLE, "The selected date/time is in the past. Please choose a future time.")
        return None

    def _write_task_wrapper(self, cmd_list, task_name):
        base = os.path.join(os.environ.get("LOCALAPPDATA", os.getcwd()), "VLCIPTVRecorder", "tasks")
        ensure_dir(base)
        script = os.path.join(base, f"{task_name}.cmd")
        cmd_str = " ".join(f'"{c}"' if (" " in c and not c.startswith("-")) else c for c in cmd_list)
        with open(script, "w", encoding="utf-8", newline="\r\n") as f:
            f.write("@echo off\r\n")
            f.write(cmd_str + "\r\n")
        return script

    def arm_record(self):
        self.schedule_task_async(recurring=False)

    def schedule_task_async(self, recurring=True):
        Worker(self._schedule_task, recurring, done=lambda w: self.after(0, self._schedule_done, w)).start()
        
    def _schedule_done(self, w):
        if isinstance(w.result, tuple):
            ok, msg = w.result
            if ok:
                messagebox.showinfo(APP_TITLE, msg)
                self.refresh_tasks_async()
            else:
                messagebox.showerror(APP_TITLE, msg)
        else:
            messagebox.showerror(APP_TITLE, "Task scheduling failed (unknown error).")

    def _schedule_task(self, recurring=True):
        if not self.ffmpeg_path:
            return (False, "FFmpeg not ready yet.")
        ch = self.get_selected_channel()
        if not ch:
            return (False, "Pick a channel first.")
        try:
            start_at = self._parse_when()
        except Exception as e:
            return (False, str(e))
        if self.dur_var.get().strip():
            try:
                dur_s = parse_duration(self.dur_var.get())
            except Exception as e:
                return (False, f"Duration: {e}")
        else:
            dur_s = 2*3600 + 5*60
        start_at = self._ensure_future_start(start_at)
        if not start_at:
            return (False, "Start time is not in the future.")
        if self.buf_start_var.get():
            mins = max(0, int(self.buf_start_min.get()))
            start_at = start_at - dt.timedelta(minutes=mins)
            dur_s += mins * 60
        if self.buf_end_var.get():
            mins = max(0, int(self.buf_end_min.get()))
            dur_s += mins * 60
        out_dir = (self.outdir_var.get().strip() or self.cfg["out_dir"]); ensure_dir(out_dir)
        base_name = (self.filename_var.get().strip() or self._auto_filename(ch["name"], start_at))
        if not base_name.lower().endswith(".mp4"): base_name += ".mp4"
        out_path = os.path.join(out_dir, base_name)
        cmd = build_ffmpeg_cmd(self.ffmpeg_path, ch["url"], out_path, dur_s, QUALITY_OPTS[self.quality_var.get()], crash_safe=bool(self.crash_safe_var.get()))
        task_name = f"IPTV_DVR_{re.sub(r'[^A-Za-z0-9_-]+','_', base_name)}"
        wrapper = self._write_task_wrapper(cmd, task_name)
        run_date = start_at.strftime("%m/%d/%Y")
        run_time = start_at.strftime("%H:%M")
        if recurring:
            weekday_map = ["MON","TUE","WED","THU","FRI","SAT","SUN"]
            daycode = weekday_map[start_at.weekday()]
            sch = ["schtasks","/Create","/SC","WEEKLY","/D",daycode,"/TN",task_name,"/TR",wrapper,"/ST",run_time,"/SD",run_date,"/F"]
        else:
            sch = ["schtasks","/Create","/SC","ONCE","/TN",task_name,"/TR",wrapper,"/ST",run_time,"/SD",run_date,"/F"]
        rc, out, err = run_schtasks(sch, timeout=20)
        if rc == 0:
            return (True, f"{'Scheduled weekly' if recurring else 'Scheduled one-time'}.\nTask: {task_name}\nTime: {run_time}  Date: {run_date}")
        return (False, f"Task creation failed (rc={rc}):\n{out}\n{err}")

    def series_record_async(self):
        Worker(self._series_record, done=lambda w: self.after(0, self._series_done, w)).start()
        self.status["text"] = "Scheduling series… (running in background)"

    def _series_done(self, w):
        if isinstance(w.result, tuple):
            ok, msg = w.result
            if ok:
                messagebox.showinfo(APP_TITLE, msg)
                self.refresh_tasks_async()
            else:
                messagebox.showerror(APP_TITLE, msg)
        else:
            messagebox.showerror(APP_TITLE, "Series scheduling failed (unknown error).")
        self.status["text"] = "Ready."

    def refresh_tasks_async(self):
        Worker(self._query_tasks, done=lambda w: self.after(0, self._show_tasks, w)).start()

    def _query_tasks(self):
        rc, out, err = run_schtasks(["schtasks","/Query","/FO","CSV","/V"], timeout=25)
        if rc != 0: return (False, f"Query failed (rc={rc}): {err or out}")
        rows = parse_schtasks_csv(out)
        ours = []
        for r in rows:
            name = (r.get("TaskName") or r.get("TaskName ") or "").strip()
            if not name: continue
            if "IPTV_DVR" in name:
                next_run = (r.get("Next Run Time") or r.get("Next Run Time " ) or "").strip()
                schedule = (r.get("Schedule") or r.get("Schedule ") or "").strip()
                status = (r.get("Status") or r.get("Status ") or "").strip()
                ours.append((name, next_run, schedule, status))
        ours.sort()
        return (True, ours)

    def _show_tasks(self, w):
        self.tasks_list.delete(0, tk.END)
        self.series_info.delete(0, tk.END)
        if isinstance(w.result, tuple) and w.result and w.result[0]:
            self.tasks_index = list(w.result[1])
            for name, nxt, sched, status in self.tasks_index:
                self.tasks_list.insert(tk.END, f"{name}    |    Next: {nxt}    |    {sched}    |    {status}")
        else:
            self.tasks_index = []
            error_message = w.result[1] if isinstance(w.result, tuple) and len(w.result) > 1 else "Unable to read scheduled tasks. Try Refresh."
            self.tasks_list.insert(tk.END, error_message)

    def _get_selected_task_names(self):
        names = []
        for idx in self.tasks_list.curselection():
            line = self.tasks_list.get(idx)
            names.append(line.split("    |", 1)[0].strip())
        return names

    def on_task_double_click(self, event):
        idx = self.tasks_list.curselection()
        if not idx: return
        task_name = self.tasks_list.get(idx[0]).split("    |")[0].strip()
        
        def _get_task_details_done(w):
            if w.result and w.result[0]:
                WaitRecord(self, task_name, w.result[1])
            else:
                messagebox.showerror(APP_TITLE, w.result[1] if w.result else "Failed to get task details.")
        Worker(self._get_task_details, task_name, done=lambda w: self.after(0, _get_task_details_done, w)).start()
    
    def _get_task_details(self, task_name):
        rc, out, err = run_schtasks(["schtasks", "/Query", "/TN", task_name, "/XML"], timeout=20)
        if rc != 0:
            return (False, f"Error fetching task details (rc={rc}):\n{err or out}")
        try:
            root = ET.fromstring(out)
            task_details = {}
            command = root.find(".//Command").text
            arguments = root.find(".//Arguments").text if root.find(".//Arguments") is not None else ""
            full_command = f'"{command}" {arguments}'
            
            m = re.search(r'-i\s+"([^"]+)"\s+-t\s+(\d+)\s+.*"([^"]+)"', full_command)
            if not m:
                return (False, "Could not parse FFmpeg command from task wrapper.")

            task_details["stream_url"] = m.group(1)
            task_details["duration_s"] = int(m.group(2))
            task_details["output_path"] = m.group(3)
            return (True, task_details)
        except Exception as e:
            return (False, f"Error parsing XML: {e}")

    def on_task_select(self, event=None):
        self.series_info.delete(0, tk.END)
        names = self._get_selected_task_names()
        if len(names) != 1: return
        base = self._series_group_key(names[0])
        if not base: return
        matches = [t for t in self.tasks_index if t[0].startswith(base+"_")]
        if not matches: return
        self.series_info.insert(tk.END, f"Series group: {base[len(self.SERIES_PREFIX):]}")
        self.series_info.insert(tk.END, "-"*40)
        for name, nxt, sched, status in sorted(matches):
            pretty = f"{name.rsplit('_',1)[-1]}    | Next: {nxt} | {sched} | {status}"
            self.series_info.insert(tk.END, pretty)

    def cancel_task_async(self):
        names = self._get_selected_task_names()
        if not names:
            messagebox.showinfo(APP_TITLE, "Select one or more tasks to cancel (Shift/Ctrl + click)."); return
        if not messagebox.askyesno(APP_TITLE, f"Delete {len(names)} scheduled task(s)?"):
            return
        Worker(self._delete_tasks_batch, names, done=lambda w: self.after(0, self._after_delete_tasks, w)).start()

    def _delete_tasks_batch(self, names):
        successes, failures = 0, []
        for nm in names:
            rc, out, err = run_schtasks(["schtasks","/Delete","/TN",nm,"/F"], timeout=20)
            if rc == 0:
                successes += 1
            else:
                failures.append((nm, rc, err or out))
        msg = f"Deleted {successes} task(s)."
        if failures:
            msg += f"  {len(failures)} failed."
        return (len(failures)==0, msg, failures)

    def _after_delete_tasks(self, w):
        ok, msg, failures = (w.result if isinstance(w.result, tuple) else (False, "Unknown error", []))
        self.refresh_tasks_async()
        if ok:
            messagebox.showinfo(APP_TITLE, msg)
        else:
            detail = "\n".join(f"- {nm} (rc={rc}) {err}" for nm,rc,err in failures[:8])
            messagebox.showerror(APP_TITLE, f"{msg}\n\n{detail}")

    SERIES_RE = re.compile(r"^(IPTV_DVR_SERIES_.+?)_\d{8}_\d{4,6}$")
    def _series_group_key(self, task_name: str):
        m = self.SERIES_RE.match(task_name)
        if m: return m.group(1)
        return None

# --- FIX: ADDED MISSING EPG HELPER FUNCTIONS ---
def epg_search_rows(progs, chmap, query, cutoff_dt=None):
    now = dt.datetime.now()
    ql = query.lower().split()
    rows = []
    for p in progs:
        hay = f"{p['title']} {p['desc']}".lower()
        if all(t in hay for t in ql):
            st = xmltv_to_local(p["start"]); en = xmltv_to_local(p["stop"])
            if not st or not en: continue
            if en <= now: continue
            if cutoff_dt and st > cutoff_dt: continue
            chname = chmap.get(p["channel"],{}).get("names",[p["channel"]])[0]
            rows.append(f"{st.strftime('%Y-%m-%d %H:%M')} - {en.strftime('%H:%M')} | {chname} | {p['title']}")
            if len(rows) >= 400: break
    rows.sort()
    return rows

def epg_title_suggestions(progs, query, k=8):
    now = dt.datetime.now()
    future_titles = {
        (p["title"] or "").strip()
        for p in progs
        if p.get("title") and xmltv_to_local(p["stop"]) and xmltv_to_local(p["stop"]) > now
    }
    future_titles = [t for t in future_titles if t]
    return get_close_matches(query, future_titles, n=k, cutoff=0.6)

# ----- Task Details / Recording window -----
class WaitRecord(tk.Toplevel):
    def __init__(self, master, task_name, task_details):
        super().__init__(master)
        self.master = master
        self.task_name = task_name
        self.task_details = task_details
        self.title("Task Details: " + task_name)
        self.geometry("800x600")
        self.configure(bg=CARD_BG)
        self.protocol("WM_DELETE_WINDOW", self.on_close_window)
        
        ttk.Label(self, text="Task Details", style="Header.TLabel").pack(pady=8)
        
        details_frame = ttk.Frame(self, style="Card.TFrame")
        details_frame.pack(fill="x", padx=16, pady=8)
        details_frame.grid_columnconfigure(1, weight=1)

        ttk.Label(details_frame, text="Task Name:").grid(row=0, column=0, sticky="w", padx=4, pady=2)
        ttk.Label(details_frame, text=self.task_name, wraplength=500).grid(row=0, column=1, sticky="w", padx=4, pady=2)
        
        ttk.Label(details_frame, text="Output File:").grid(row=1, column=0, sticky="w", padx=4, pady=2)
        ttk.Label(details_frame, text=self.task_details.get("output_path", "N/A"), wraplength=500).grid(row=1, column=1, sticky="w", padx=4, pady=2)

        ttk.Label(details_frame, text="Stream URL:").grid(row=2, column=0, sticky="w", padx=4, pady=2)
        ttk.Label(details_frame, text=self.task_details.get("stream_url", "N/A"), wraplength=500).grid(row=2, column=1, sticky="w", padx=4, pady=2)
        
        ttk.Label(details_frame, text="Duration:").grid(row=3, column=0, sticky="w", padx=4, pady=2)
        ttk.Label(details_frame, text=fmt_hms(self.task_details.get("duration_s", 0)), wraplength=500).grid(row=3, column=1, sticky="w", padx=4, pady=2)

        self.log_frame = ttk.Frame(self)
        self.log_frame.pack(fill="both", expand=True, padx=16, pady=8)
        self.log_text = tk.Text(self.log_frame, bg=LOG_BG, fg=LOG_TXT, height=10)
        self.log_text.pack(fill="both", expand=True)

        btns = ttk.Frame(self); btns.pack(pady=6)
        ttk.Button(btns, text="Start Now", command=self.start_now).pack(side="left", padx=6)
        ttk.Button(btns, text="Abort (Delete Task)", command=self.abort_task).pack(side="left", padx=6)
        ttk.Button(btns, text="Close", command=self.on_close_window).pack(side="right", padx=6)

    def start_now(self):
        if not messagebox.askyesno(APP_TITLE, "Start this recording immediately?"):
            return
        
        self.master.update_output_preview()
        
        WaitRecordLive(self.master, self.master.ffmpeg_path, self.task_details["stream_url"], self.task_details["output_path"], dt.datetime.now(), self.task_details["duration_s"], QUALITY_OPTS["High"], crash_safe=self.master.crash_safe_var.get())
        self.destroy()

    def abort_task(self):
        if not messagebox.askyesno(APP_TITLE, "Are you sure you want to delete this scheduled task?"):
            return
        Worker(self.master._delete_tasks_batch, [self.task_name], done=lambda w: self.after(0, self._after_abort, w)).start()

    def _after_abort(self, w):
        ok, msg, failures = w.result
        if ok:
            messagebox.showinfo(APP_TITLE, f"Task '{self.task_name}' deleted successfully.")
            self.master.refresh_tasks_async()
            self.destroy()
        else:
            messagebox.showerror(APP_TITLE, f"Failed to delete task: {msg}")

    def on_close_window(self):
        self.destroy()

# ----- Live Recording window (similar to original WaitRecord) -----
class WaitRecordLive(tk.Toplevel):
    def __init__(self, master, ffmpeg, stream, out_file, start_at, dur_s, qopt, crash_safe=False):
        super().__init__(master)
        self.title("Recording Session")
        self.geometry("1000x640")
        self.configure(bg=CARD_BG)
        self.ffmpeg=ffmpeg; self.stream=stream; self.out=out_file
        self.start_at=start_at; self.dur_s=dur_s; self.qopt=qopt
        self.crash_safe = crash_safe
        self.proc=None; self.stop=False
        self.elapsed = 0
        self.protocol("WM_DELETE_WINDOW", self.on_close_window)

        ttk.Label(self, text="Armed & Recording", style="Header.TLabel").pack(pady=8)
        ttk.Label(self, text=f"File: {self.out}\nStarts: {self.start_at.strftime('%Y-%m-%d %H:%M')}    Duration: {self.dur_s//60} min    Quality: {('High/copy' if qopt['mode']=='copy' else 'Transcode')}"
                          ).pack(pady=4)
        self.status = ttk.Label(self, text="Waiting…", style="Small.TLabel"); self.status.pack()
        self.pb = ttk.Progressbar(self, maximum=100, mode="determinate"); self.pb.pack(fill="x", padx=16, pady=6)

        self.stats_line = ttk.Label(self, text="kbps: -    fps: -", style="Small.TLabel")
        self.stats_line.pack(anchor="w", padx=16)

        self.log = tk.Text(self, height=20, bg=LOG_BG, fg=LOG_TXT)
        self.log.pack(fill="both", expand=True, padx=16, pady=8)

        btns = ttk.Frame(self); btns.pack(pady=6)
        ttk.Button(btns, text="Stop & Finalize (Keep)", command=self.stop_keep).pack(side="left", padx=6)
        ttk.Button(btns, text="Abort (Delete Partial)", command=self.abort_delete).pack(side="left", padx=6)
        self.open_folder_btn = ttk.Button(btns, text="Open Folder", command=self.open_folder, state="disabled")
        self.open_folder_btn.pack(side="left", padx=6)

        Worker(self._run).start()

    def _log(self, s): self.log.insert(tk.END, s+"\n"); self.log.see(tk.END)

    def _update_stats_from_line(self, line: str):
        m = re.search(r"time=(\d+):(\d+):(\d+)", line)
        if m:
            h,mn,sc = map(int, m.groups())
            self.elapsed = h*3600 + mn*60 + sc
        fps = None; kbps = None
        m = re.search(r"fps=\s*([0-9.]+)", line);        fps = m.group(1) if m else None
        m = re.search(r"bitrate=\s*([0-9.]+)\s*kbits/s", line)
        if m: kbps = m.group(1)
        if kbps is None:
            m = re.search(r"size=\s*([0-9.]+)\s*([kM]?B|KiB|MiB)", line)
            if m and self.elapsed>0:
                amt = float(m.group(1)); unit = m.group(2).lower()
                if unit in ("kb","kib"): bytes_now = amt*1024
                elif unit in ("mb","mib"): bytes_now = amt*1024*1024
                else: bytes_now = amt
                kbps = f"{(bytes_now*8/1000)/self.elapsed:.1f}"
        cur = self.stats_line.cget("text")
        cur_kbps = re.search(r"kbps:\s*([^\s]+)", cur)
        cur_fps  = re.search(r"fps:\s*([^\s]+)", cur)
        show_kbps = kbps if kbps is not None else (cur_kbps.group(1) if cur_kbps else "-")
        show_fps  = fps  if fps  is not None else (cur_fps.group(1)  if cur_fps  else "-")
        self.stats_line.config(text=f"kbps: {show_kbps}    fps: {show_fps}")

    def _run(self):
        now = dt.datetime.now()
        if self.start_at > now:
            total = (self.start_at - now).total_seconds()
            while not self.stop:
                now = dt.datetime.now()
                remain = (self.start_at - now).total_seconds()
                if remain <= 0: break
                pct = 0 if total<=0 else max(0,min(100, (1 - remain/total)*100))
                self.pb["value"]=pct
                self.status["text"]=f"Armed. Starts in {fmt_hms(remain)}"
                time.sleep(0.5)
        if self.stop: return

        cmd = build_ffmpeg_cmd(self.ffmpeg, self.stream, self.out, self.dur_s, self.qopt, crash_safe=self.crash_safe)
        self._log("> " + " ".join(cmd))
        ensure_dir(os.path.dirname(self.out) or ".")
        try:
            self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                          text=True, bufsize=1, universal_newlines=True)
        except Exception as e:
            self._log(f"ERROR starting ffmpeg: {e}")
            return

        while True:
            if self.stop:
                try: self.proc.terminate()
                except Exception: pass
                break
            line = self.proc.stdout.readline()
            if not line:
                if self.proc.poll() is not None: break
                time.sleep(0.1); continue
            line = line.rstrip()
            if "time=" in line:
                m = re.search(r"time=(\d+):(\d+):(\d+)", line)
                if m:
                    h,mn,sc = map(int, m.groups())
                    elapsed = h*3600 + mn*60 + sc
                    self.elapsed = elapsed
                    pct = min(100, (elapsed/self.dur_s)*100)
                    rem = max(0, self.dur_s - elapsed)
                    self.pb["value"]=pct
                    self.status["text"]=f"Recording… elapsed {fmt_hms(elapsed)}  |  remaining {fmt_hms(rem)}"
            self._update_stats_from_line(line)
            self._log(line)

        try:
            rest = self.proc.stdout.read()
            if rest:
                for ln in rest.splitlines():
                    self._update_stats_from_line(ln); self._log(ln)
        except Exception:
            pass

        rc = self.proc.returncode if self.proc else -1
        if os.path.exists(self.out):
            self._log(f"Saved: {self.out}  ({fmt_bytes(os.path.getsize(self.out))})")
        self.status["text"] = f"FFmpeg exited with code {rc}."
        self.pb["value"]=100
        try: self.title("Recording Session — ✅ Finished")
        except Exception: pass
        self.open_folder_btn.configure(state="normal")

    def stop_keep(self):
        if not messagebox.askyesno(APP_TITLE, "Stop now and finalize the file so it stays playable?"):
            return
        self.stop=True
        self._log("Stopping… finalizing file.")
        def finisher():
            try:
                if self.proc and self.proc.poll() is None:
                    self.proc.terminate()
                    self.proc.wait(timeout=10)
                finalize_recording(self.ffmpeg, self.out)
            except Exception:
                pass
        Worker(finisher).start()

    def abort_delete(self):
        if not messagebox.askyesno(APP_TITLE, "Abort recording and delete the partial file?"):
            return
        self.stop=True
        def killer():
            try:
                if self.proc and self.proc.poll() is None:
                    self.proc.terminate()
                    self.proc.wait(timeout=10)
            except Exception:
                pass
            try:
                if os.path.exists(self.out):
                    os.remove(self.out)
            except Exception:
                pass
        Worker(killer).start()

    def on_close_window(self):
        self.stop_keep()

    def open_folder(self):
        try:
            folder = os.path.dirname(os.path.abspath(self.out)) or "."
            os.startfile(folder)
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Could not open folder:\n{e}")

# ------------------- main -------------------
def main():
    app = App()
    app.mainloop()

if __name__ == "__main__":
    main()