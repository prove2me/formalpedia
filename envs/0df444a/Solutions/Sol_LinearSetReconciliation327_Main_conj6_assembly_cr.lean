-- Prove2me | solution 1 for LinearSetReconciliation327.Main.conj6_assembly_cr
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-21T15:34:42.266915+00:00
-- url     : https://prove2.me/submissions/3f1faef2-d6e5-41f2-b218-77f32fe69223

import Definitions.Def_LinearSetReconciliation327_Main_Conj6CR

set_option autoImplicit false

open LinearSetReconciliation327.Main

theorem solution
    (Sup : Stmt) (E : RAMEnv) {l N t Wd Rpad : ℕ} {f : Fin l → ℕ}
    {dt : Fin l → ℕ → ℕ}
    {Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2)}
    {C : Fin N → Fin (cr23D N) → Fin (cr23M t)}
    {Tu : ℝ} (hTu : 0 ≤ Tu)
    (hW : 0 < E.W) (hW1 : 1 < 2 ^ E.W) (hWd1 : 1 ≤ Wd) (hWd2 : 2 ≤ Wd)
    (hpad : ∀ s : Fin l, E.W * wordsOf E.W (f s) = f s)
    (hUp : UpChildSemC Sup E Tu (2 ^ Wd) f Hs)
    (hE : E.det = compUpDetB Wd Rpad dt (cr23DecDetAt N t C (blkTotal E.W f))
      (fun s => blkOff E.W f s.val) (blkTotal E.W f))
    (hN : 1 ≤ N) (htN : t ≤ N) (hEW : E.W = cr23Word N) (hBw : cr23Graph0 N ≤ Rpad)
    (hWdW : 2 ^ Wd < 2 ^ E.W) (hlW : l + 1 < 2 ^ E.W)
    (hRpad : 0 < Rpad) (hRfit : Rpad ≤ 2 ^ Wd) (hpayfit : Rpad + l ≤ 2 ^ Wd)
    (hlWd : (l + 1) * 2 ^ Wd < 2 ^ E.W)
    (hcrfit : (l + 1) * 2 ^ Wd + Rpad ≤ 2 ^ E.W)
    (hpaylt : compPayBase l Wd Rpad + l ≤ 2 ^ E.W)
    (hbtlt : blkTotal E.W f < 2 ^ E.W)
    (hbtfit : blkTotal E.W f + wordsOf E.W (cr23R N t) ≤ 2 ^ E.W)
    (y : Fin (E.W * blkTotal E.W f + (cr23R N t)) → ZMod 2) (i : Fin N) :
    ∃ s' : RAMState,
      HaltsWithin (progUpOfProB Sup cr23UpStmtAt) E
        (7 + (8 * (l : ℝ) + (l : ℝ) * Tu) + 2 + 3 + (65536 * lg ((N : ℝ) + 2) ^ 2))
        (initState (packMem E.W y) i.val 0 0) s' ∧
      (∀ addr < wordsOf E.W (E.W * blkTotal E.W f + (cr23R N t)),
        s'.mem addr
          = packMem E.W (y + compH E.W hW f (cr23R N t) Hs (cr23Sketch N t C) (Pi.single i 1)) addr) := by
  exact conj6_assembly_CR (Sup := Sup) (E := E) hTu hW hW1 hWd1 hWd2 hpad hUp hE hN htN hEW hBw
    hWdW hlW hRpad hRfit hpayfit hlWd hcrfit hpaylt hbtlt hbtfit y i
