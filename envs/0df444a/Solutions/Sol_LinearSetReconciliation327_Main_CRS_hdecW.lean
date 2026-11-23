-- Prove2me | solution 1 for LinearSetReconciliation327.Main.CRS.hdecW
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-23T11:36:18.706191+00:00
-- url     : https://prove2.me/submissions/46742b0f-14b2-49e7-9199-b32aaa616e11

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23DecExitWz20261123
import Definitions.Def_LinearSetReconciliation327_Main_CrStageInWz20261123

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main

namespace CRS

/-- **`hdecW`: Proposition 2.3's decoder from the finite window pin.**

From any state that presents the decoder's payload on `[0, wordsOf (cr23Word N) (cr23R N t))` and is
zero on `[wordsOf …, Z)` — with `Z ≥ decZeroBound N t` and memory at `≥ Z` **arbitrary** — the
published decoder program `progDec` halts within the published budget, outputs the support of `x` and
leaves `r0 = decOutBase N t`.

`Z = decZeroBound N t = decOutBase N t` is the exact bound of the published proof's zero reads
(`decZeroBound_tight`), so this is the sharp form of the fifth hypothesis. -/
theorem hdecW (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t) (Z : ℕ) (hZ : decZeroBound N t ≤ Z)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (st : RAMState) (hpc : st.pc = 0)
    (hIn : CrStageInWz (detEnv (cr23Word N) (cr23DecDet N t C)) (cr23R N t) Z
      (cr23Sketch N t C x) ab al bb bl ob Lx st) :
    ∃ s' : RAMState,
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
        ((decStmtCost N t : ℝ) + 1) st s' ∧
        OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t := by
  obtain ⟨hregs, hpay, hzero, -⟩ := hIn
  have h0 : st.regs r0 = 0 := by
    rw [hregs]
    simp [decoderStart, initState]
  exact decStmt_halts_exit_wz N t hN ht htN C x eps hexp heps hsup st hpc h0 hpay
    (fun a ha haZ => hzero a ha (lt_of_lt_of_le haZ hZ))

/-- **The same statement at the exact bound `Z = decZeroBound N t`**, the sharpest form. -/
theorem hdecW_sharp (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (st : RAMState) (hpc : st.pc = 0)
    (hIn : CrStageInWz (detEnv (cr23Word N) (cr23DecDet N t C)) (cr23R N t)
      (decZeroBound N t) (cr23Sketch N t C x) ab al bb bl ob Lx st) :
    ∃ s' : RAMState,
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
        ((decStmtCost N t : ℝ) + 1) st s' ∧
        OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t :=
  hdecW N t hN ht htN C x eps hexp heps hsup (decZeroBound N t) le_rfl ab al bb bl ob Lx st
    hpc hIn

/-- **The `cr` slot composes at the finite window pin.**  The published `stageRun_crMerge_top` is
generic in its precondition, so `CrStageInWz` plugs in verbatim — this is the Z-pin counterpart of
`stageRun_crMerge_top_window`.  The only hypothesis left in this slot is the `hdec` *post*
(`CrMergeIn` after decoder · setup · unpack), i.e. the arithmetic half, not the decoder. -/
theorem stageRun_crMerge_topZ {Sinit Srow Sdec Sassem Sres Sdec23 : Stmt} {E : RAMEnv}
    {Tdec : ℝ} {M Z : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ}
    {S xhat : Finset ℕ}
    (hno : sNoJumpB Sdec23 = true) (hhf : sHaltFreeB Sdec23 = true)
    (hdec : ∀ s : RAMState, s.pc = 0 →
      CrStageInWz E M Z y ab al bb bl ob Lx (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement Sdec23) E Tdec s s' ∧
        CrMergeIn E ab al bb bl ob Lx S
          (withPc (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len) s'))
    (hLx : Lx.toFinset = xhat) (hW : 1 < 2 ^ E.W) :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres (ScrStage Sdec23)) E
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres (ScrStage Sdec23))
      (Tdec + RMR.mrgCost al bl) (CrStageInWz E M Z y ab al bb bl ob Lx)
      (fun s' => OutListIs s' (symmDiff xhat S)) :=
  stageRun_crMerge_top hno hhf hdec hLx hW

/-- **Non-degeneracy of the finite window in the decoder itself**: for every expanding `C`, every
payload `x` and every `k`, the decoder still halts correctly from a state whose word `Z + k` is `1`
(where the whole-memory pin would force `0`).  So the gain over `decStmt_halts_exit` is real: garbage
above `Z` is allowed. -/
theorem hdecW_nondegen {N t : ℕ} (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t) (ab al bb bl ob : ℕ) (Lx : List ℕ)
    (hdata : CrMergeData (detEnv (cr23Word N) (cr23DecDet N t C)) ab al bb bl ob Lx)
    (hZ : wordsOf (cr23Word N) (cr23R N t) ≤ decZeroBound N t) (k : ℕ) :
    ∃ st : RAMState, st.mem (decZeroBound N t + k) = 1 ∧
      ∃ s', HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
        ((decStmtCost N t : ℝ) + 1) st s' ∧
        OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t := by
  classical
  let st : RAMState :=
    ⟨0, (decoderStart (cr23Word N) (cr23Sketch N t C x) []).regs,
      fun a => if a < wordsOf (cr23Word N) (cr23R N t) then
        packMem (cr23Word N) (cr23Sketch N t C x) a
      else if a < decZeroBound N t then 0 else 1⟩
  have hpc : st.pc = 0 := rfl
  have hmem1 : st.mem (decZeroBound N t + k) = 1 := by
    show (if decZeroBound N t + k < wordsOf (cr23Word N) (cr23R N t) then
        packMem (cr23Word N) (cr23Sketch N t C x) (decZeroBound N t + k)
      else if decZeroBound N t + k < decZeroBound N t then 0 else 1) = 1
    rw [if_neg (by omega), if_neg (by omega)]
  have hpin : CrStageInWz (detEnv (cr23Word N) (cr23DecDet N t C)) (cr23R N t)
      (decZeroBound N t) (cr23Sketch N t C x) ab al bb bl ob Lx st := by
    refine ⟨rfl, ?_, ?_, hdata⟩
    · intro j hj
      rw [show (detEnv (cr23Word N) (cr23DecDet N t C)).W = cr23Word N from rfl] at hj
      show (if j < wordsOf (cr23Word N) (cr23R N t) then
          packMem (cr23Word N) (cr23Sketch N t C x) j
        else if j < decZeroBound N t then 0 else 1)
        = packMem (cr23Word N) (cr23Sketch N t C x) j
      rw [if_pos hj]
    · intro a ha haZ
      rw [show (detEnv (cr23Word N) (cr23DecDet N t C)).W = cr23Word N from rfl] at ha
      show (if a < wordsOf (cr23Word N) (cr23R N t) then
          packMem (cr23Word N) (cr23Sketch N t C x) a
        else if a < decZeroBound N t then 0 else 1) = 0
      rw [if_neg (by omega), if_pos haZ]
  obtain ⟨s', h1, h2, h3⟩ :=
    hdecW N t hN ht htN C x eps hexp heps hsup (decZeroBound N t) le_rfl ab al bb bl ob Lx st
      hpc hpin
  exact ⟨st, hmem1, s', h1, h2, h3⟩

end CRS

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main LinearSetReconciliation327.Main.CRS in
/-- **Submission wrapper**: Proposition 2.3's decoder from the finite window pin. -/
theorem solution {N t : ℕ} (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t) (Z : ℕ) (hZ : decZeroBound N t ≤ Z)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (st : RAMState) (hpc : st.pc = 0)
    (hIn : CrStageInWz (detEnv (cr23Word N) (cr23DecDet N t C)) (cr23R N t) Z
      (cr23Sketch N t C x) ab al bb bl ob Lx st) :
    ∃ s' : RAMState,
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
        ((decStmtCost N t : ℝ) + 1) st s' ∧
        OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t :=
  hdecW N t hN ht htN C x eps hexp heps hsup Z hZ ab al bb bl ob Lx st hpc hIn