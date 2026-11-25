-- Prove2me | solution 1 for GlobalTheory.PosEntries.shape_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:41.069096+00:00
-- url     : https://prove2.me/submissions/d7fe099d-20cf-4a3c-be2a-ba305e2af08a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.PosEntries
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.PosEntries
theorem _root_.solution {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i : Fin c) (s : n ⊕ Fin c)
    (hs : M (Sum.inr i) s ≠ 0) : s = Sum.inr i := by
  rcases s with x | j
  · exfalso
    by_cases h : i.val + 1 < p
    · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))
    · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
  · by_cases hij : j = i
    · rw [hij]
    exfalso
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
    · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))
end GlobalTheory.PosEntries
