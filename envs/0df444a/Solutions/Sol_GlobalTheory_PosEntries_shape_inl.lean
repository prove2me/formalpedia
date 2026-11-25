-- Prove2me | solution 1 for GlobalTheory.PosEntries.shape_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:35.07382+00:00
-- url     : https://prove2.me/submissions/f515753e-9727-4150-8ec0-dd80349abfdb

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
theorem _root_.solution {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hp : 1 ≤ p)
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (j : Fin c)
    (hs : M (Sum.inl x) (Sum.inr j) ≠ 0) : j.val + 1 = p := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
  · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))
end GlobalTheory.PosEntries
