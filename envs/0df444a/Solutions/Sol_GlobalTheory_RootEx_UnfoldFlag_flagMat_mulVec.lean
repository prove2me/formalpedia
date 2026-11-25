-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldFlag.flagMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:40.755275+00:00
-- url     : https://prove2.me/submissions/3a42bcfd-9e12-432c-9ca2-dd34d6871aa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsUnipotent
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_inX_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldFlag
variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.UnfoldFlag
theorem _root_.solution (y : Fin c → (n ⊕ Fin c → k)) (v : n ⊕ Fin c → k) :
    flagMat y *ᵥ v = inX k n c (fun r => v (Sum.inl r)) + ∑ i, v (Sum.inr i) • y i := by
  funext r
  rw [inX_apply]
  simp only [mulVec, dotProduct, flagMat, of_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · rcases r with r | l
    · simp [one_apply]
    · simp [one_apply]
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end GlobalTheory.RootEx.UnfoldFlag
