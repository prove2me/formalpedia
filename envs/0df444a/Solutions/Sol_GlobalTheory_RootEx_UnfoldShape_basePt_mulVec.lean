-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.basePt_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:34.400798+00:00
-- url     : https://prove2.me/submissions/63c63122-4464-4f91-ba2a-728d77ae1d09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice

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
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (x₀ : Matrix n n' k) (v : n' ⊕ Fin (c + 1) → k) :
    basePt c x₀ *ᵥ v = Sum.elim (x₀ *ᵥ fun s => v (Sum.inl s)) fun l => v (Sum.inr l.castSucc) := by
  ext (r | r)
  · simp [basePt, Matrix.mulVec, dotProduct]
  · simp only [basePt, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.of_apply, Sum.elim_inr]
    rw [Finset.sum_eq_single r.castSucc]
    · simp
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro h
      exact hj (Fin.ext (by simp [h]))
    · simp
end GlobalTheory.RootEx.UnfoldShape
