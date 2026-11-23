-- Prove2me | solution 1 for GlobalTheory.SelfDualClasses.norm_herm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:25.072469+00:00
-- url     : https://prove2.me/submissions/063d35f4-5844-47e2-b9e8-50a978971b50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_eq
import Theorems.Thm_GlobalTheory_TraceDualMin_herm_one_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.SelfDualClasses
open ShortVectors
namespace GlobalTheory.SelfDualClasses
theorem _root_.solution {n : ℕ} (τ : E →+* ℂ) (x y : Fin n → E) (C : ℝ)
    (hx : ∑ k, ‖τ (x k)‖ ^ 2 ≤ C) (hy : ∑ k, ‖τ (y k)‖ ^ 2 ≤ C) : ‖τ (herm 1 x y)‖ ≤ C := by
  have h : ‖τ (herm 1 x y)‖ ≤ ∑ k, (‖τ (x k)‖ ^ 2 + ‖τ (y k)‖ ^ 2) / 2 := by
    rw [DualFamily.herm_one_eq, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have : ‖τ (cc (y k))‖ = ‖τ (y k)‖ := by
      simp [cc, IsCMField.complexEmbedding_complexConj]
    rw [map_mul, norm_mul, this]
    nlinarith [sq_nonneg (‖τ (x k)‖ - ‖τ (y k)‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at h
  linarith
end GlobalTheory.SelfDualClasses
