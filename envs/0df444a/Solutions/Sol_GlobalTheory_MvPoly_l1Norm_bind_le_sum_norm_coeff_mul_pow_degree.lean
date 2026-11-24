-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_bind_le_sum_norm_coeff_mul_pow_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:35.673058+00:00
-- url     : https://prove2.me/submissions/f4a94da0-6a5f-4293-b6de-7f0a742825e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_prod_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K]
namespace GlobalTheory.MvPoly
theorem _root_.solution [NormOneClass K] (f : σ → MvPolynomial τ K) (P : MvPolynomial σ K)
    {R : ℝ} (h : ∀ i, l1Norm (f i) ≤ R) :
    l1Norm (bind₁ f P) ≤ ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun α _ ↦ ?_)
  rw [bind₁_monomial]
  refine (l1Norm_mul_le _ _).trans ?_
  rw [l1Norm_C, Finsupp.degree_apply, ← prod_pow_eq_pow_sum]
  exact mul_le_mul_of_nonneg_left (l1Norm_prod_pow_le _ _ _ _ fun i _ ↦ h i) (norm_nonneg _)
end GlobalTheory.MvPoly
