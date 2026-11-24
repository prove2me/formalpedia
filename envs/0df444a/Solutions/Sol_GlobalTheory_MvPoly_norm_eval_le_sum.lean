-- Prove2me | solution 1 for GlobalTheory.MvPoly.norm_eval_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:42.778801+00:00
-- url     : https://prove2.me/submissions/5ade330b-b0e5-4b6e-af10-15192d514f4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial

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
theorem _root_.solution [NormOneClass K] (x : σ → K) (P : MvPolynomial σ K) {R : ℝ}
    (h : ∀ i, ‖x i‖ ≤ R) : ‖eval x P‖ ≤ ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree := by
  rw [eval_eq]
  refine norm_sum_le_of_le _ fun α _ ↦ (norm_mul_le _ _).trans ?_
  rw [Finsupp.degree_apply, ← prod_pow_eq_pow_sum]
  refine mul_le_mul_of_nonneg_left ((Finset.norm_prod_le _ _).trans ?_) (norm_nonneg _)
  exact prod_le_prod (fun _ _ ↦ norm_nonneg _) fun i _ ↦
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (h i) _)
end GlobalTheory.MvPoly
