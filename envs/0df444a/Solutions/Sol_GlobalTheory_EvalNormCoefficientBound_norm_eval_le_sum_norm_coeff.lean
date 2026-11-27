-- Prove2me | solution 1 for GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:36.509322+00:00
-- url     : https://prove2.me/submissions/7d010f0b-aae4-4baf-b031-913ef7ef9cf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEvalLeSumNormCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EvalNormCoefficientBound
namespace GlobalTheory.EvalNormCoefficientBound
theorem _root_.solution {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ)
    (hv : ∀ (s : σ), ‖v s‖ ≤ (1 : ℝ)) :
    ‖(MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P‖ ≤
      ∑ d ∈ MvPolynomial.support P, ‖MvPolynomial.coeff d P‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  rw [norm_mul]
  have h1 : ‖∏ s ∈ d.support, v s ^ d s‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun s _ => norm_nonneg _) (fun s _ => ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hv s)
  exact mul_le_of_le_one_right (norm_nonneg _) h1
end GlobalTheory.EvalNormCoefficientBound
