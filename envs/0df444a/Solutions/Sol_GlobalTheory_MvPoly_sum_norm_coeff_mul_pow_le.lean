-- Prove2me | solution 1 for GlobalTheory.MvPoly.sum_norm_coeff_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:47.773339+00:00
-- url     : https://prove2.me/submissions/9f9b5826-7b75-4fbe-913e-38014a56beec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_degree_le_totalDegree

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
theorem _root_.solution (P : MvPolynomial σ K) {R : ℝ} (hR : 0 ≤ R) {d : ℕ}
    (hd : P.totalDegree ≤ d) :
    ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree ≤ l1Norm P * max 1 R ^ d := by
  rw [l1Norm, sum_mul]
  refine sum_le_sum fun α hα ↦ mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (pow_le_pow_left₀ hR (le_max_right 1 R) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) ((degree_le_totalDegree hα).trans hd))
end GlobalTheory.MvPoly
