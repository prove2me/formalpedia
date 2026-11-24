-- Prove2me | solution 1 for GlobalTheory.MvPoly.norm_eval_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:56.185013+00:00
-- url     : https://prove2.me/submissions/eb374af4-f92c-4190-92fb-468101296082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_sum_norm_coeff_mul_pow_le
import Theorems.Thm_GlobalTheory_MvPoly_norm_eval_le_sum

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
    (h : ∀ i, ‖x i‖ ≤ R) {d : ℕ} (hd : P.totalDegree ≤ d) :
    ‖eval x P‖ ≤ l1Norm P * max 1 R ^ d := by
  have := (norm_eval_le_sum x P fun i ↦ (h i).trans (le_max_right 1 R)).trans
    (sum_norm_coeff_mul_pow_le P (zero_le_one.trans (le_max_left 1 R)) hd)
  rwa [← max_assoc, max_self] at this
end GlobalTheory.MvPoly
