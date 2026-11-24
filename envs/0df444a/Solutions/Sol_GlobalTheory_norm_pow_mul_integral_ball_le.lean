-- Prove2me | solution 1 for GlobalTheory.norm_pow_mul_integral_ball_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:16.331073+00:00
-- url     : https://prove2.me/submissions/20c87cf6-e2a6-484a-822b-b40b5136f79b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_ball_le_of_centre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) {w : ℝ → ℝ}
    (hw : Measurable w) (hw0 : ∀ t, 0 ≤ t → 0 ≤ w t) (n : ℕ)
    (hi : IntegrableOn (fun z => w ‖z - a‖) (ball a r) μ)
    (hi' : IntegrableOn (fun z => ‖φ z‖ ^ n * w ‖z - a‖) (ball a r) μ) :
    ‖φ a‖ ^ n * ∫ z in ball a r, w ‖z - a‖ ∂μ ≤ ∫ z in ball a r, ‖φ z‖ ^ n * w ‖z - a‖ ∂μ := by
  have h := enorm_pow_mul_lintegral_ball_le_of_centre μ hφ (w := fun t => ENNReal.ofReal (w t))
    hw.ennreal_ofReal n
  have h0 : ∀ z : E, 0 ≤ ‖φ z‖ ^ n * w ‖z - a‖ := fun z =>
    mul_nonneg (by positivity) (hw0 _ (norm_nonneg _))
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg h0), ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun z => hw0 _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall h0)]
  simpa [ENNReal.ofReal_mul, ENNReal.ofReal_pow] using h
end GlobalTheory
