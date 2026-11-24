-- Prove2me | solution 1 for GlobalTheory.volume_ball_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:15.081992+00:00
-- url     : https://prove2.me/submissions/503bac18-ae34-4855-895b-d810f7846931

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_volume_ball_of_finrank_eq_two_mul

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
namespace GlobalTheory
theorem _root_.solution (a : E) {r : ℝ} (hr : 0 < r) :
    volume (ball a r) = ENNReal.ofReal (π ^ Module.finrank ℂ E * r ^ (2 * Module.finrank ℂ E) /
      (Module.finrank ℂ E).factorial) :=
  volume_ball_of_finrank_eq_two_mul
    (by rw [← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]) a hr
end GlobalTheory
