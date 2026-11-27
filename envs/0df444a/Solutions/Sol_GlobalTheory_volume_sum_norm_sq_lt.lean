-- Prove2me | solution 1 for GlobalTheory.volume_sum_norm_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:02.168409+00:00
-- url     : https://prove2.me/submissions/e04c73af-7ca3-4e1a-afcf-7af63ae85e9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_volume_ball_euclideanSpace_complex
import Theorems.Thm_GlobalTheory_measurePreserving_toLp_complex
import Theorems.Thm_GlobalTheory_preimage_toLp_ball_complex

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
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution {r : ℝ} (hr : 0 < r) :
    volume {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < r ^ 2} =
      ENNReal.ofReal (π ^ Fintype.card ι * r ^ (2 * Fintype.card ι) /
        (Fintype.card ι).factorial) := by
  rw [← preimage_toLp_ball_complex hr,
    measurePreserving_toLp_complex.measure_preimage measurableSet_ball.nullMeasurableSet,
    volume_ball_euclideanSpace_complex 0 hr]
end GlobalTheory
