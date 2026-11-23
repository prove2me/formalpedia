-- Prove2me | solution 1 for GlobalTheory.volume_ball_euclideanSpace_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:41.14599+00:00
-- url     : https://prove2.me/submissions/6632a7e0-fd2a-4977-a341-6c5cd48f34b9

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
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (a : EuclideanSpace ℂ ι) {r : ℝ} (hr : 0 < r) :
    volume (ball a r) = ENNReal.ofReal (π ^ Fintype.card ι * r ^ (2 * Fintype.card ι) /
      (Fintype.card ι).factorial) :=
  volume_ball_of_finrank_eq_two_mul (by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]) a hr
end GlobalTheory
