-- Prove2me | solution 1 for GlobalTheory.volume_closedBall_euclideanSpace_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:47.911338+00:00
-- url     : https://prove2.me/submissions/00948847-78aa-492a-aa67-34bab15132c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_volume_closedBall_of_finrank_eq_two_mul

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
    volume (closedBall a r) = ENNReal.ofReal (π ^ Fintype.card ι * r ^ (2 * Fintype.card ι) /
      (Fintype.card ι).factorial) :=
  volume_closedBall_of_finrank_eq_two_mul (by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]) a hr
end GlobalTheory
