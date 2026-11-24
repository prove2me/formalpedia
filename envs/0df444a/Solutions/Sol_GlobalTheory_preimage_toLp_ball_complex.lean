-- Prove2me | solution 1 for GlobalTheory.preimage_toLp_ball_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:49.069812+00:00
-- url     : https://prove2.me/submissions/58b68faf-bbb1-4403-b06e-7870288c4df7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall

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
    (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) ⁻¹' ball 0 r =
      {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < r ^ 2} := by
  ext x
  simp [EuclideanSpace.norm_eq, Real.sqrt_lt' hr]
end GlobalTheory
