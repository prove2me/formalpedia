-- Prove2me | solution 1 for GlobalTheory.coe_sphereRotation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:05.657153+00:00
-- url     : https://prove2.me/submissions/a8672c74-7ad5-4aba-ab91-131e9027d3dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralLogNormLeHalfLogIntegralSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
omit [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (θ : ℝ) (x : sphere (0 : E) 1) :
    (sphereRotation θ x : E) = circleMap 0 1 θ • (x : E) := rfl
end GlobalTheory
