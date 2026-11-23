-- Prove2me | solution 1 for GlobalTheory.IntegralAgainstMeasure.integralAgainstLinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:35.210083+00:00
-- url     : https://prove2.me/submissions/0e24675e-4f1d-45f8-bc9e-1e597ad34458

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IntegralAgainstLinearApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IntegralAgainstMeasure
variable {K B : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [NormedAddCommGroup B] [NormedSpace ℂ B]
namespace GlobalTheory.IntegralAgainstMeasure
theorem _root_.solution (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B))
    (f : C(K, ℂ)) : integralAgainstLinear μ p f = ∫ k, f k • p k ∂μ := rfl
end GlobalTheory.IntegralAgainstMeasure
