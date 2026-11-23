-- Prove2me | solution 1 for GlobalTheory.IntegralAgainstMeasure.integralAgainst_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:54.344582+00:00
-- url     : https://prove2.me/submissions/b0e68df2-eaab-4292-bcd4-a50d2cbc1597

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
    (f : C(K, ℂ)) : integralAgainst μ p f = ∫ k, f k • p k ∂μ := rfl
end GlobalTheory.IntegralAgainstMeasure
