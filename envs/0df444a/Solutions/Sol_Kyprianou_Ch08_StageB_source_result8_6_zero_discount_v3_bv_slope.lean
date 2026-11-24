-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:55:14.321811+00:00
-- url     : https://prove2.me/submissions/0d292fa3-dc3c-43da-809d-b3ec0de3dcfe

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv_jump_slope
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_exponent_slope_from_jump_limit
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Derive the source physical BV exponent slope from its compensated jump limit. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ => ψ β / β) atTop
        (𝓝 (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)) := by
  intro Ω mΩ P hP D ψ hψ hbv
  exact p2m86_bv_exponent_slope_from_jump_limit Ω P D ψ hψ hbv
    (source_result8_6_zero_discount_v3_bv_jump_slope Ω P D hbv)
