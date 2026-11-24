-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:50:58.968841+00:00
-- url     : https://prove2.me/submissions/0fbabb96-188c-4f9d-85ce-667e32e62767

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv_slope
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_drift_positive_from_exponent_slope
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_origin_value_from_exponent_slope
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

/-- Recover the corrected source BV dichotomy from the exponent-slope and scale-origin laws. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure ∧
      W 0 0 = (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)⁻¹ := by
  intro Ω mΩ P hP D ψ W hψ hW hbv
  have hlim := source_result8_6_zero_discount_v3_bv_slope Ω P D ψ hψ hbv
  have hpos := p2m86_bv_drift_positive_from_exponent_slope
    Ω P D ψ W hψ hW hbv hlim
  have hvalue := p2m86_bv_origin_value_from_exponent_slope
    Ω P D ψ W hψ hW hbv hlim hpos
  exact ⟨hpos, hvalue⟩
