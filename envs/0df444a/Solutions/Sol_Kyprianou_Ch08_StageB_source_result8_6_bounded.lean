-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_bounded
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:52:51.625586+00:00
-- url     : https://prove2.me/submissions/ccf173bb-3458-4df9-b185-b628c462ed7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_discount_invariant
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q →
        (HasBoundedVariationTriplet
          D.gaussianCoefficient D.triplet.levyMeasure →
          0 < bvDrift D.triplet.drift D.triplet.levyMeasure ∧
          W q 0 =
            (bvDrift D.triplet.drift D.triplet.levyMeasure)⁻¹) := by
  intro Ω mΩ P mP D ψ W hψ hW q hq hBV
  have h0 := source_result8_6_zero_discount Ω P D ψ W hψ hW
  have hbounded := h0.2 hBV
  constructor
  · exact hbounded.1
  · calc
      W q 0 = W 0 0 := source_scale_origin_discount_invariant ψ W hW q hq
      _ = (bvDrift D.triplet.drift D.triplet.levyMeasure)⁻¹ := hbounded.2
