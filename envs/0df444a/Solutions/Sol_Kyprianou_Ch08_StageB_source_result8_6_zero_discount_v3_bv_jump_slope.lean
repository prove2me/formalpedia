-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_jump_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:54:45.244147+00:00
-- url     : https://prove2.me/submissions/5c6e6ac0-0311-4a49-be3f-f6213e433bf1

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv_small_jump_slope
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv_large_jump_vanish
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_compensated_integral_exact_partition
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Join the established BV small/large jump limits via the exact integral split. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ =>
        (∫ x, (Real.exp (β * x) - 1 - (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β)
        atTop (𝓝 (-∫ x in Set.Ioo (-1 : ℝ) 0, x ∂D.triplet.levyMeasure)) := by
  intro Ω mΩ P hP D hbv
  have hsmall := source_result8_6_zero_discount_v3_bv_small_jump_slope Ω P D hbv
  have hlarge := source_result8_6_zero_discount_v3_bv_large_jump_vanish Ω P D
  have hsum : Tendsto (fun β : ℝ =>
      (∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) +
      (∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure)) atTop
      (𝓝 (-∫ x in Set.Ioo (-1 : ℝ) 0, x ∂D.triplet.levyMeasure)) := by
    simpa only [add_zero] using hsmall.add hlarge
  have hEq : (fun β : ℝ =>
      (∫ x, (Real.exp (β * x) - 1 -
        (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β) =ᶠ[atTop]
      (fun β : ℝ =>
      (∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) +
      (∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact p2m86_bv_compensated_integral_exact_partition Ω P D hbv β hβ
  exact hsum.congr' hEq.symm
