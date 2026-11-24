-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m86_bv_compensated_integral_exact_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:03:54.0119+00:00
-- url     : https://prove2.me/submissions/4eecc1ec-d4be-40d9-9db5-12e04b0f3b0c

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_triplet_measure_min_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_exact_partition_transport_from_generic
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reuse the Proved generic negative jump partition in the exact source branch. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      ∀ β : ℝ, 0 < β →
      (∫ x, (Real.exp (β * x) - 1 -
        (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β =
      (∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) +
      (∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure) := by
  intro Ω mΩ P hP D hbv β hβ
  have hμ := p2m86_bv_triplet_measure_min_integrable Ω P D
  have hsplit :=
    source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
      D.triplet.levyMeasure hμ β hβ
  exact p2m86_bv_exact_partition_transport_from_generic Ω P D hbv β hβ hsplit
