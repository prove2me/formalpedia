-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m86_bv_exact_partition_transport_from_generic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:18:53.45319+00:00
-- url     : https://prove2.me/submissions/e8c79a1a-04a8-429c-acbf-57a28fcf24f7

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Transport the negative-halfline identity by null support and scalar algebra. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P),
    HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
    ∀ β : ℝ, 0 < β →
    (∫ y in Iio (0 : ℝ),
        (Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)) / β ∂D.triplet.levyMeasure) =
        (∫ y in Ioo (-1 : ℝ) 0,
          (Real.exp (β * y) - 1 - β * y) / β ∂D.triplet.levyMeasure) +
        (∫ y in Iic (-1 : ℝ),
          (Real.exp (β * y) - 1) / β ∂D.triplet.levyMeasure) →
    (∫ x, (Real.exp (β * x) - 1 -
        (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β =
      (∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) +
      (∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure) := by
  intro Ω mΩ P hP D hbv β hβ hsplit
  have hae : ∀ᵐ x ∂D.triplet.levyMeasure, x ∈ Iio (0 : ℝ) := by
    rw [ae_iff]
    have hs : {x : ℝ | ¬ x ∈ Iio (0 : ℝ)} = Ici 0 := by
      ext x
      simp only [mem_setOf_eq, mem_Iio, mem_Ici, not_lt]
    rw [hs]
    exact D.negativeJumps
  have hrestrict := Measure.restrict_eq_self_of_ae_mem hae
  rw [hrestrict, integral_div] at hsplit
  rw [hsplit]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  field_simp [hβ.ne']
  <;> ring
