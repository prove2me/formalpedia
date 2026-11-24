-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m86_bv_exponent_slope_from_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:26:42.222851+00:00
-- url     : https://prove2.me/submissions/99b779d6-fdaa-475c-8d54-26c61bf7d305

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_triplet_eq
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- The BV exponent quotient has the physical drift as its limiting value. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ =>
        (∫ x, (Real.exp (β * x) - 1 -
          (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β)
        atTop (𝓝 (-∫ x in Set.Ioo (-1 : ℝ) 0, x ∂D.triplet.levyMeasure)) →
      Tendsto (fun β : ℝ => ψ β / β) atTop
        (𝓝 (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)) := by
  intro Ω mΩ P hP D ψ hψ hbv hlim
  have hae : ∀ᵐ x ∂D.triplet.levyMeasure, x ∈ Iio (0 : ℝ) := by
    rw [ae_iff]
    have hs : {x : ℝ | ¬ x ∈ Iio (0 : ℝ)} = Ici 0 := by
      ext x
      simp only [mem_setOf_eq, mem_Iio, mem_Ici, not_lt]
    rw [hs]
    exact D.negativeJumps
  have hrestrict := Measure.restrict_eq_self_of_ae_mem hae
  have hg : D.gaussianCoefficient = 0 := hbv.1
  have hsum := (tendsto_const_nhds (x := D.triplet.drift)).add hlim
  have hEq : (fun β : ℝ => D.triplet.drift +
      (∫ x, (Real.exp (β * x) - 1 -
        (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β) =ᶠ[atTop]
      (fun β : ℝ => ψ β / β) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    rw [source_result8_6_zero_discount_v3_unbounded_triplet_eq P D ψ hψ β hβ]
    rw [hg, hrestrict, integral_div]
    ring
  simpa only [bvDrift, neg_neg, sub_eq_add_neg] using hsum.congr' hEq
