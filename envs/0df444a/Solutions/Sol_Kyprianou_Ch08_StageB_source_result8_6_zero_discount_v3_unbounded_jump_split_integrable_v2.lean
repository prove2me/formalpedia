-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:58:50.427152+00:00
-- url     : https://prove2.me/submissions/752a73e9-dbca-4167-9021-d72c7fcb3f98

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_compensated_integrable
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem solution
    (μ : Measure ℝ) (hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ)
    (θ : ℝ) (hθ : 0 < θ) :
    (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 - (if -1 < y then θ * y else 0)) / θ ∂μ) =
      (∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ) +
      (∫ y in Iic (-1 : ℝ), (Real.exp (θ * y) - 1) / θ ∂μ) := by
  let K : ℝ → ℝ := fun y => Real.exp (θ * y) - 1 - (if -1 < y then θ * y else 0)
  have hcomp := Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_compensated_integrable
    μ hμ θ hθ.le
  have hK_int : IntegrableOn (fun y => K y / θ) (Iio (0 : ℝ)) μ := by
    refine (hcomp.const_mul θ⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    by_cases hs : -1 < y
    · have hmem : y ∈ Ioo (-1 : ℝ) 1 :=
        ⟨hs, lt_trans (by simpa using hy) (by norm_num : (0 : ℝ) < 1)⟩
      simp [K, hs, hmem, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    · have hnot : y ∉ Ioo (-1 : ℝ) 1 := fun h => hs h.1
      simp [K, hs, hnot, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hu : Iio (0 : ℝ) = Ioo (-1 : ℝ) 0 ∪ Iic (-1 : ℝ) := by
    ext y
    simp only [mem_Iio, mem_Ioo, mem_Iic, mem_union]
    constructor
    · intro hy
      by_cases hle : y ≤ -1
      · exact Or.inr hle
      · exact Or.inl ⟨by linarith, hy⟩
    · intro hy
      rcases hy with h | h
      · exact h.2
      · linarith
  have hdisj : Disjoint (Ioo (-1 : ℝ) 0) (Iic (-1 : ℝ)) :=
    disjoint_left.mpr (by
      intro y hy1 hy2
      exact (not_lt_of_ge (by simpa using hy2)) (by simpa using hy1.1))
  rw [hu]
  rw [MeasureTheory.integral_union_ae hdisj.aedisjoint measurableSet_Iic.nullMeasurableSet
    (hK_int.mono_set (by intro y hy; exact hy.2))
    (hK_int.mono_set (by
      intro y hy
      exact lt_of_le_of_lt (by simpa using hy) (by norm_num : (-1 : ℝ) < 0)))]
  congr 1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    simp [K, hy.1]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    have hnot : ¬ -1 < y := fun hgt => (not_lt_of_ge (by simpa using hy)) hgt
    simp [K, hnot]
