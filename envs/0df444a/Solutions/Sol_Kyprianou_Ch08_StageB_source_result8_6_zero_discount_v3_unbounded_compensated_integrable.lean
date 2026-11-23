-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_compensated_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:34:16.953184+00:00
-- url     : https://prove2.me/submissions/4695118c-7b94-4507-9684-bf6a464e0331

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_neg_remainder_bounds
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (μ : Measure ℝ) (hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ) :
    ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn
        (fun y : ℝ => Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
        (Iio (0 : ℝ)) μ := by
  intro θ hθ
  let f : ℝ → ℝ := fun y => Real.exp (θ * y) - 1 -
    θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
  have hmin_nonneg : 0 ≤ᵐ[μ] (fun y : ℝ => min 1 (y ^ 2)) :=
    Filter.Eventually.of_forall (fun y => le_min (by norm_num) (sq_nonneg y))
  have hdom_int : Integrable (fun y : ℝ => (1 + θ ^ 2) * min 1 (y ^ 2)) μ :=
    hμ.const_mul _
  have hf_meas : Measurable f := by
    dsimp [f]
    measurability
  have hbound (y : ℝ) (hy : y < 0) :
      |f y| ≤ (1 + θ ^ 2) * min 1 (y ^ 2) := by
    have hz : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.le
    by_cases hsmall : -1 < y
    · have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
      have hy2 : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y + 1)]
      have hr := AvramDividend.Classical.exp_neg_remainder_bounds (θ * y) hz
      have hb : |Real.exp (θ * y) - 1 - θ * y| ≤ (1 + θ ^ 2) * y ^ 2 := by
        rw [abs_of_nonneg hr.1]
        nlinarith [hr.2, sq_nonneg y, sq_nonneg θ]
      simpa only [f, Set.indicator_of_mem hmem, mul_one, min_eq_right hy2] using hb
    · have hnot : y ∉ Ioo (-1 : ℝ) 1 := fun h => hsmall h.1
      have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y + 1)]
      have he0 : 0 ≤ Real.exp (θ * y) := (Real.exp_pos _).le
      have he1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hz
      have hb : |Real.exp (θ * y) - 1| ≤ (1 + θ ^ 2) * 1 := by
        rw [abs_of_nonpos (by linarith)]
        nlinarith [sq_nonneg θ]
      simpa only [f, Set.indicator_of_notMem hnot, mul_zero, sub_zero,
        min_eq_left hy2] using hb
  apply Integrable.mono' hdom_int.restrict hf_meas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  simpa only [Real.norm_eq_abs] using hbound y hy
