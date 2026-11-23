-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_large_jump_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:41:04.334451+00:00
-- url     : https://prove2.me/submissions/4b63a8f8-c05c-4829-8109-7954e9abea0e

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_compensated_integrable
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem solution
    (μ : Measure ℝ) (hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ)
    (θ : ℝ) (hθ : 0 < θ) :
    -(∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂μ) / θ
      ≤ ∫ y in Iic (-1 : ℝ), (Real.exp (θ * y) - 1) / θ ∂μ := by
  have hcomp := Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_compensated_integrable
    μ hμ θ hθ.le
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (-1 : ℝ)) μ := by
    refine hμ.restrict.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y + 1), (show y ≤ (-1 : ℝ) from hy)]
    rw [min_eq_left hy2]
  have hkernel : IntegrableOn (fun y : ℝ => (Real.exp (θ * y) - 1) / θ)
      (Iic (-1 : ℝ)) μ := by
    refine ((hcomp.mono_set (by
      intro y hy
      have hy' : y ≤ (-1 : ℝ) := by simpa using hy
      exact lt_of_le_of_lt hy' (by norm_num))).const_mul θ⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
      intro h
      exact (not_lt_of_ge (by simpa using hy)) h.1
    simp [Set.indicator_of_notMem hnot, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hconst : IntegrableOn (fun _ : ℝ => -(1 / θ)) (Iic (-1 : ℝ)) μ := by
    simpa only [IntegrableOn, mul_one] using hone.const_mul (-(1 / θ))
  have heq : (∫ y in Iic (-1 : ℝ), -(1 / θ) ∂μ) =
      -(∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂μ) / θ := by
    have hc := integral_const_mul (μ := μ.restrict (Iic (-1 : ℝ))) (-(1 / θ))
      (fun _ : ℝ => (1 : ℝ))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hc
  rw [← heq]
  refine integral_mono_ae hconst hkernel ?_
  filter_upwards with y
  have hnum : (-1 : ℝ) ≤ Real.exp (θ * y) - 1 := by
    linarith [(Real.exp_pos (θ * y)).le]
  have hdiv : (-1 : ℝ) / θ ≤ (Real.exp (θ * y) - 1) / θ :=
    (div_le_div_iff_of_pos_right hθ).2 hnum
  simpa only [neg_div] using hdiv
