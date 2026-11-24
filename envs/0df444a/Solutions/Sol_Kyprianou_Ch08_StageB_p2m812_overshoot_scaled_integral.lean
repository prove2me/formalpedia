-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m812_overshoot_scaled_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:44:19.155812+00:00
-- url     : https://prove2.me/submissions/fa77d13f-ed69-4002-a112-9a21efeea635

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (r x y : ℝ) (hr : 0 < r) (hr1 : r < 1) (hx : 0 < x) (hy : 0 ≤ y) :
    (∫ t in (0 : ℝ)..y/x, t^(-r)/(1+t)) =
      x^r * ∫ t in (0 : ℝ)..y, t^(-r)/(t+x) := by
  have hsub := intervalIntegral.integral_comp_div
    (a := (0 : ℝ)) (b := y) (f := fun t : ℝ => t^(-r)/(1+t)) hx.ne'
  simp only [zero_div, smul_eq_mul] at hsub
  have he : (∫ t in (0 : ℝ)..y, (t/x)^(-r)/(1+t/x)) =
      (x * x^r) * ∫ t in (0 : ℝ)..y, t^(-r)/(t+x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hy] at ht
    dsimp only
    rw [Real.div_rpow ht.1 hx.le, Real.rpow_neg hx.le]
    have ht' : t+x ≠ 0 := (add_pos_of_nonneg_of_pos ht.1 hx).ne'
    rw [show 1+t/x = (t+x)/x by field_simp [hx.ne']; ring]
    field_simp [hx.ne', (Real.rpow_pos_of_pos hx r).ne', ht']
    <;> ring
  rw [he] at hsub
  exact mul_left_cancel₀ hx.ne' (by simpa only [mul_assoc] using hsub.symm)
