-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m812_overshoot_integral_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:44:18.66159+00:00
-- url     : https://prove2.me/submissions/d0e3b130-1ef1-40b9-bc42-930f1aa00cd0

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (r x y : ℝ) (hr : 0 < r) (hr1 : r < 1) (hx : 0 < x) (hy : 0 ≤ y) :
    (∫ t in (0 : ℝ)..y, t^(-r)/(t+x)) -
      (∫ t in (0 : ℝ)..y, t^(-r)/(t+1)) =
      (1-x) * ∫ t in (0 : ℝ)..y, t^(-r)/((t+1)*(t+x)) := by
  let f (c t : ℝ) := t^(-r)/(t+c)
  have hint (c : ℝ) (hc : 0 < c) : IntervalIntegrable (f c) volume 0 y := by
    have hp : IntervalIntegrable (fun t : ℝ => t^(-r)) volume 0 y :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa only [f, div_eq_mul_inv, Pi.inv_apply, Pi.add_apply, id_eq] using hp.mul_continuousOn
      ((continuous_id.add continuous_const).continuousOn.inv₀
        (fun t ht => by rw [uIcc_of_le hy] at ht; exact (add_pos_of_nonneg_of_pos ht.1 hc).ne'))
  change (∫ t in (0 : ℝ)..y, f x t) - (∫ t in (0 : ℝ)..y, f 1 t) = _
  rw [← intervalIntegral.integral_sub (hint x hx) (hint 1 zero_lt_one),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hy] at ht
  change t^(-r)/(t+x) - t^(-r)/(t+1) = (1-x)*(t^(-r)/((t+1)*(t+x)))
  field_simp [(add_pos_of_nonneg_of_pos ht.1 hx).ne',
    (add_pos_of_nonneg_of_pos ht.1 zero_lt_one).ne']
  <;> ring
