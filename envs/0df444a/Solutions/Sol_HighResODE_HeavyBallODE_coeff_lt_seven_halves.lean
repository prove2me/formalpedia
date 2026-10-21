-- Prove2me | solution 1 for HighResODE.HeavyBallODE.coeff_lt_seven_halves
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:23:40.726147+00:00
-- url     : https://prove2.me/submissions/9b7aeb7c-116d-4e64-a706-da58faaec40b

import Mathlib
set_option autoImplicit false

theorem solution (μ s : ℝ) (hμ : 0 < μ) (hs : 0 < s) (hμs : μ * s ≤ 1) :
    1 / 2 + 3 / (1 + Real.sqrt (μ * s)) ^ 3 + 2 * μ * s / (1 + Real.sqrt (μ * s)) < 7 / 2 := by
  have hp : 0 < μ * s := mul_pos hμ hs
  have ha0 : 0 < Real.sqrt (μ * s) := Real.sqrt_pos.2 hp
  have ha1 : Real.sqrt (μ * s) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hμs
  have hsq : Real.sqrt (μ * s) ^ 2 = μ * s := Real.sq_sqrt hp.le
  have e : 2 * μ * s = 2 * Real.sqrt (μ * s) ^ 2 := by rw [hsq]; ring
  rw [e]
  generalize Real.sqrt (μ * s) = a at ha0 ha1
  have hu : 0 < 1 + a := by linarith
  have : 3 / (1 + a) ^ 3 + 2 * a ^ 2 / (1 + a) < 3 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos ha0 ha0, mul_pos ha0 hu, mul_pos (mul_pos ha0 ha0) ha0, mul_nonneg ha0.le (sub_nonneg.2 ha1), mul_nonneg (mul_pos ha0 ha0).le (sub_nonneg.2 ha1), pow_pos ha0 4, pow_pos ha0 5, mul_nonneg (pow_pos ha0 3).le (sub_nonneg.2 ha1), mul_nonneg (pow_pos ha0 4).le (sub_nonneg.2 ha1)]
  linarith
