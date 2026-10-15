-- Prove2me | solution 1 for OAI.PiExponent.window_lower_ratio_of_scaled_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:24:22.572382+00:00
-- url     : https://prove2.me/submissions/a6dd5513-852f-4fd8-8e2d-571c8a4bc9c8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

theorem solution
    (theta A R : ℝ) (m K : ℕ)
    (htheta : 0 < theta) (hA : 0 < A)
    (hscaled : (R * A / theta) ^ m / 8 < (K : ℝ)) :
    R ^ m / (8 * ((m : ℝ) + 1)) <
      ((K : ℝ) * theta ^ m) / (((m : ℝ) + 1) * A ^ m) := by
  have hfactor : 0 < theta ^ m / A ^ m :=
    div_pos (pow_pos htheta m) (pow_pos hA m)
  have hmul := mul_lt_mul_of_pos_right hscaled hfactor
  have hleft :
      (R * A / theta) ^ m / 8 * (theta ^ m / A ^ m) = R ^ m / 8 := by
    rw [div_pow, mul_pow]
    field_simp [ne_of_gt htheta, ne_of_gt hA]
    <;> ring
  have hright :
      (K : ℝ) * (theta ^ m / A ^ m) = ((K : ℝ) * theta ^ m) / A ^ m :=
    (mul_div_assoc (K : ℝ) (theta ^ m) (A ^ m)).symm
  rw [hleft, hright] at hmul
  have hden : 0 < (m : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
  have hfinal := div_lt_div_of_pos_right hmul hden
  simpa only [div_div, mul_comm (A ^ m) ((m : ℝ) + 1)] using hfinal