-- Prove2me | solution 1 for OAI.PiExponent.rational_scale_error_control_rational_w
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:50:05.569622+00:00
-- url     : https://prove2.me/submissions/3ca658b5-9d9a-4c3b-b841-cb99dac0baf9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem solution
    (theta : ℚ) (m K : ℕ) (v : ℚ) (s : ℝ)
    (hK : 0 < K) (htheta : 0 < theta)
    (hbalance : (K : ℝ) ^ 2 * (theta : ℝ) ^ m < 1)
    (hv : 0 < v) (hs : 0 < s) :
    ∃ w : ℚ, 0 < w ∧
      (K : ℚ) * (w / v) * theta ^ m < 1 ∧
      s * (K : ℝ) / (w : ℝ) < 2 * s / (v : ℝ) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hθ : (0 : ℝ) < (theta : ℝ) ^ m := pow_pos (by exact_mod_cast htheta) m
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hlt : (K : ℝ) * v / 2 < v / ((K : ℝ) * (theta : ℝ) ^ m) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    have : (K : ℝ) * (K * (theta : ℝ) ^ m) < 2 := by nlinarith
    nlinarith
  obtain ⟨w, hw1, hw2⟩ := exists_rat_btwn hlt
  have hw' : (0 : ℝ) < w := lt_trans (by positivity) hw1
  refine ⟨w, by exact_mod_cast hw', ?_, ?_⟩
  · have h : ((K : ℚ) * (w / v) * theta ^ m : ℚ) = ((K : ℝ) * ((w : ℝ) / v) * (theta : ℝ) ^ m : ℝ) := by
      push_cast; ring
    have h2 : (K : ℝ) * ((w : ℝ) / v) * (theta : ℝ) ^ m < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hw2
      rw [mul_div_assoc', div_mul_eq_mul_div, div_lt_one hv']
      nlinarith
    have h3 : (((K : ℚ) * (w / v) * theta ^ m : ℚ) : ℝ) < 1 := by rw [h]; exact h2
    exact_mod_cast h3
  · rw [div_lt_div_iff₀ hw' hv']
    nlinarith
