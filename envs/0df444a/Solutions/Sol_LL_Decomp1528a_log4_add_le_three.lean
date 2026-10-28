-- Prove2me | solution 1 for LL_Decomp1528a.log4_add_le_three
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:27:16.719997+00:00
-- url     : https://prove2.me/submissions/d5169a60-33b3-4932-a622-ff5e767c9417

import Mathlib

open Real

theorem solution {t : ℝ} (ht : 1 ≤ t) : log 4 + 2 * log t / √t ≤ 3 := by
  have hs : 0 < √t := Real.sqrt_pos.2 (by linarith)
  have hlogs : log √t ≤ √t / exp 1 := by
    have h := Real.log_le_sub_one_of_pos (x := √t / exp 1) (by positivity)
    rw [Real.log_div hs.ne' (exp_pos 1).ne', Real.log_exp] at h
    linarith
  have hlt : log t = 2 * log √t := by
    rw [← Real.log_rpow hs, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (by linarith)]
  have h1 : 2 * log t / √t ≤ 4 / exp 1 := by
    rw [div_le_div_iff₀ hs (exp_pos 1), hlt]
    have := mul_le_mul_of_nonneg_left hlogs (show (0:ℝ) ≤ 4 * exp 1 by positivity)
    have he : 4 * exp 1 * (√t / exp 1) = 4 * √t := by field_simp
    nlinarith [exp_pos 1]
  have h4 : log 4 < 1.3863 := by
    have : log 4 = 2 * log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have he : 4 / exp 1 < 1.4716 := by
    rw [div_lt_iff₀ (exp_pos 1)]; linarith [Real.exp_one_gt_d9]
  linarith
