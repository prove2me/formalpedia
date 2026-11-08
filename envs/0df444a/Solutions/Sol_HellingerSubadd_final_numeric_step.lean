-- Prove2me | solution 1 for HellingerSubadd.final_numeric_step
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T15:08:02.303498+00:00
-- url     : https://prove2.me/submissions/63c4899c-a74f-4e90-9c6e-763b8af8b619

import Mathlib

/-- Hellinger subadditivity: the numerical step `2(6 log(96n) + 18/(96n)) ≤ 100 log n`. -/
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    2 * (6 * Real.log (96 * (n : ℝ)) + 18 / (96 * (n : ℝ))) ≤ 10 ^ 2 * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h96 : (96 : ℝ) ≤ n ^ 7 := by
    have h : (2 : ℝ) ^ 7 ≤ n ^ 7 := pow_le_pow_left₀ (by norm_num) h2 7
    norm_num at h ⊢
    linarith
  have hle : (96 : ℝ) * n ≤ n ^ 8 := by
    calc (96 : ℝ) * n ≤ n ^ 7 * n := by nlinarith
      _ = n ^ 8 := by ring
  have hlog : Real.log (96 * (n : ℝ)) ≤ 8 * Real.log n := by
    have h := Real.log_le_log (by positivity) hle
    rwa [Real.log_pow] at h
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hl2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2
  have hsmall : 36 / (96 * (n : ℝ)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h12 : 12 * Real.log (96 * (n : ℝ)) ≤ 96 * Real.log n := by linarith
  have h2log : 2 ≤ 4 * Real.log n := by nlinarith [Real.log_two_gt_d9]
  have h36 : 36 / (96 * (n : ℝ)) ≤ 4 * Real.log n := by linarith
  have hgoal : 12 * Real.log (96 * (n : ℝ)) + 36 / (96 * (n : ℝ)) ≤ 100 * Real.log n := by
    linarith
  calc 2 * (6 * Real.log (96 * (n : ℝ)) + 18 / (96 * (n : ℝ)))
      = 12 * Real.log (96 * (n : ℝ)) + 36 / (96 * (n : ℝ)) := by ring
    _ ≤ 100 * Real.log n := hgoal
    _ = 10 ^ 2 * Real.log n := by norm_num
