-- Prove2me | solution 1 for JRPHard.Shor.two_rpow_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T12:14:11.944617+00:00
-- url     : https://prove2.me/submissions/9d637465-d0a3-460c-af85-47a5372a97e4

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (2 : ℝ) ^ (-x) ≤ 1 - x / 2 := by
  have h2 : (2 : ℝ) ^ (-x) = Real.exp (x • (-Real.log 2) + (1 - x) • (0 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    simp
    ring
  have hc := convexOn_exp.2 (Set.mem_univ (-Real.log 2)) (Set.mem_univ (0 : ℝ)) hx0 (sub_nonneg.2 hx1)
    (by ring : x + (1 - x) = 1)
  rw [h2]
  refine hc.trans ?_
  have : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  simp only [smul_eq_mul, Real.exp_zero, this]
  linarith
