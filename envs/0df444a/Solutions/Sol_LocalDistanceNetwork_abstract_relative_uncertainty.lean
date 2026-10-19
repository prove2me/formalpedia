-- Prove2me | solution 1 for LocalDistanceNetwork.abstract_relative_uncertainty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:34:28.006987+00:00
-- url     : https://prove2.me/submissions/c5ad66d9-6494-4235-8ff3-19fe47fb26de

import Mathlib

theorem solution :
    (0.0105 : ℝ) ≤ 0.809 / 73.499 ∧ (0.809 : ℝ) / 73.499 < 0.0115 ∧
    (0.0085 : ℝ) ≤ 0.697 / 73.994 ∧ (0.697 : ℝ) / 73.994 < 0.0095 := by
  norm_num
