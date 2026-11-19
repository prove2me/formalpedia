-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kc_exponent_identity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:52:50.674305+00:00
-- url     : https://prove2.me/submissions/a2b7a142-dcf7-4ee5-b8e1-2897b368665b

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem solution {α p q : ℝ} (n : ℕ) :
    (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p
      = ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n := by
  rw [show (2 : ℝ) ^ n = ((1 / 2 : ℝ) ^ (-1 : ℝ)) ^ n by norm_num]
  simp only [← Real.rpow_natCast]
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  rw [← Real.rpow_mul hpos.le, ← Real.rpow_mul hpos.le, ← Real.rpow_mul hpos.le,
      ← Real.rpow_mul hpos.le, ← Real.rpow_mul hpos.le,
      ← Real.rpow_add hpos, ← Real.rpow_sub hpos]
  congr 1
  ring
