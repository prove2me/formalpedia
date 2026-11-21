-- Prove2me | solution 8 for MasulloRH.zero_free_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:35:18.842365+00:00
-- url     : https://prove2.me/submissions/8da774de-ccd2-4d25-b850-e5f69de59d3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_rational_RH_of_fixed_damping_mean_square
import Theorems.Thm_NymanBeurling_damped_moebius_truncation_mean_square_convergence

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (_hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  by_cases hhigh : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hhigh
  · intro hz
    have hline := NymanBeurling.rational_RH_of_fixed_damping_mean_square
      (fun ε hε hεhalf ↦ NymanBeurling.damped_moebius_truncation_mean_square_convergence
        ε hε hεhalf 1 zero_lt_one)
      s (by linarith) (lt_of_not_ge hhigh) hz
    linarith
