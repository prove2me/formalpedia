-- Prove2me | solution 1 for LevyStochCalc.Driver.abs_cellDrift_le
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:28:17.271529+00:00
-- url     : https://prove2.me/submissions/81e0b856-fa47-43c7-b2a3-ae4cc07887df

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F001
open LevyStochCalc.Driver
theorem solution (l : ℝ) (a b : ℝ) (s : ℝ) : |cellDrift l a b s| ≤ l ^ 2 / 2 := by
  by_cases h : s ∈ Set.Ioc a b
  · simp only [cellDrift, Set.indicator_of_mem h, one_pow, mul_one]
    rw [abs_of_nonpos (by nlinarith [sq_nonneg l])]
    linarith
  · simp only [cellDrift, Set.indicator_of_notMem h, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, abs_zero]
    positivity
#print axioms solution
