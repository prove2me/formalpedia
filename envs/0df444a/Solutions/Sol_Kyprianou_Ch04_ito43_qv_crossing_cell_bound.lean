-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_crossing_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:45:28.152044+00:00
-- url     : https://prove2.me/submissions/a6215858-74bb-4416-8a8c-ad4b1b42106d

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Quadratic energy error on a split grid cell. -/
theorem solution (A B M : ℝ) (hA : |A| ≤ M) :
    |(A+B)^2-A^2| ≤ 2*M*|B| + B^2 := by
  have h : (A+B)^2-A^2 = 2*A*B+B^2 := by ring
  rw [h]
  calc
    |2*A*B+B^2| ≤ |2*A*B|+|B^2| := abs_add_le _ _
    _ = 2*|A| * |B| + B^2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg B)]
      norm_num
    _ ≤ 2*M*|B| + B^2 := by
      have hh := mul_le_mul_of_nonneg_right hA (abs_nonneg B)
      linarith
