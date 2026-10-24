-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.det_ne_zero_of_linearIndependent_columns
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:42:27.595022+00:00
-- url     : https://prove2.me/submissions/2d172048-de81-47ec-a11c-46ea0890174d

import Mathlib
open scoped BigOperators

theorem solution
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Matrix alpha alpha Complex)
    (hA : LinearIndependent Complex A.col) : A.det ≠ 0 := by
  have := (Matrix.linearIndependent_cols_iff_isUnit).mp hA
  exact (Matrix.isUnit_iff_isUnit_det A).mp this |>.ne_zero
