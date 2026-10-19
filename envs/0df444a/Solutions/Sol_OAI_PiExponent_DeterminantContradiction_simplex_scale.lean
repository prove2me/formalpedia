-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T20:21:34.199708+00:00
-- url     : https://prove2.me/submissions/1a71ff76-f182-4708-a727-79cca9aa980a

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_scale_pos
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_scale_zero

open scoped BigOperators

theorem solution (k : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U}).toReal =
      (U ^ k) * (MeasureTheory.volume
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal := by
  by_cases h : U = 0
  · subst U
    exact OAI.PiExponent.DeterminantContradiction.simplex_scale_zero k
  · exact OAI.PiExponent.DeterminantContradiction.simplex_scale_pos k U
      (lt_of_le_of_ne hU (Ne.symm h))