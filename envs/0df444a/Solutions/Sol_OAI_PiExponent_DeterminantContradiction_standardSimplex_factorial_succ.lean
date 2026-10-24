-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_factorial_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:59:13.816351+00:00
-- url     : https://prove2.me/submissions/655b9f89-900d-4746-9ef8-f47a20cc4b15

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem solution (n : Nat) :
    ENNReal.ofReal (1 / (n.factorial : Real)) / (n + 1 : ENNReal) =
      ENNReal.ofReal (1 / ((n + 1).factorial : Real)) := by
  have hn1 : (0 : Real) < (n + 1 : Real) := by positivity
  have hfac : (n.factorial : Real) ≠ 0 := by positivity
  have hreal :
      (1 / (n.factorial : Real)) / (n + 1 : Real) =
        1 / ((n + 1).factorial : Real) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp [hfac, ne_of_gt hn1] <;> ring
  have hden : (n + 1 : ENNReal) = ENNReal.ofReal (n + 1 : Real) := by
    norm_cast
  rw [hden]
  have henc := congrArg ENNReal.ofReal hreal
  rw [ENNReal.ofReal_div_of_pos hn1] at henc
  exact henc