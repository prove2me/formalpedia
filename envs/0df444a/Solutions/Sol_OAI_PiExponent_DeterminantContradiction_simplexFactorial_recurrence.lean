-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexFactorial_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:04:14.670625+00:00
-- url     : https://prove2.me/submissions/1558c000-0ec6-453b-9794-75271bbb14ae

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem solution (n : Nat) :
    ENNReal.ofReal (1 / (n + 1 : Real)) *
        ENNReal.ofReal (1 / (Nat.factorial n : Real)) =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  calc
    _ = ENNReal.ofReal
        ((1 / (n + 1 : Real)) * (1 / (Nat.factorial n : Real))) :=
      (ENNReal.ofReal_mul (by positivity : 0 <= (1 / (n + 1 : Real)))).symm
    _ = ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp <;> try positivity <;> ring