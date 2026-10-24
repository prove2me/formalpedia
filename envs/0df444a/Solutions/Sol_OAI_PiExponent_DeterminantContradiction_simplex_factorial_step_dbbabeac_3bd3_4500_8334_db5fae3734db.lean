-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_factorial_step_dbbabeac_3bd3_4500_8334_db5fae3734db
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:52:28.402658+00:00
-- url     : https://prove2.me/submissions/cf1eab6a-5b4d-4eae-b3df-5ed0016cab85

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem solution (n : Nat) :
    ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  have hf : (Nat.factorial n : Real) ≠ 0 := by
    positivity
  have hk : ((n + 1 : Nat) : Real) ≠ 0 := by
    positivity
  have hreal :
      1 / (Nat.factorial (n + 1) : Real) =
        (1 / (Nat.factorial n : Real)) * (1 / ((n + 1 : Nat) : Real)) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp [hf, hk]
    <;> ring
  rw [hreal]
  exact ENNReal.ofReal_mul (by positivity)