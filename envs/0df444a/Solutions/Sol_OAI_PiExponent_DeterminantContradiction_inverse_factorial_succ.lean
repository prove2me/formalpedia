-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.inverse_factorial_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:21:28.489972+00:00
-- url     : https://prove2.me/submissions/1dd6ccd4-511e-493c-83f7-89dde799ee04

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem solution (n : Nat) :
    ENNReal.ofReal (1 / ((Nat.factorial (n + 1) : Nat) : Real)) =
      ENNReal.ofReal (1 / ((Nat.factorial n : Nat) : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  have hfact :
      ((Nat.factorial (n + 1) : Nat) : Real) =
        ((Nat.factorial n : Nat) : Real) * ((n + 1 : Nat) : Real) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfactpos : 0 < ((Nat.factorial n : Nat) : Real) := by
    exact_mod_cast Nat.factorial_pos n
  have hnpos : 0 < ((n + 1 : Nat) : Real) := by
    positivity
  have hinv :
      1 / ((Nat.factorial (n + 1) : Nat) : Real) =
        (1 / ((Nat.factorial n : Nat) : Real)) *
          (1 / ((n + 1 : Nat) : Real)) := by
    rw [hfact]
    field_simp [ne_of_gt hfactpos, ne_of_gt hnpos]
  have hleft_nonneg :
      0 <= (1 / ((Nat.factorial n : Nat) : Real)) := by
    positivity
  rw [hinv, ENNReal.ofReal_mul hleft_nonneg]