-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.inverse_factorial_succ_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:38:47.980983+00:00
-- url     : https://prove2.me/submissions/4110f949-a205-4f58-a96c-302896646ba1

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (n : Nat) :
    ENNReal.ofReal (1 / ((Nat.factorial n : Nat) : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) =
      ENNReal.ofReal (1 / ((Nat.factorial (n + 1) : Nat) : Real)) := by
  have hfac : 0 <= 1 / ((Nat.factorial n : Nat) : Real) := by positivity
  have hfac_ne : ((Nat.factorial n : Nat) : Real) ≠ 0 := by positivity
  have hnext_ne : ((n + 1 : Nat) : Real) ≠ 0 := by positivity
  rw [← ENNReal.ofReal_mul hfac]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp [hfac_ne, hnext_ne]