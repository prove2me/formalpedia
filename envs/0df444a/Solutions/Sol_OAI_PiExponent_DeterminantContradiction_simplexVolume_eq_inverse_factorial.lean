-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inverse_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:24:41.104107+00:00
-- url     : https://prove2.me/submissions/6abe78d5-4837-471f-a8db-2105e33d75da

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero_47e3ceaa
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_47e3ceaa
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / ((Nat.factorial n : Nat) : Real)) := by
  cases n with
  | zero =>
      exact OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_47e3ceaa
  | succ n =>
      rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_47e3ceaa n]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      <;> ring