-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:14:42.771064+00:00
-- url     : https://prove2.me/submissions/5f683695-f54f-414a-a19f-e98b6ba2a718

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_inverse_factorial
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_inverse_factorial_succ

open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inverse_factorial (n + 1),
      OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inverse_factorial n,
      OAI.PiExponent.DeterminantContradiction.inverse_factorial_succ n]