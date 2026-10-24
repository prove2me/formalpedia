-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:05:50.758689+00:00
-- url     : https://prove2.me/submissions/0cf3ba20-7bc6-4269-91b4-01fce65bda53

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_step

open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
    ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  induction n with
  | zero =>
      simpa [Nat.factorial_zero] using
        OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_zero
  | succ n ih =>
      exact OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_step n ih