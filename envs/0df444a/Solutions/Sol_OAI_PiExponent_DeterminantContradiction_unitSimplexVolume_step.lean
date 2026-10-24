-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:20:42.293328+00:00
-- url     : https://prove2.me/submissions/f02ed5a8-edce-4791-8a16-d0d62e12d36d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_recurrence
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_arithmetic
open scoped BigOperators

theorem solution (n : Nat)
    (h : MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_recurrence,
    OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_arithmetic n h]