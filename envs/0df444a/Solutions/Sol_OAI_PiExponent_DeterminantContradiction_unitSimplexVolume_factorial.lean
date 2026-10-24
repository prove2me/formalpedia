-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:38:47.297963+00:00
-- url     : https://prove2.me/submissions/e1b09c79-edaa-4d5d-a57a-f0101997f22c

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux <;> assumption
