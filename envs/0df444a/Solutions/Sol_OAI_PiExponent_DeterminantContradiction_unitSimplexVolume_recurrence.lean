-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:27:42.183071+00:00
-- url     : https://prove2.me/submissions/2f1741bb-f58a-43eb-9f44-b51726b48d36

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ENNReal.ofReal (1 / (n + 1 : Real)) *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1} := by
  rw [OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux,
    OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux]
  rw [← ENNReal.ofReal_mul]
  congr 1
  have hf : (Nat.factorial (n + 1) : Real) = (n + 1 : Real) * Nat.factorial n := by
    simp [Nat.factorial_succ]
  rw [hf]
  field_simp
  positivity