-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_unit
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:09:13.055618+00:00
-- url     : https://prove2.me/submissions/ec8b0292-500c-4899-b4ae-e9405649cce2

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_base_v2
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_slice_recurrence
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  induction n with
  | zero => exact OAI.PiExponent.DeterminantContradiction.simplexVolume_base_v2
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice_recurrence, ih]
      rw [Nat.factorial_succ]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      exact_mod_cast Nat.mul_comm (n + 1) (Nat.factorial n)