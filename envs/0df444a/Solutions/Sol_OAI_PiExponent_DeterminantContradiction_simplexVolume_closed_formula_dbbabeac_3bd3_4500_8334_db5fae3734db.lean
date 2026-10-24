-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_closed_formula_dbbabeac_3bd3_4500_8334_db5fae3734db
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:54:35.293534+00:00
-- url     : https://prove2.me/submissions/4d208cba-265b-4fcc-9b68-6da9257db9a7

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero_v2
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_recurrence_v2
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  induction n with
  | zero =>
      simpa using OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_v2
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence_v2, ih]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      have hn : (n + 1 : Real) ≠ 0 := by positivity
      have hf : (Nat.factorial n : Real) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp
      <;> ring