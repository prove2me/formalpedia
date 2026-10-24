-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:13:14.289021+00:00
-- url     : https://prove2.me/submissions/31ffb4b4-e41a-4aed-bd8b-f82aa51222cc

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_zero_aux
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ_slice_aux
open scoped BigOperators

theorem solution (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      ENNReal.ofReal (T ^ m / (Nat.factorial m : Real)) := by
  induction m with
  | zero =>
      simpa using
        OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_aux T hT
  | succ m ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_slice_aux m T hT, ih]
      rw [Nat.factorial_succ]
      push_cast
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1 <;> field_simp <;> ring