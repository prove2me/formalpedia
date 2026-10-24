-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_fubini
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:56:44.974865+00:00
-- url     : https://prove2.me/submissions/7a31ea45-1a84-4c88-bd9c-c3c056ed3226

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_integral_eq_full
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_full_fubini

open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) :
    (∫⁻ t in Set.Ioo (0 : Real) T,
      MeasureTheory.volume
        {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}
      ∂MeasureTheory.volume) =
      MeasureTheory.volume
        {z : Real × (Fin n → Real) |
          0 ≤ z.1 ∧ (∀ i, 0 ≤ z.2 i) ∧ z.1 + (∑ i, z.2 i) < T} := by
  exact
    (OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_eq_full
      n T hT).trans
      (OAI.PiExponent.DeterminantContradiction.simplex_full_fubini n T)