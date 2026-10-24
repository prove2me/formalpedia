-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:10:45.444558+00:00
-- url     : https://prove2.me/submissions/abe9d611-2440-486b-b44b-23efe91b0ef5

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_fubini
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_product_volume

open scoped BigOperators

theorem solution
    (n : Nat) (T : Real) (hT : 0 < T) :
    (∫⁻ t in Set.Ioo (0 : Real) T,
      MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}
        ∂MeasureTheory.volume) =
      ENNReal.ofReal (T ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by
  exact Eq.trans (OAI.PiExponent.DeterminantContradiction.simplex_slice_fubini n T hT) (OAI.PiExponent.DeterminantContradiction.simplex_product_volume n T hT)