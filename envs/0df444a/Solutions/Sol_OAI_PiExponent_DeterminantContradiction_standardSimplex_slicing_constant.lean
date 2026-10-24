-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_slicing_constant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:16:28.417511+00:00
-- url     : https://prove2.me/submissions/365236c0-41b9-4a77-aa36-b1e5f8e7caee

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_slicing_fubini
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_integrated_homothety
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {y : Fin (n + 1) → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      ∫⁻ t in Set.Icc (0 : Real) 1,
        (ENNReal.ofReal (1 - t) ^ n *
          MeasureTheory.volume
            {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1})
        ∂MeasureTheory.volume := by
  exact (OAI.PiExponent.DeterminantContradiction.standardSimplex_slicing_fubini n).trans
    (OAI.PiExponent.DeterminantContradiction.standardSimplex_integrated_homothety n)
