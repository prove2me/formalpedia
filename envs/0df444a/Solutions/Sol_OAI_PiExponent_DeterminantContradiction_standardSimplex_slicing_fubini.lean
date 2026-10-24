-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_slicing_fubini
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:25:10.915265+00:00
-- url     : https://prove2.me/submissions/a782d2c3-c090-46ef-9125-28cd9015c53f

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_integratedScaledSimplexVolume
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {y : Fin (n + 1) → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      ∫⁻ t in Set.Icc (0 : Real) 1,
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1 - t}
        ∂MeasureTheory.volume := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled
        (n + 1) 1 (by norm_num),
      OAI.PiExponent.DeterminantContradiction.integratedScaledSimplexVolume n]
  norm_num