-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slice_fubini
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:02:59.734982+00:00
-- url     : https://prove2.me/submissions/6c0595b9-7269-4042-b9d6-b4b33831b412

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_formula
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_integral_formula
open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      (∫⁻ t in Set.Ioo (0 : Real) T,
        MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} ∂MeasureTheory.volume) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_volume_formula
        (m := n + 1) (T := T) (hT := hT),
      OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_formula
        (n := n) (T := T) (hT := hT)]