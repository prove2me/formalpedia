-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:59:43.498202+00:00
-- url     : https://prove2.me/submissions/27891eb9-d3d7-4586-8719-a58a9908d37e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_volume_measure_scaling_positive
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_volume_measure_scaling_zero
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ r} =
      ENNReal.ofReal (r ^ n) *
        MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
          ∑ i : Fin n, y i ≤ 1} := by
  by_cases hzero : r = 0
  · subst r
    exact OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling_zero n
  · exact OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling_positive
      n r hr (lt_of_le_of_ne hr (Ne.symm hzero))