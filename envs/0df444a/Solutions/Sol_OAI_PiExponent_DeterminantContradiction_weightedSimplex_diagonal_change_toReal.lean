-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_diagonal_change_toReal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:01:02.341985+00:00
-- url     : https://prove2.me/submissions/fd2bc2f9-97c6-4628-916e-611c87914072

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_preimage_volume_toReal
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_eq_diagonal_preimage
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_compact
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, w i * x i ≤ A}).toReal =
      (MeasureTheory.volume {y : Fin m → Real | (∀ i : Fin m, 0 ≤ y i) ∧
        ∑ i : Fin m, y i ≤ A}).toReal / ∏ i : Fin m, w i := by
  have hset := OAI.PiExponent.DeterminantContradiction.weighted_simplex_eq_diagonal_preimage
    (w := w) (A := A) hw
  rw [hset]
  exact OAI.PiExponent.DeterminantContradiction.diagonal_preimage_volume_toReal
    w hw _ (OAI.PiExponent.DeterminantContradiction.standard_simplex_compact A hA)