-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:09:20.8957+00:00
-- url     : https://prove2.me/submissions/e0b6b1d0-bd4b-4e58-aa18-9653fae5fe4e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_floor_box_cover
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_finite_unit_box_volume_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (R : Real)
    (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧
      ∑ i, w i * x i ≤ R - ∑ i : Fin m, w i}).toReal ≤
      ((realWeightedSimplex w R).card : Real) := by
  exact (weightedSimplex_floor_box_cover w R hw hR).trans
    (finite_unit_box_volume_bound (realWeightedSimplex w R))