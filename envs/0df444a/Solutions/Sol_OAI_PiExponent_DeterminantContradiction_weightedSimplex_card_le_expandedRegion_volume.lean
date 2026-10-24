-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_expandedRegion_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:12:13.310544+00:00
-- url     : https://prove2.me/submissions/1aa5c278-de91-4732-a5dc-2f577b803ea4

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Definitions.Def_OAI_PiExponent_DeterminantContradiction_UnitBoxes
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitBoxUnion_volume_lower
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_unitBoxUnion_subset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (H : Real) (hH : 0 ≤ H) :
    ENNReal.ofReal ((strictWeightedSimplex w H).card : Real) ≤
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (∑ i, w i * x i) ≤ H + Finset.univ.sum w} := by
  exact le_trans
    (unitBoxUnion_volume_lower (strictWeightedSimplex w H))
    (MeasureTheory.measure_mono
      (strictWeightedSimplex_unitBoxUnion_subset n w hw H hH))