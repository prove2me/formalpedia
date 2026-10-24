-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:13:38.385948+00:00
-- url     : https://prove2.me/submissions/3a86ec87-148a-4584-afc8-b1a35c099f76

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_shifted_boxes_volume_le_card
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    ENNReal.toReal
      (MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T})
      ≤ ((strictWeightedSimplex w (T + Finset.univ.sum w)).card : Real) := by
  exact le_trans
    (OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes
      n w hw T hT)
    (OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_shifted_boxes_volume_le_card
      n w T)