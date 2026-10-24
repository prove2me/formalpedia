-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_expanded_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:20:09.257581+00:00
-- url     : https://prove2.me/submissions/fe7b7916-92cc-4867-8aba-1fbbaf2d7ebe

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_le_weighted_region_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_region_volume_formula
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (B : Real)
    (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    ((OAI.PiExponent.realWeightedSimplex w B).card : Real) ≤
      (B + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  have h := OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_weighted_region_volume
    w B hw hB
  rw [OAI.PiExponent.DeterminantContradiction.weighted_region_volume_formula w B hw hB] at h
  exact h