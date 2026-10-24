-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_ge_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:03:20.305203+00:00
-- url     : https://prove2.me/submissions/2ec7fbdd-479f-44af-afad-725c1545bafd

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_region_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_floor_box_bound
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (R : Real)
    (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) :
    (R - ∑ i : Fin m, w i) ^ m / ((Nat.factorial m : Nat) : Real) / (∏ i : Fin m, w i) ≤
      ((realWeightedSimplex w R).card : Real) := by
  rw [← weightedSimplex_region_volume w (R - ∑ i : Fin m, w i) hw (by linarith)]
  exact weightedSimplex_floor_box_bound w R hw hR