-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_count_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:50:37.459194+00:00
-- url     : https://prove2.me/submissions/efc09af4-4a1b-42b7-9971-453b45d17e22

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_lower_eventually
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_upper_eventually
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    Filter.Eventually
      (fun H : Real => And
        ((H - Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)
          ≤ ((strictWeightedSimplex w H).card : Real))
        (((strictWeightedSimplex w H).card : Real) ≤
          (H + Finset.univ.sum w) ^ n /
            ((n.factorial : Real) * Finset.univ.prod w)))
      atTop := by
  filter_upwards
    [OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_lower_eventually n w hw,
      OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_upper_eventually n w hw]
    with H h_lower h_upper
  exact ⟨h_lower, h_upper⟩