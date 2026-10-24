-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair5_count_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:16.606728+00:00
-- url     : https://prove2.me/submissions/0437080d-7dde-425e-b72f-1d954ddd28c4

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair6_count_sandwich
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
  apply OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_count_sandwich <;> assumption
