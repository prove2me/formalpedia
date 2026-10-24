-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_upper_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:55:28.591165+00:00
-- url     : https://prove2.me/submissions/91480531-1d81-444a-b9c2-9d3bbfd7ada6

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_le_box_expansion
import Mathlib.Data.Real.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    Filter.Eventually
      (fun H : Real =>
        ((strictWeightedSimplex w H).card : Real) ≤
          (H + Finset.univ.sum w) ^ n /
            ((n.factorial : Real) * Finset.univ.prod w))
      atTop := by
  filter_upwards [eventually_gt_atTop (0 : Real)] with H hH
  exact OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_box_expansion
    n w hw H (le_of_lt hH)