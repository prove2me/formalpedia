-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:44:49.13011+00:00
-- url     : https://prove2.me/submissions/366272ca-949f-4995-a712-0e41e1ac166a

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair6_count_sandwich
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair6_squeeze
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n -> Real) (hw : forall i, 0 < w i) :
    Tendsto (fun H : Real => ((strictWeightedSimplex w H).card : Real) / H ^ n) atTop
      (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w))) := by
  have hsand := weightedSimplex_card_normalized_tendsto_427e7a71_repair6_count_sandwich n w hw
  have hbound : Filter.Eventually
      (fun H : Real => And
        (((H - Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n
          <= ((strictWeightedSimplex w H).card : Real) / H ^ n)
        (((strictWeightedSimplex w H).card : Real) / H ^ n <=
          ((H + Finset.univ.sum w) ^ n /
            ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)) atTop := by
    filter_upwards [hsand, eventually_gt_atTop (0 : Real)] with H h hH
    have hpow : 0 <= H ^ n := le_of_lt (pow_pos hH n)
    exact And.intro (div_le_div_of_nonneg_right h.1 hpow)
      (div_le_div_of_nonneg_right h.2 hpow)
  exact weightedSimplex_card_normalized_tendsto_427e7a71_repair6_squeeze
    (fun H => ((H - Finset.univ.sum w) ^ n /
      ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)
    (fun H => ((H + Finset.univ.sum w) ^ n /
      ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)
    (fun H => ((strictWeightedSimplex w H).card : Real) / H ^ n)
    (1 / ((n.factorial : Real) * Finset.univ.prod w))
    (weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto n w hw).1
    (weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto n w hw).2
    hbound