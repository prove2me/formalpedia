-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:53:54.385471+00:00
-- url     : https://prove2.me/submissions/e36b5125-be4d-40ad-9d75-57959404b563
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_card_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    T ^ m / ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) ≤
        ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) := by
  rw [← OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_volume
    m w T hw hT]
  exact OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_card_bound
    m w T hw hT