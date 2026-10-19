-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_card_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:00:32.577642+00:00
-- url     : https://prove2.me/submissions/2eb9c3f4-bda7-47a1-a3f6-d4df0ffbbef5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_cube_cover
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_cube_union_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_toReal_le_card_of_cube_cover

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) ≤
      ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) := by
  apply OAI.PiExponent.DeterminantContradiction.weighted_simplex_toReal_le_card_of_cube_cover
    m w T hT
  · exact OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_cube_cover
      m w T hw hT
  · exact OAI.PiExponent.DeterminantContradiction.weighted_simplex_cube_union_volume
      m w T