-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.diagonal_map_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:28:28.379029+00:00
-- url     : https://prove2.me/submissions/164858f7-f5fc-47d4-90ec-ad8d618a7b70

import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_map_volume_of_measurable_finite
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplexRegion_measurable_finite

open scoped BigOperators Topology
open OAI.PiExponent.DeterminantContradiction

theorem solution (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hw : ∀ i, 0 < w i) :
    ENNReal.toReal (MeasureTheory.volume ((fun x i => w i * x i) '' weightedSimplexRegion w T)) =
      (∏ i : Fin m, w i) * ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) := by
  have hmf := weightedSimplexRegion_measurable_finite m w T hw
  exact diagonal_map_volume_of_measurable_finite m w hw (weightedSimplexRegion w T) hmf.1 hmf.2