-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:10:37.834591+00:00
-- url     : https://prove2.me/submissions/2d28e8b6-aac8-472d-8abd-68a7701a6e03

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_region_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_scale

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) =
      T ^ m / ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) := by
  rw [weighted_simplex_region_scale m w T hw]
  rw [standard_simplex_region_volume m T hT]
  simp only [div_eq_mul_inv]
  ring