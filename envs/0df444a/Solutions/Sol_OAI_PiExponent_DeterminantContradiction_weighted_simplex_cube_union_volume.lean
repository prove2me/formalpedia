-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_cube_union_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:03:43.929752+00:00
-- url     : https://prove2.me/submissions/c631bb2c-1ea6-43fd-8bed-b9df2875e518

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_finite_nat_cube_union_volume

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ) :
    MeasureTheory.volume {x : Fin m → ℝ | ∃ a ∈ OAI.PiExponent.realWeightedSimplex w T, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} =
      ((OAI.PiExponent.realWeightedSimplex w T).card : ENNReal) := by
  exact OAI.PiExponent.DeterminantContradiction.finite_nat_cube_union_volume
    (OAI.PiExponent.realWeightedSimplex w T)