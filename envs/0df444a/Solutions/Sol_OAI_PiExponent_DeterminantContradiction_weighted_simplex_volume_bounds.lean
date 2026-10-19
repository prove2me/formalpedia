-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:41:44.317038+00:00
-- url     : https://prove2.me/submissions/6fc92d3d-a322-4b26-b5d0-252a79e446bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_volume_lower_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_volume_upper_bound

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    T ^ m / ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) ≤
        ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) ∧
      ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) ≤
        (T + ∑ i : Fin m, w i) ^ m /
          ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) := by
  exact ⟨
    OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_lower_bound
      m w T hw hT,
    OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_upper_bound
      m w T hw hT⟩