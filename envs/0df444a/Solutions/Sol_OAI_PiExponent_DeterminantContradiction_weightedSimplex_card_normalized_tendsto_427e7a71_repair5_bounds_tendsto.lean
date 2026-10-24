-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair5_bounds_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:05.54798+00:00
-- url     : https://prove2.me/submissions/da8ce55b-7d6d-4d19-95b9-7d4939eabb3d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    And
      (Tendsto (fun H : Real =>
        ((H - Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w))))
      (Tendsto (fun H : Real =>
        ((H + Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w)))) := by
  apply OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto <;> assumption
