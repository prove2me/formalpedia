-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:52:58.747663+00:00
-- url     : https://prove2.me/submissions/3f16955a-148d-458d-a0b8-6f8d43621a82

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_box_packing_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) ≤
        (T + ∑ i : Fin m, w i) ^ m /
          ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) := by
  apply OAI.PiExponent.DeterminantContradiction.weighted_lattice_box_packing_bound
    m (OAI.PiExponent.realWeightedSimplex w T) w T hw hT
  intro a ha
  have ha' : a ∈ (Fintype.piFinset
      (fun i => Finset.range (⌊T / w i⌋₊ + 1))).filter
      (fun a => ∑ i, w i * (a i : ℝ) ≤ T) := by
    simpa [OAI.PiExponent.realWeightedSimplex] using ha
  exact (Finset.mem_filter.mp ha').2