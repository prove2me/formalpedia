-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_map
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:23:21.967913+00:00
-- url     : https://prove2.me/submissions/457d29a1-4724-4712-9f90-abc692960119

import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open OAI.PiExponent.DeterminantContradiction

theorem solution (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hw : ∀ i, 0 < w i) :
    (fun x i => w i * x i) '' weightedSimplexRegion w T =
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · intro i
      exact mul_nonneg (hw i).le (hx.1 i)
    · simpa using hx.2
  · intro hy
    refine ⟨fun i => y i / w i, ?_, ?_⟩
    · constructor
      · intro i
        exact div_nonneg (hy.1 i) (hw i).le
      · calc
          ∑ i : Fin m, w i * (y i / w i) = ∑ i : Fin m, y i := by
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [ne_of_gt (hw i)]
          _ ≤ T := hy.2
    · funext i
      field_simp [ne_of_gt (hw i)]