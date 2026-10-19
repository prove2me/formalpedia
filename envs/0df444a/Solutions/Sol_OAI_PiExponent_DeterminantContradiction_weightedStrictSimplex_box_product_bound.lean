-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_product_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:48:23.084419+00:00
-- url     : https://prove2.me/submissions/8c331e92-e70f-4d02-a1fd-7366698b304c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictSimplex_box_product_bound_explicit

open Filter
open scoped Topology BigOperators

theorem solution
    {m : ℕ} (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ,
      ∀ᶠ H : ℝ in atTop,
        (∏ i : Fin (m + 1), ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ)) ≤
          C * (H + 1) ^ (m + 1) := by
  refine ⟨∏ i : Fin (m + 1), (1 / w i + 2), ?_⟩
  exact OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_product_bound_explicit w hw