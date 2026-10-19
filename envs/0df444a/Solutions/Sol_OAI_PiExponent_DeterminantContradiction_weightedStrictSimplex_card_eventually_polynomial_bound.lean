-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_card_eventually_polynomial_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:44:40.316321+00:00
-- url     : https://prove2.me/submissions/8b893277-b7c7-43ea-8119-0016c52bf5dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictSimplex_box_card_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictSimplex_box_product_bound

open Filter
open scoped Topology BigOperators

theorem solution
    {m : ℕ} (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ,
      (∀ᶠ H : ℝ in atTop,
        (Fintype.card {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H} : ℝ) ≤
          C * (H + 1) ^ (m + 1)) := by
  obtain ⟨C, hC⟩ :=
    OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_product_bound
      w hw
  refine ⟨C, ?_⟩
  filter_upwards [hC] with H hH
  exact
    (OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_card_bound
      w hw H).trans hH