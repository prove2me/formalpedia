-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedStrictRowCount_eventually_polynomial_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:38:36.044838+00:00
-- url     : https://prove2.me/submissions/d7824a22-ec53-4f08-b093-4072468156e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictSimplex_card_eventually_polynomial_bound

open Filter
open scoped Topology

theorem solution
    {m : ℕ} (K : ℕ) (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ,
      (∀ᶠ H : ℝ in atTop,
        (Fintype.card (Fin K × {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H}) : ℝ) ≤
          C * (H + 1) ^ (m + 1)) := by
  obtain ⟨C, hC⟩ :=
    OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_card_eventually_polynomial_bound
      w hw
  refine ⟨(K : ℝ) * C, ?_⟩
  filter_upwards [hC] with H hH
  have hcard :
      (Fintype.card (Fin K × {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H}) : ℝ) =
        (K : ℝ) *
          (Fintype.card {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H} : ℝ) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  rw [hcard]
  calc
    (K : ℝ) * (Fintype.card {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H} : ℝ) ≤
        (K : ℝ) * (C * (H + 1) ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg K)
    _ = ((K : ℝ) * C) * (H + 1) ^ (m + 1) := by ring