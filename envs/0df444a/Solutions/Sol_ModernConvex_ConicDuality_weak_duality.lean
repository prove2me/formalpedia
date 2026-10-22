-- Prove2me | solution 1 for ModernConvex.ConicDuality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:02:28.922539+00:00
-- url     : https://prove2.me/submissions/0522b0e1-d7e2-46d8-98e6-29528bbd23c3

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

open ModernConvex.ConicDuality

theorem solution {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ∀ (x : Fin n → ℝ) (l : Fin m → ℝ), PrimalFeasible K A b x → DualFeasible K A c l →
      b ⬝ᵥ l ≤ c ⬝ᵥ x := by
  intro x l hx ⟨hc, hl⟩
  have h1 := hl _ hx
  have h2 : c ⬝ᵥ x = l ⬝ᵥ (A *ᵥ x) := by
    rw [← hc, mulVec_transpose, dotProduct_mulVec]
  rw [dotProduct_sub] at h1
  rw [h2, dotProduct_comm b]
  linarith
