-- Prove2me | solution 2 for ModernConvex.ConicDuality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:26:23.194683+00:00
-- url     : https://prove2.me/submissions/12d0ebf3-b7e8-4472-8015-f4cb34cda71f

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem
set_option autoImplicit false
open Matrix

theorem solution {m n : ℕ} (K : Set (Fin m → ℝ))
    (hK : ModernConvex.ConicDuality.IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : ModernConvex.ConicDuality.AssumptionA A)
    (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ∀ (x : Fin n → ℝ) (l : Fin m → ℝ), ModernConvex.ConicDuality.PrimalFeasible K A b x →
      ModernConvex.ConicDuality.DualFeasible K A c l → b ⬝ᵥ l ≤ c ⬝ᵥ x := by
  intro x l hx hl
  obtain ⟨hAl, hlK⟩ := hl
  have h : 0 ≤ l ⬝ᵥ (A *ᵥ x - b) := hlK _ hx
  rw [dotProduct_sub] at h
  have h2 : c ⬝ᵥ x = l ⬝ᵥ (A *ᵥ x) := by
    rw [← hAl, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  rw [h2, dotProduct_comm b l]
  linarith
