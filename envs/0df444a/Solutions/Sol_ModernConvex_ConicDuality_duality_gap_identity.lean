-- Prove2me | solution 1 for ModernConvex.ConicDuality.duality_gap_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:03:05.822586+00:00
-- url     : https://prove2.me/submissions/c60f5b1c-fb33-417e-bbfa-cb4bf4b4ebe0

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

open ModernConvex.ConicDuality

theorem solution {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ∀ (x : Fin n → ℝ) (l : Fin m → ℝ), PrimalFeasible K A b x → DualFeasible K A c l →
      c ⬝ᵥ x - b ⬝ᵥ l = (A *ᵥ x - b) ⬝ᵥ l := by
  intro x l _ ⟨hc, _⟩
  have h2 : c ⬝ᵥ x = l ⬝ᵥ (A *ᵥ x) := by
    rw [← hc, mulVec_transpose, dotProduct_mulVec]
  rw [h2, sub_dotProduct, dotProduct_comm l]
