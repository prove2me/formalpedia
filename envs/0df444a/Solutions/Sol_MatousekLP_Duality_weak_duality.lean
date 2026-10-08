-- Prove2me | solution 1 for MatousekLP.Duality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:47:00.962131+00:00
-- url     : https://prove2.me/submissions/0ab716c9-a772-4583-ac44-94c46c587622

import Definitions.Def_MatousekLP_Duality_PrimalDual
import Mathlib

open Matrix MatousekLP.Duality

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    (∀ x y, IsPrimalFeasible A b x → IsDualFeasible A c y → c ⬝ᵥ x ≤ b ⬝ᵥ y) ∧
    (PrimalUnbounded A b c → ¬ ∃ y, IsDualFeasible A c y) ∧
    (DualUnbounded A b c → ¬ ∃ x, IsPrimalFeasible A b x) := by
  have key : ∀ x y, IsPrimalFeasible A b x → IsDualFeasible A c y → c ⬝ᵥ x ≤ b ⬝ᵥ y := by
    rintro x y ⟨hAx, hx⟩ ⟨hAy, hy⟩
    calc c ⬝ᵥ x ≤ (Aᵀ *ᵥ y) ⬝ᵥ x := dotProduct_le_dotProduct_of_nonneg_right hAy hx
      _ = y ⬝ᵥ (A *ᵥ x) := by rw [mulVec_transpose, ← dotProduct_mulVec]
      _ ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hAx hy
      _ = b ⬝ᵥ y := dotProduct_comm _ _
  refine ⟨key, ?_, ?_⟩
  · rintro hU ⟨y, hy⟩
    obtain ⟨x, hx, hlt⟩ := hU (b ⬝ᵥ y)
    exact absurd (key x y hx hy) (not_le.mpr hlt)
  · rintro hU ⟨x, hx⟩
    obtain ⟨y, hy, hlt⟩ := hU (c ⬝ᵥ x)
    exact absurd (key x y hx hy) (not_le.mpr hlt)
