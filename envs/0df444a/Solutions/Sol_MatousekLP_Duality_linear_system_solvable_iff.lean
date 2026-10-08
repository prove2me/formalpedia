-- Prove2me | solution 1 for MatousekLP.Duality.linear_system_solvable_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:56:43.929526+00:00
-- url     : https://prove2.me/submissions/99181836-955d-4387-8fb8-e0e8c872f835

import Definitions.Def_MatousekLP_Duality_PrimalDual
import Mathlib

open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, Aᵀ *ᵥ y = 0 → y ⬝ᵥ b = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, hy, zero_dotProduct]
  · intro h
    by_contra hb
    have hnot : b ∉ LinearMap.range (Matrix.mulVecLin A) := by
      rintro ⟨x, hx⟩; exact hb ⟨x, hx⟩
    obtain ⟨f, hfb, hmap⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hnot (Module.Projective.of_free)
    -- represent the functional `f` by a vector `y`
    set y : Fin m → ℝ := fun i => f (Pi.single i 1)
    have hf : ∀ v, f v = y ⬝ᵥ v := by
      intro v
      conv_lhs => rw [show v = ∑ i, v i • Pi.single i (1 : ℝ) by
        ext k; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, map_smul, y, dotProduct, mul_comm]
    have hvanish : ∀ x : Fin n → ℝ, y ⬝ᵥ (A *ᵥ x) = 0 := by
      intro x
      rw [← hf]
      have : f (A *ᵥ x) ∈ (LinearMap.range (Matrix.mulVecLin A)).map f :=
        ⟨A *ᵥ x, ⟨x, rfl⟩, rfl⟩
      rw [hmap] at this
      simpa using this
    have hAy : Aᵀ *ᵥ y = 0 := by
      funext j
      have := hvanish (Pi.single j 1)
      rw [dotProduct_mulVec, ← mulVec_transpose] at this
      simpa [dotProduct, Pi.single_apply] using this
    exact hfb (by rw [hf]; exact h y hAy)
