-- Prove2me | solution 1 for GeneralizedComplex.bShift_pairing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:29:03.42006+00:00
-- url     : https://prove2.me/submissions/a438b903-8419-42d9-a8e9-86b07de8e7e4

import Mathlib
import Definitions.Def_GeneralizedComplex_Basic

open Matrix

open GeneralizedComplex in
theorem solution {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = -B)
    (u v : GIdx N → ℝ) :
    pairing (bShift B *ᵥ u) (bShift B *ᵥ v) = pairing u v := by
  unfold pairing bShift vecPart formPart
  simp only [fromBlocks_mulVec, Sum.elim_inl, Sum.elim_inr, one_mulVec, zero_mulVec, add_zero]
  have key : ∀ X Y : Fin N → ℝ, (Bᵀ *ᵥ X) ⬝ᵥ Y = -((Bᵀ *ᵥ Y) ⬝ᵥ X) := by
    intro X Y
    have h1 : (Bᵀ *ᵥ Y) ⬝ᵥ X = (B *ᵥ X) ⬝ᵥ Y := by
      rw [mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm]
    rw [h1, hB, neg_mulVec, neg_dotProduct]
  simp only [add_dotProduct]
  have := key (u ∘ Sum.inl) (v ∘ Sum.inl)
  simp only [Function.comp_def] at this ⊢
  linarith
