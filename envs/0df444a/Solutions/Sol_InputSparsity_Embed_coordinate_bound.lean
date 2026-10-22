-- Prove2me | solution 1 for InputSparsity.Embed.coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:05:13.043489+00:00
-- url     : https://prove2.me/submissions/e758c615-312a-4acd-9d4d-ae2a3d8fbac5

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

set_option autoImplicit false
open InputSparsity.Embed Matrix

theorem solution {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : HasOrthonormalCols U) (y : Fin n → ℝ)
    (hy : y ∈ LinearMap.range (Matrix.mulVecLin U)) (hunit : sqNorm y = 1) :
    ∀ i : Fin n, y i ^ 2 ≤ lev U i := by
  intro i
  obtain ⟨x, rfl⟩ := hy
  simp only [Matrix.mulVecLin_apply] at hunit ⊢
  have h1 : sqNorm (U *ᵥ x) = ∑ j, x j ^ 2 := by
    have h : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
      have : Uᵀ * U = 1 := hU
      rw [this, Matrix.one_mulVec]
    simpa [sqNorm, dotProduct, sq] using h
  have h2 : (U *ᵥ x) i ^ 2 ≤ (∑ j, U i j ^ 2) * ∑ j, x j ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => U i j) x
    simpa [Matrix.mulVec, dotProduct] using this
  rw [hunit] at h1
  rw [← h1] at h2
  unfold lev
  linarith
