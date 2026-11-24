-- Prove2me | solution 1 for GlobalTheory.ClassFin.det_leading_gram_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:11:48.635394+00:00
-- url     : https://prove2.me/submissions/163e0069-f874-4ca7-ba21-d73b9be12c36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DetLeadingMinorGramIwasawa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → ∀ (j : ℕ) (h : j ≤ N), (((k * diagonal a * n)ᵀ * (k * diagonal a * n)).submatrix (Fin.castLE h) (Fin.castLE h)).det = ∏ i : Fin j, a (Fin.castLE h i) ^ 2 := by
  intro N k a n hk hd hn j h
  have h1 : (k * diagonal a * n)ᵀ * (k * diagonal a * n)
      = nᵀ * diagonal (fun i => a i ^ 2) * n := by
    have : diagonal (fun i => a i ^ 2) = diagonal a * diagonal a := by
      rw [diagonal_mul_diagonal]; simp [sq]
    rw [this, transpose_mul, transpose_mul, diagonal_transpose]
    calc nᵀ * (diagonal a * kᵀ) * (k * diagonal a * n)
        = nᵀ * (diagonal a * (kᵀ * k) * diagonal a) * n := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hk, Matrix.mul_one]
  have h2 : (nᵀ * diagonal (fun i => a i ^ 2) * n).submatrix (Fin.castLE h) (Fin.castLE h)
      = (n.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ
        * diagonal (fun i : Fin j => a (Fin.castLE h i) ^ 2)
        * n.submatrix (Fin.castLE h) (Fin.castLE h) := by
    ext p q
    rw [submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro r hr
      have hr' : j ≤ r.val := by
        by_contra hlt
        exact hr ⟨⟨r.val, not_le.mp hlt⟩, Fin.ext rfl⟩
      have : n r (Fin.castLE h q) = 0 := hn _ _ (by
        rw [Fin.lt_def]; have := q.2; simp; omega)
      rw [this, mul_zero]
    · intro r
      simp [Matrix.mul_diagonal]
  have h3 : (n.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    rw [det_of_isUpperTriangular]
    · simp [hd]
    · intro p q hpq
      exact hn _ _ (by
        have h' : q < p := hpq
        exact h')
  rw [h1, h2, det_mul, det_mul, det_transpose, h3, det_diagonal]
  simp
end GlobalTheory.ClassFin
