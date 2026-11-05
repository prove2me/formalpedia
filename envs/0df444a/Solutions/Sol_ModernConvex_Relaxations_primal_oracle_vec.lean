-- Prove2me | solution 1 for ModernConvex.Relaxations.primal_oracle_vec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:44:18.372198+00:00
-- url     : https://prove2.me/submissions/312769c0-d6cf-4a1d-905d-961f1fdf2b55

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_MatrixVec

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- A non-positive-semidefinite symmetric matrix has a vector of negative quadratic form. -/
theorem exists_neg_vector {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (h : ¬ M.PosSemidef) : ∃ v : Fin n → ℝ, v ⬝ᵥ (M *ᵥ v) < 0 := by
  by_contra hcon
  push_neg at hcon
  exact h (posSemidef_iff_dotProduct_mulVec.mpr ⟨hM, hcon⟩)

/-- `v ⬝ᵥ (Z *ᵥ v) = Σ i, Σ j, Z i j * (v i * v j)`. -/
theorem dotProduct_mulVec_eq_sum_sum {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (Z *ᵥ v) = ∑ i, ∑ j, Z i j * (v i * v j) := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The coordinate dot product of the enumerated vectors is the Frobenius pairing. -/
theorem vecFin_dotProduct {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    vecFin A ⬝ᵥ vecFin B = ∑ i, ∑ j, A i j * B i j := by
  have h1 : vecFin A ⬝ᵥ vecFin B = Matrix.vec A ⬝ᵥ Matrix.vec B := by
    simp only [dotProduct, vecFin]
    exact Equiv.sum_comp finProdFinEquiv.symm
      (fun p : Fin n × Fin n => Matrix.vec A p * Matrix.vec B p)
  rw [h1, Matrix.vec_dotProduct_vec]
  have hsymmA : ∀ i j : Fin n, A j i = A i j := by
    intro i j
    simpa using hA.apply i j
  have hsymmB : ∀ i j : Fin n, B j i = B i j := by
    intro i j
    simpa using hB.apply i j
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.transpose_apply, hsymmA j i, hsymmB j i]

/-- **The primal oracle in vector form.** For a symmetric matrix, reindexed as a vector of length
`n * n`, either it is positive semidefinite, or there is a nonzero vector `w` with
`(y - x) ⬝ᵥ w ≤ 0` for every positive semidefinite `y`.

The cut is explicit: `w = vecFin (fun i j => -(v i * v j))` where `v` is a negative direction. -/
theorem primal_oracle_vec_proof {n : ℕ} (x : Fin (n * n) → ℝ) (hx : (finToMat x).IsHermitian) :
    (finToMat x).PosSemidef ∨
      ∃ w : Fin (n * n) → ℝ, w ≠ 0 ∧
        ∀ y : Fin (n * n) → ℝ, (finToMat y).PosSemidef → (y - x) ⬝ᵥ w ≤ 0 := by
  by_cases h : (finToMat x).PosSemidef
  · exact Or.inl h
  · obtain ⟨v, hv⟩ := exists_neg_vector hx h
    refine Or.inr ⟨vecFin (Matrix.of fun i j => -(v i * v j)), ?_, ?_⟩
    · intro hw
      have h0 : (Matrix.of fun i j => -(v i * v j) : Matrix (Fin n) (Fin n) ℝ) = 0 := by
        rw [← finToMat_vecFin (A := Matrix.of fun i j => -(v i * v j)), hw]
        ext i j
        simp [finToMat]
      have hv0 : v = 0 := by
        funext i
        have hi : -(v i * v i) = 0 := by
          have := congrFun (congrFun h0 i) i
          simpa using this
        have h2 : v i * v i = 0 := by linarith
        exact mul_self_eq_zero.mp h2
      rw [hv0] at hv
      simpa using hv
    · intro y hy
      have hyH : (finToMat y).IsHermitian := hy.isHermitian
      have hWH : (Matrix.of fun i j => -(v i * v j) : Matrix (Fin n) (Fin n) ℝ).IsHermitian :=
        isHermitian_neg_mul v
      have hsub : (finToMat y - finToMat x).IsHermitian := hyH.sub hx
      have hsubeq : y - x = vecFin (finToMat y - finToMat x) := by
        rw [vecFin_sub, vecFin_finToMat, vecFin_finToMat]
      rw [hsubeq, vecFin_dotProduct hsub hWH]
      have hYq : 0 ≤ ∑ i, ∑ j, (finToMat y) i j * (v i * v j) := by
        rw [← dotProduct_mulVec_eq_sum_sum]
        exact hy.dotProduct_mulVec_nonneg v
      have hXq : ∑ i, ∑ j, (finToMat x) i j * (v i * v j) < 0 := by
        rw [← dotProduct_mulVec_eq_sum_sum]
        exact hv
      have hrow : ∀ i, (∑ j, (finToMat y - finToMat x) i j * -(v i * v j))
          = -((∑ j, (finToMat y) i j * (v i * v j))
              - ∑ j, (finToMat x) i j * (v i * v j)) := by
        intro i
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.sub_apply]
        ring
      have hsplit : ∑ i, ∑ j, (finToMat y - finToMat x) i j * -(v i * v j)
          = -((∑ i, ∑ j, (finToMat y) i j * (v i * v j))
              - ∑ i, ∑ j, (finToMat x) i j * (v i * v j)) := by
        simp only [hrow]
        rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
      simp only [Matrix.of_apply]
      rw [hsplit]
      linarith

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} (x : Fin (n * n) → ℝ) (hx : (finToMat x).IsHermitian) :
    (finToMat x).PosSemidef ∨
      ∃ w : Fin (n * n) → ℝ, w ≠ 0 ∧
        ∀ y : Fin (n * n) → ℝ, (finToMat y).PosSemidef → (y - x) ⬝ᵥ w ≤ 0 :=
  ModernConvex.Relaxations.primal_oracle_vec_proof x hx
