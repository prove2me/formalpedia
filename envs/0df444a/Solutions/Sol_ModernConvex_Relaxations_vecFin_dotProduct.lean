-- Prove2me | solution 1 for ModernConvex.Relaxations.vecFin_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:44:17.635312+00:00
-- url     : https://prove2.me/submissions/191c3da4-552f-4156-be64-ced23bba9a16

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
theorem vecFin_dotProduct_proof {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
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


end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    vecFin A ⬝ᵥ vecFin B = ∑ i, ∑ j, A i j * B i j :=
  ModernConvex.Relaxations.vecFin_dotProduct_proof hA hB
