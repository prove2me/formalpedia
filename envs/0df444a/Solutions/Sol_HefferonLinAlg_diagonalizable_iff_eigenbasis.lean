-- Prove2me | solution 1 for HefferonLinAlg.diagonalizable_iff_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T14:32:00.306873+00:00
-- url     : https://prove2.me/submissions/32333844-62cc-4645-b409-4438525789cd

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

private theorem col_mul (A P : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    (fun i => (A * P) i j) = A *ᵥ (fun i => P i j) := by
  funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

private theorem col_mul_diagonal (P : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (j : Fin n) :
    (fun i => (P * Matrix.diagonal d) i j) = d j • (fun i => P i j) := by
  funext i
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq', mul_comm]

/-- With `P` invertible, `P⁻¹ A P` is diagonal exactly when each column of `P` is an
eigenvector of `A` with the corresponding diagonal entry as eigenvalue. -/
private theorem conj_diag_iff (A P : Matrix (Fin n) (Fin n) K) (d : Fin n → K)
    (hP : IsUnit P.det) :
    P⁻¹ * A * P = Matrix.diagonal d ↔
      ∀ j, A *ᵥ (fun i => P i j) = d j • (fun i => P i j) := by
  have key : P⁻¹ * A * P = Matrix.diagonal d ↔ A * P = P * Matrix.diagonal d := by
    constructor
    · intro h
      calc A * P = P * (P⁻¹ * A * P) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
                Matrix.mul_nonsing_inv _ hP, Matrix.one_mul]
        _ = P * Matrix.diagonal d := by rw [h]
    · intro h
      rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP,
          Matrix.one_mul]
  rw [key]
  constructor
  · intro h j; rw [← col_mul, ← col_mul_diagonal, h]
  · intro h
    ext i j
    have h1 := congrFun (col_mul A P j) i
    have h2 := congrFun (col_mul_diagonal P d j) i
    have h3 := congrFun (h j) i
    rw [h1, h2]; exact h3

theorem solution (A : Matrix (Fin n) (Fin n) K) :
    (∃ (P : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
        IsUnit P.det ∧ P⁻¹ * A * P = Matrix.diagonal d) ↔
      (∃ (B : Module.Basis (Fin n) K (Fin n → K)) (lam : Fin n → K),
        ∀ i, A *ᵥ B i = lam i • B i) := by
  constructor
  · rintro ⟨P, d, hP, hdiag⟩
    have hcols : LinearIndependent K P.col :=
      Matrix.linearIndependent_cols_of_isUnit (Matrix.isUnit_iff_isUnit_det P |>.mpr hP)
    have hcard : Fintype.card (Fin n) = Module.finrank K (Fin n → K) := by simp
    refine ⟨basisOfLinearIndependentOfCardEqFinrank' P.col hcols hcard, d, ?_⟩
    intro i
    have := (conj_diag_iff A P d hP).mp hdiag i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    exact this
  · rintro ⟨B, lam, hB⟩
    refine ⟨(Pi.basisFun K (Fin n)).toMatrix B, lam, ?_, ?_⟩
    · haveI := Module.Basis.invertibleToMatrix (Pi.basisFun K (Fin n)) B
      exact Matrix.isUnit_det_of_invertible _
    · haveI := Module.Basis.invertibleToMatrix (Pi.basisFun K (Fin n)) B
      refine (conj_diag_iff A _ lam (Matrix.isUnit_det_of_invertible _)).mpr ?_
      intro j
      have hentry : (fun i => (Pi.basisFun K (Fin n)).toMatrix B i j) = B j := by
        funext i; simp [Module.Basis.toMatrix_apply]
      rw [hentry]; exact hB j
