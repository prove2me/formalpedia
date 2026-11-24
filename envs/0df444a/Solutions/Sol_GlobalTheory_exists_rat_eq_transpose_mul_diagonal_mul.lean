-- Prove2me | solution 1 for GlobalTheory.exists_rat_eq_transpose_mul_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:58.011372+00:00
-- url     : https://prove2.me/submissions/59720842-8720-4653-8dad-5d9edfe2ed00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSmulEqTransposeMulDiagonalMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hs : A.IsSymm) (hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) :
    ∃ (d : Fin n → ℚ) (Q : Matrix (Fin n) (Fin n) ℚ), (∀ i, 0 < d i) ∧ Q.det ≠ 0 ∧
      A = Qᵀ * Matrix.diagonal d * Q := by
  have hsym : (Matrix.toBilin' A).IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hs
  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := Fin n → ℚ)
    (B := Matrix.toBilin' A) (LinearMap.BilinForm.isSymm_iff.mp hsym)
  have hr : Module.finrank ℚ (Fin n → ℚ) = n := by simp
  let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr hr
  let v := v₀.reindex e
  have hv : ∀ i j, i ≠ j → v i ⬝ᵥ A *ᵥ v j = 0 := by
    intro i j hij
    have h := hv₀ (e.symm.injective.ne hij)
    simp only [Function.onFun] at h
    rw [Matrix.toBilin'_apply'] at h
    simpa only [v, Module.Basis.reindex_apply] using h
  let P : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => v i j
  have hP : IsUnit P := Matrix.linearIndependent_rows_iff_isUnit.mp v.linearIndependent
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdiag : P * A * Pᵀ = Matrix.diagonal fun i => v i ⬝ᵥ A *ᵥ v i := by
    ext i j
    have : (P * A * Pᵀ) i j = v i ⬝ᵥ A *ᵥ v j := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, P, dotProduct, Matrix.mulVec]
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hv i j hij]
  refine ⟨fun i => v i ⬝ᵥ A *ᵥ v i, (P⁻¹)ᵀ, fun i => hp _ (v.ne_zero i), ?_, ?_⟩
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det P hPd).ne_zero
  · rw [← hdiag, Matrix.transpose_transpose]
    have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
    have h2 : Pᵀ * (P⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc A = (P⁻¹ * P) * A * (Pᵀ * (P⁻¹)ᵀ) := by rw [h1, h2]; simp
      _ = P⁻¹ * (P * A * Pᵀ) * (P⁻¹)ᵀ := by simp only [Matrix.mul_assoc]
end GlobalTheory
