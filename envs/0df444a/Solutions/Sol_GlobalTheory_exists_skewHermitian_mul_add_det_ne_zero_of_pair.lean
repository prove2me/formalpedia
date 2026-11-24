-- Prove2me | solution 1 for GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:25.122815+00:00
-- url     : https://prove2.me/submissions/ac06bda7-f8df-42db-8621-a024414a1676

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankNormalFormMatrixFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SkewHermitianPerturbIdempotentDetNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSkewHermitianMulAddDetNeZeroOfPair
import Theorems.Thm_GlobalTheory_T_exists_rank_normal_form_matrix_field
import Theorems.Thm_GlobalTheory_T_exists_skewHermitian_det_mul_add_ne_zero_of_idempotent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n C D hCD hrk
  obtain ⟨U, P, e, hU, hP, he, hE⟩ := GlobalTheory.T.exists_rank_normal_form_matrix_field k n C
  have hmul : ∀ A B : Matrix (Fin n) (Fin n) k,
      ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
    intro A B
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hinv : ∀ A : Matrix (Fin n) (Fin n) k, (((A.map σ)ᵀ).map σ)ᵀ = A := by
    intro A
    ext i j
    simp [hσ]
  have hone : (((1 : Matrix (Fin n) (Fin n) k).map σ)ᵀ) = 1 := by
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have h3 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUu
  set E : Matrix (Fin n) (Fin n) k := Matrix.diagonal e with hEdef
  have hEE : E * E = E := by
    rw [hEdef, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  have hEs : (E.map σ)ᵀ = E := by
    rw [hEdef, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  set Q : Matrix (Fin n) (Fin n) k := (P⁻¹.map σ)ᵀ with hQ
  set Ps : Matrix (Fin n) (Fin n) k := (P.map σ)ᵀ with hPs
  have hPQ : Ps * Q = 1 := by rw [hPs, hQ, ← hmul, h2, hone]
  have hQP : Q * Ps = 1 := by rw [hPs, hQ, ← hmul, h1, hone]
  have hQs : (Q.map σ)ᵀ = P⁻¹ := hinv _
  have hE' : E = Ps * ((C.map σ)ᵀ * (U.map σ)ᵀ) := by
    rw [← hEs, ← hE, hmul, hmul]
  have hA : E * ((U * D * Q).map σ)ᵀ = U * (C * (D.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hmul, hmul, hQs, ← hE]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P, h1, Matrix.one_mul]
  have hB : U * D * Q * E = U * (D * (C.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hE']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q, hQP, Matrix.one_mul]
  have hsum : E * ((U * D * Q).map σ)ᵀ + U * D * Q * E = 0 := by
    rw [hA, hB, ← Matrix.add_mul, ← Matrix.mul_add, hCD, Matrix.mul_zero, Matrix.zero_mul]
  have hrk' : ∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* (U * D * Q) = 0 → a = 0 := by
    intro a ha hb
    have e1 : U * C = E * P⁻¹ := by
      rw [← hE, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : U * D = (U * D * Q) * Ps := by
      rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
    have h0 : a ᵥ* U = 0 := by
      apply hrk
      · rw [Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      · rw [Matrix.vecMul_vecMul, e2, ← Matrix.vecMul_vecMul, hb, Matrix.zero_vecMul]
    have : a ᵥ* (U * U⁻¹) = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
    rwa [h3, Matrix.vecMul_one] at this
  obtain ⟨V', hV', hdet⟩ := GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent k σ hσ ε hε hσε n E (U * D * Q) hEE hEs hsum hrk'
  refine ⟨P * V' * Ps, ?_, ?_⟩
  · have hPss : (Ps.map σ)ᵀ = P := hinv _
    rw [hmul, hmul, hV', hPss, ← hPs]
    simp [Matrix.mul_assoc]
  · intro h
    apply hdet
    have : E * V' + U * D * Q = U * (C * (P * V' * Ps) + D) * Q := by
      rw [← hE, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one]
    rw [this, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul]
end GlobalTheory
