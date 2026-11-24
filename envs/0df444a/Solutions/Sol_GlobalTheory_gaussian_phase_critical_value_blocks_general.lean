-- Prove2me | solution 1 for GlobalTheory.gaussian_phase_critical_value_blocks_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:07.613867+00:00
-- url     : https://prove2.me/submissions/1e0bff2e-6564-4567-97ae-0767bf97be65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GaussianPhaseCriticalValueBlocksGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexOrder
namespace GlobalTheory
private lemma dot_transpose_mulVec' {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) (u : n → ℂ) (v : m → ℂ) : u ⬝ᵥ Xᵀ *ᵥ v = v ⬝ᵥ X *ᵥ u := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
end GlobalTheory
end

set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (C : Matrix n m ℂ) (B : Matrix m n ℂ)
    (a c : m → ℂ) (b d : n → ℂ) (hN : IsUnit (1 - C * B).det) :
    let S : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 Cᵀ C 0
    let T : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 B Bᵀ 0
    let w : m ⊕ n → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b)
    let u : m ⊕ n → ℂ := Sum.elim a b + S *ᵥ w
    1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u)
      = a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
        + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c := by
  intro S T w u
  have hM : IsUnit (1 - B * C).det := by rwa [det_one_sub_mul_comm]
  set M := (1 - B * C)⁻¹ with hMdef
  set N := (1 - C * B)⁻¹ with hNdef
  have hM1 : M * (1 - B * C) = 1 := nonsing_inv_mul _ hM
  have hM2 : (1 - B * C) * M = 1 := mul_nonsing_inv _ hM
  have hN1 : N * (1 - C * B) = 1 := nonsing_inv_mul _ hN
  have hN2 : (1 - C * B) * N = 1 := mul_nonsing_inv _ hN
  have hMB : B * N = M * B := by
    have h : B * (1 - C * B) = (1 - B * C) * B := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    calc B * N = M * ((1 - B * C) * B) * N := by
          rw [← Matrix.mul_assoc, hM1, Matrix.one_mul]
      _ = M * B := by
          rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, hN2, Matrix.mul_one]
  have hCM : C * M = N * C := by
    have h : C * (1 - B * C) = (1 - C * B) * C := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    calc C * M = N * ((1 - C * B) * C) * M := by
          rw [← Matrix.mul_assoc, hN1, Matrix.one_mul]
      _ = N * C := by
          rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, hM2, Matrix.mul_one]
  have hMBC : B * (N * C) = M - 1 := by
    rw [← Matrix.mul_assoc, hMB, ← hM1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hNCB : N * C * B = N - 1 := by
    rw [← hN1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hinv : (1 - T * S)⁻¹ = fromBlocks M 0 0 Nᵀ := by
    apply inv_eq_left_inv
    have h1 : (1 - T * S) = fromBlocks (1 - B * C) 0 0 (1 - C * B)ᵀ := by
      simp only [T, S, fromBlocks_multiply, ← fromBlocks_one]
      ext (i | i) (j | j) <;> simp [transpose_mul, one_apply, eq_comm]
    rw [h1, fromBlocks_multiply, ← transpose_mul, hM1, hN2]
    simp
  have hw : w = Sum.elim (M *ᵥ (c + B *ᵥ b)) (Nᵀ *ᵥ (d + Bᵀ *ᵥ a)) := by
    have h : Sum.elim c d + T *ᵥ Sum.elim a b = Sum.elim (c + B *ᵥ b) (d + Bᵀ *ᵥ a) := by
      simp only [T, fromBlocks_mulVec]
      ext (i | i) <;> simp
    simp only [w]
    rw [hinv, h, fromBlocks_mulVec]
    simp
  have hu : u = Sum.elim (a + (N * C)ᵀ *ᵥ (d + Bᵀ *ᵥ a)) (b + (N * C) *ᵥ (c + B *ᵥ b)) := by
    simp only [u, S]
    rw [hw, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr,
      mulVec_mulVec, ← transpose_mul, hCM]
    ext (i | i) <;> simp
  rw [hu, hw, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
  simp only [dotProduct_add, mulVec_add, mulVec_mulVec, ← transpose_mul, dot_transpose_mulVec',
    hMB, hMBC, hNCB, sub_mulVec, one_mulVec, dotProduct_sub]
  rw [dotProduct_comm c a]
  ring
end GlobalTheory
