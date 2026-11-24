-- Prove2me | solution 1 for GlobalTheory.hermitian_involution_unitary_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:56.115536+00:00
-- url     : https://prove2.me/submissions/c3fffa27-ee98-40ce-8545-7ac1ef9bcfac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisAdaptedToCartanInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (t : Matrix (Fin n) (Fin n) ℂ)
    (hH : tᴴ = t) (ht : t * t = 1) :
    ∃ (p q : ℕ) (V : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
      Vᴴ * t * V = Matrix.fromBlocks 1 0 0 (-1) := by
  classical
  have hH' : t.IsHermitian := hH
  set U : Matrix (Fin n) (Fin n) ℂ := (hH'.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℂ := fun i => ((hH'.eigenvalues i : ℝ) : ℂ) with hd
  have hspec : t = U * diagonal d * Uᴴ := by
    have := hH'.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def] using this
  have hUU : U * Uᴴ = 1 := by
    have := hH'.eigenvectorUnitary.2.2
    simpa [star_eq_conjTranspose] using this
  have hUU' : Uᴴ * U = 1 := by
    have := hH'.eigenvectorUnitary.2.1
    simpa [star_eq_conjTranspose] using this
  have hD : Uᴴ * t * U = diagonal d := by
    rw [hspec]
    calc Uᴴ * (U * diagonal d * Uᴴ) * U = (Uᴴ * U) * diagonal d * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal d := by rw [hUU']; simp
  have hDD : diagonal d * diagonal d = 1 := by
    rw [← hD]
    calc Uᴴ * t * U * (Uᴴ * t * U) = Uᴴ * (t * (U * Uᴴ) * t) * U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, ht, Matrix.mul_one, hUU']
  have hsq : ∀ i, d i * d i = 1 := by
    intro i
    have := congrFun (congrFun hDD i) i
    simpa [diagonal_mul_diagonal] using this
  let e : Fin (Fintype.card {i // d i = 1}) ⊕ Fin (Fintype.card {i // ¬ d i = 1}) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl (fun i => d i = 1))
  have he1 : ∀ a, d (e (Sum.inl a)) = 1 := fun a => ((Fintype.equivFin {i // d i = 1}).symm a).2
  have he2 : ∀ a, d (e (Sum.inr a)) = -1 := fun a =>
    (mul_self_eq_one_iff.1 (hsq _)).resolve_left
      ((Fintype.equivFin {i // ¬ d i = 1}).symm a).2
  refine ⟨_, _, U.submatrix id e, ?_, ?_, ?_⟩
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, hUU, submatrix_id_id]
  · rw [conjTranspose_submatrix]
    have := Matrix.submatrix_mul_equiv Uᴴ U e (Equiv.refl _) e
    simp only [Equiv.coe_refl] at this
    rw [this, hUU', submatrix_one_equiv]
  · have h1 : (U.submatrix id e)ᴴ * t * U.submatrix id e = (Uᴴ * t * U).submatrix e e := by
      ext a b
      simp [Matrix.mul_apply]
    rw [h1, hD, submatrix_diagonal_equiv]
    ext (a | a) (b | b) <;> simp [diagonal_apply, he1, he2, one_apply]
    all_goals (split_ifs <;> simp)
end GlobalTheory
