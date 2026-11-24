-- Prove2me | solution 1 for GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:29.463261+00:00
-- url     : https://prove2.me/submissions/e1afe69e-32fd-4f01-ac4c-1b0a3b1e4aa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.CayleyRat
namespace GlobalTheory.CayleyRat
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  intro L _ _ _ n S hS hdet
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  set T : Matrix (Fin n) (Fin n) L := 1 - S with hT
  set U : Matrix (Fin n) (Fin n) L := 1 + S with hU
  have hSc : conjT c S = -S := by
    unfold conjT; exact (neg_eq_of_add_eq_zero_right hS).symm
  have hcT : conjT c T = U := by
    have : conjT c T = conjT c 1 - conjT c S := by
      simp [conjT, hT, Matrix.map_sub, Matrix.transpose_sub]
    rw [this, conjT_one, hSc, hU, sub_neg_eq_add]
  have hcU : conjT c U = T := by
    have : conjT c U = conjT c 1 + conjT c S := by
      simp [conjT, hU, Matrix.map_add, Matrix.transpose_add]
    rw [this, conjT_one, hSc, hT, sub_eq_add_neg]
  have hdetU : U.det ≠ 0 := by
    have : U.det = c T.det := by
      rw [← hcT, conjT, Matrix.det_transpose, RingHom.map_det]; rfl
    rw [this]; exact (map_ne_zero c).mpr hdet
  have huT : IsUnit T.det := isUnit_iff_ne_zero.mpr hdet
  have huU : IsUnit U.det := isUnit_iff_ne_zero.mpr hdetU
  have hcTinv : conjT c T⁻¹ = U⁻¹ := by
    have h1 : U * conjT c T⁻¹ = 1 := by
      rw [← hcT, ← conjT_mul, Matrix.nonsing_inv_mul _ huT, conjT_one]
    exact (Matrix.inv_eq_right_inv h1).symm
  have hcomm : U * T = T * U := by
    simp [hU, hT, mul_sub, sub_mul, mul_add, add_mul]; abel
  have hinv : T⁻¹ * U⁻¹ = U⁻¹ * T⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hcomm]
  have hdetγ : IsUnit (U * T⁻¹).det := by
    rw [Matrix.det_mul]; exact huU.mul (Matrix.isUnit_nonsing_inv_det T huT)
  refine ⟨Matrix.nonsingInvUnit (U * T⁻¹) hdetγ, ?_, rfl⟩
  show (U * T⁻¹) * conjT c (U * T⁻¹) = 1
  rw [conjT_mul, hcTinv, hcU, Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹, hinv, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huU, Matrix.one_mul, Matrix.nonsing_inv_mul _ huT]
end GlobalTheory.CayleyRat
