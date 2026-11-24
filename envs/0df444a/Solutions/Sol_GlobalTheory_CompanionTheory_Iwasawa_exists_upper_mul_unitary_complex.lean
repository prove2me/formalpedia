-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwasawa.exists_upper_mul_unitary_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:19.267331+00:00
-- url     : https://prove2.me/submissions/81cccb5b-2a2e-486c-8730-99b1a0c7a521

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_exists_cholesky


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwasawa
namespace GlobalTheory.CompanionTheory.Iwasawa
theorem _root_.solution {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y) :
    ∃ B R K : Matrix (Fin n) (Fin n) ℂ, B.IsUpperTriangular ∧ B * R = 1 ∧ R * B = 1 ∧
      K * Kᴴ = 1 ∧ Kᴴ * K = 1 ∧ Y = B * K := by
  let e : Fin n ≃ Fin n := Fin.revPerm
  have hYd : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY).ne_zero
  set Y' : Matrix (Fin n) (Fin n) ℂ := Y.submatrix e e with hY'
  have hY'u : IsUnit Y' := by
    rw [Matrix.isUnit_iff_isUnit_det, hY', Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det Y).mp hY
  have hpd : (Y' * Y'ᴴ).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self Y' (Matrix.vecMul_injective_iff_isUnit.mpr hY'u)
  obtain ⟨C, a, hCu, -, -, hC⟩ := CompanionTheory.D.gk.admitted.CholeskyDecomposition.exists_cholesky hpd
  have hBu : (Cᴴ.submatrix e e).IsUpperTriangular := by
    intro i j hij
    have h0 : C (e j) (e i) = 0 := hCu (Fin.rev_lt_rev.mpr hij)
    simp only [Matrix.submatrix_apply, Matrix.conjTranspose_apply]
    rw [h0, star_zero]
  have hBB : Cᴴ.submatrix e e * (Cᴴ.submatrix e e)ᴴ = Y * Yᴴ := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose, Matrix.submatrix_mul_equiv, hC,
      hY', Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix]
    have hee : (e : Fin n → Fin n) ∘ e = id := funext fun i => Fin.rev_rev i
    rw [hee, Matrix.submatrix_id_id]
  have hBd : (Cᴴ.submatrix e e).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBB
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, Matrix.det_conjTranspose] at this
    exact mul_ne_zero hYd (star_ne_zero.mpr hYd) this.symm
  set B := Cᴴ.submatrix e e with hBdef
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hBd)
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hBd)
  have hKK : (B⁻¹ * Y) * (B⁻¹ * Y)ᴴ = 1 := by
    calc (B⁻¹ * Y) * (B⁻¹ * Y)ᴴ = B⁻¹ * (Y * Yᴴ) * B⁻¹ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * Bᴴ) * B⁻¹ᴴ := by rw [hBB]
      _ = (B⁻¹ * B) * (B⁻¹ * B)ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBi, Matrix.conjTranspose_one, Matrix.mul_one]
  refine ⟨B, B⁻¹, B⁻¹ * Y, hBu, hBi', hBi, hKK, mul_eq_one_comm.mp hKK, ?_⟩
  rw [← Matrix.mul_assoc, hBi', Matrix.one_mul]
end GlobalTheory.CompanionTheory.Iwasawa
