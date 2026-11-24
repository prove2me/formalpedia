-- Prove2me | solution 1 for GlobalTheory.KSp.exists_gl_diagonal_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:24:42.465355+00:00
-- url     : https://prove2.me/submissions/482c6fcd-2014-481e-b86a-ec42f4ce36e9

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGLDiagonalCongruentHermitian
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_of_fixed
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  intro F _ _ E _ _ c δ hE ν _ _ b hb hdet
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hG : ∀ x y, (c : E →+* E) (b x y) = b y x := by
    intro x y
    have := congrFun (congrFun hb y) x
    simpa using this
  obtain ⟨P, d, hP, hPd, hfix, hne⟩ :=
    GlobalTheory.HermDiag.exists_congr_diagonal (c := (c : E →+* E)) h2 (fun t => hE.invol t) (G := b) hG
  have hd0 := hne hdet
  have hPd' : Pᵀ * b * P.map c = diagonal d := hPd
  choose f hf using fun i => hE.exists_of_fixed (hfix i)
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h; apply hd0 i; rw [hf i, h, map_zero]
  have hQ : (Pᵀ).det ≠ 0 := by rwa [det_transpose]
  set A : Matrix ν ν E := (Pᵀ)⁻¹ with hA
  have hAQ : A * Pᵀ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQ)
  have hQA : Pᵀ * A = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ)
  have hAs : (A.map c)ᵀ * P.map c = 1 := by
    have h1 : (Pᵀ * A).map c = 1 := by rw [hQA]; exact Matrix.map_one _ (map_zero c) (map_one c)
    rw [show (Pᵀ * A).map c = (Pᵀ).map c * A.map c from Matrix.map_mul (f := c.toRingHom)] at h1
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    simpa [Matrix.transpose_map] using h3
  have hAs' : P.map c * (A.map c)ᵀ = 1 := mul_eq_one_comm.mp hAs
  have hAdet : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAQ
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet, fun j => Units.mk0 (f j) (hf0 j), ?_⟩
  have hD : diagonal (fun j => algebraMap F E ((Units.mk0 (f j) (hf0 j) : Fˣ) : F)) = diagonal d := by
    congr 1; funext j; simp [hf j]
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  rw [hD, ← hPd']
  calc b = (A * Pᵀ) * b * (P.map c * (A.map c)ᵀ) := by rw [hAQ, hAs', Matrix.one_mul, Matrix.mul_one]
    _ = A * (Pᵀ * b * P.map c) * (A.map c)ᵀ := by simp only [Matrix.mul_assoc]
end GlobalTheory.KSp
