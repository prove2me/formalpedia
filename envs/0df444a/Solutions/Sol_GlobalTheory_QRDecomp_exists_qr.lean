-- Prove2me | solution 1 for GlobalTheory.QRDecomp.exists_qr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:52.103813+00:00
-- url     : https://prove2.me/submissions/c1ca680c-b004-4569-9be7-67d5d666b692

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsQr

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
open GlobalTheory GlobalTheory.QRDecomp
open Matrix
open scoped ComplexOrder
namespace GlobalTheory.QRDecomp
namespace _root_.GlobalTheory.QRDecomp
theorem _root_.solution (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    ∃ (Q : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ),
      Qᴴ * Q = 1 ∧ u.BlockTriangular id ∧ IsUnit u.det ∧ A = Q * u := by
  classical
  have hinj : Function.Injective A.mulVec := by
    intro v w h
    have h2 : (Aᴴ * A) *ᵥ v = (Aᴴ * A) *ᵥ w := by rw [← mulVec_mulVec, ← mulVec_mulVec, h]
    exact (mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hA)) h2
  have hS : (Aᴴ * A).PosDef := PosDef.conjTranspose_mul_self A hinj
  set L := LDL.lowerInv hS
  set d := LDL.diagEntries hS
  haveI : Invertible L := LDL.invertibleLowerInv hS
  have hLu : IsUnit L.det := isUnit_det_of_invertible L
  have hD : diagonal d = L * (Aᴴ * A) * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hDpos : (diagonal d).PosDef := by
    rw [hD]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hLu))
  have hd : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  have hdre : ∀ i, d i = ((d i).re : ℂ) ∧ 0 < (d i).re := fun i => by
    have h := hd i
    rw [Complex.pos_iff] at h
    exact ⟨Complex.ext (by simp) (by simp [h.2]), h.1⟩
  let r : Fin m → ℂ := fun i => ((Real.sqrt (d i).re : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    simp only [r, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (hdre i).2).ne'
  have hrr : ∀ i, star (r i) * r i = d i := fun i => by
    simp only [r, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hdre i).2.le, ← (hdre i).1]
  have hLt : Lᴴ.BlockTriangular id := fun i j hij => by
    have h : LDL.lowerInv hS j i = 0 := LDL.lowerInv_triangular hS hij
    simp [conjTranspose_apply, L, h]
  refine ⟨A * Lᴴ * diagonal (fun i => (r i)⁻¹), diagonal r * (Lᴴ)⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : (A * Lᴴ * diagonal fun i => (r i)⁻¹)ᴴ * (A * Lᴴ * diagonal fun i => (r i)⁻¹)
        = (diagonal fun i => star (r i)⁻¹) * (L * (Aᴴ * A) * Lᴴ) * diagonal fun i => (r i)⁻¹ := by
      simp only [conjTranspose_mul, diagonal_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rfl
    rw [h1, ← hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← hrr i]
    have h0 := hr0 i
    have h0' : star (r i) ≠ 0 := star_ne_zero.mpr h0
    rw [star_inv₀]
    field_simp
  · exact (blockTriangular_diagonal r).mul (blockTriangular_inv_of_blockTriangular hLt)
  · rw [det_mul, det_diagonal]
    exact (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hr0 i)).mul
      (isUnit_nonsing_inv_det _ (isUnit_det_of_invertible Lᴴ))
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have h1 : (fun i => (r i)⁻¹ * r i) = fun _ => (1 : ℂ) :=
      funext fun i => inv_mul_cancel₀ (hr0 i)
    rw [h1, diagonal_one, Matrix.one_mul, mul_inv_of_invertible, Matrix.mul_one]
end _root_.GlobalTheory.QRDecomp
end GlobalTheory.QRDecomp
