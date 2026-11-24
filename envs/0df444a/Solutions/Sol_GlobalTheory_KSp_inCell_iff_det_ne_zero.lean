-- Prove2me | solution 1 for GlobalTheory.KSp.inCell_iff_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:26:01.631062+00:00
-- url     : https://prove2.me/submissions/db42b3b0-3cf5-4996-8b5e-e5a9a078edca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InCellIffDetNeZero
import Theorems.Thm_GlobalTheory_KSp_mem_sieg


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)),
    InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  intro F _ _ E _ _ c δ hE ν _ _ g
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    have hdet : ∀ x : UG c (stdJ ν E), (mat c x).det ≠ 0 := fun x =>
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (x : GL (ν ⊕ ν) E))).ne_zero
    have hp0 : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0 (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hp, fromBlocks_toBlocks]
    have hq0 : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0 (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hq, fromBlocks_toBlocks]
    have hpd := hdet p
    have hqd := hdet q
    rw [hp0, det_fromBlocks_zero₂₁] at hpd
    rw [hq0, det_fromBlocks_zero₂₁] at hqd
    change (mat c p * stdJ ν E * mat c q).toBlocks₂₁.det ≠ 0
    rw [hp0, hq0]
    simp only [stdJ, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [det_neg, det_mul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (mul_ne_zero (right_ne_zero_of_mul hpd) (left_ne_zero_of_mul hqd))
  · intro hC
    set A := (mat c g).toBlocks₁₁ with hA
    set B := (mat c g).toBlocks₁₂ with hB
    set C := (mat c g).toBlocks₂₁ with hCdef
    set D := (mat c g).toBlocks₂₂ with hD
    have hg0 : mat c g = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    have hrel : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
    have hkey : C * (D.map c)ᵀ = D * (C.map c)ᵀ := by
      have h := congrArg Matrix.toBlocks₂₂ hrel
      rw [hg0] at h
      simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
      simp at h
      exact (neg_add_eq_zero.1 h).symm
    have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hC)
    have hCs : IsUnit (C.map c)ᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, det_transpose]
      exact (hCu.map (RingHom.mapMatrix (c : E →+* E))).map detMonoidHom
    have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hC)
    set v := C⁻¹ * D with hv
    have hvh : (v.map c)ᵀ = v := by
      apply hCu.mul_left_cancel
      apply hCs.mul_right_cancel
      have e1 : ((v.map c)ᵀ) * (C.map c)ᵀ = (D.map c)ᵀ := by
        rw [hv, Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← transpose_mul, ← Matrix.map_mul, hCC,
          Matrix.map_one _ (map_zero c) (map_one c), transpose_one, Matrix.mul_one]
      rw [Matrix.mul_assoc, e1, hkey, hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    let q := unip c v hvh
    have hq : q ∈ sieg c ν := by
      change (fromBlocks (1 : Matrix ν ν E) v 0 1).toBlocks₂₁ = 0
      rw [toBlocks_fromBlocks₂₁]
    refine ⟨g * q⁻¹ * (weyl c ν)⁻¹, ?_, q, hq, by group⟩
    rw [mem_sieg]
    change (mat c g * fromBlocks 1 (-v) 0 1 * -stdJ ν E).toBlocks₂₁ = 0
    rw [hg0]
    simp only [stdJ, fromBlocks_neg, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul, neg_add_cancel]
end GlobalTheory.KSp
