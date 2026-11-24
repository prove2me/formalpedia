-- Prove2me | solution 1 for GlobalTheory.KSp.exists_herm_transverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:14.229846+00:00
-- url     : https://prove2.me/submissions/03a769ea-17b0-48fa-88e3-314f2514b8ba

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertible
import Theorems.Thm_GlobalTheory_KSp_transv_field

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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)),
    ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  intro F _ _ E _ _ c δ hE ν _ _ g
  have hδ : δ ≠ 0 := hE.unit.ne_zero
  set M := mat c g with hMdef
  set cc := M.toBlocks₂₁
  set dd := M.toBlocks₂₂
  have hU := (mem_UG_iff c _).mp g.2
  change M * stdJ ν E * (M.map c)ᵀ = stdJ ν E at hU
  have key : cc * (dd.map c)ᵀ = dd * (cc.map c)ᵀ := by
    have h := congrArg Matrix.toBlocks₂₂ hU
    rw [← fromBlocks_toBlocks M] at h
    simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h
    have h' : cc * (dd.map c)ᵀ + -(dd * (cc.map c)ᵀ) = 0 := by rw [← h]; abel
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h')

  set S : Matrix ν ν E := δ • (1 : Matrix ν ν E)
  have hcδ : c δ = -δ := hE.anti
  have hSu : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]; simp [S, Matrix.det_smul, hδ]
  have hS : Sᵀ = -S.map (c : E →+* E) := by
    ext i j; by_cases h : i = j <;> simp [S, Matrix.one_apply, h, hcδ, eq_comm]
  have hmapC : (δ • ddᵀ).map (c : E →+* E) = (-δ) • (dd.map c)ᵀ := by
    ext i j; simp [hcδ]
  have hiso : (ccᵀ)ᵀ * S * (δ • ddᵀ).map (c : E →+* E) + (δ • ddᵀ)ᵀ * S * (ccᵀ).map (c : E →+* E) = 0 := by
    rw [hmapC]
    have e1 : (ccᵀ).map (c : E →+* E) = (cc.map c)ᵀ := rfl
    rw [e1]
    simp only [S, transpose_transpose, transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, key]
    rw [← add_smul]; simp
  have hinj : ∀ u : ν → E, ccᵀ *ᵥ u = 0 → (δ • ddᵀ) *ᵥ u = 0 → u = 0 := by
    intro u h1 h2
    rw [mulVec_transpose] at h1
    rw [smul_mulVec, mulVec_transpose, smul_eq_zero] at h2
    have h2' : u ᵥ* dd = 0 := h2.resolve_left hδ
    have hw : (Sum.elim 0 u : ν ⊕ ν → E) ᵥ* M = 0 := by
      rw [← fromBlocks_toBlocks M]
      funext i
      rcases i with i | i
      · have := congrFun h1 i
        simpa [vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, cc] using this
      · have := congrFun h2' i
        simpa [vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, dd] using this
    have hinv : M * ((g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = 1 := by
      change (((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
      rw [mul_inv_cancel]; rfl
    have hw0 : (Sum.elim 0 u : ν ⊕ ν → E) = 0 := by
      rw [← vecMul_one (Sum.elim 0 u : ν ⊕ ν → E), ← hinv, ← vecMul_vecMul, hw, zero_vecMul]
    funext i
    simpa using congrFun hw0 (Sum.inr i)
  obtain ⟨X, hX, hdet⟩ := transv_field (c : E →+* E) S hSu hS ccᵀ (δ • ddᵀ) hinj hiso
  refine ⟨δ • Xᵀ, ?_, ?_⟩
  · have hX' : δ • Xᵀ + δ • X.map (c : E →+* E) = 0 := by
      simpa [S, Matrix.mul_smul, Matrix.smul_mul] using hX
    rw [← smul_add, smul_eq_zero] at hX'
    have hX'' : X.map (c : E →+* E) = -Xᵀ := eq_neg_of_add_eq_zero_right (hX'.resolve_left hδ)
    have e : (δ • Xᵀ).map c = (-δ) • (X.map (c : E →+* E))ᵀ := by ext i j; simp [hcδ]
    rw [e, hX'']
    simp
  · have e : (ccᵀ + X * (δ • ddᵀ))ᵀ = cc + dd * (δ • Xᵀ) := by
      simp [transpose_add, transpose_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [← e, det_transpose]
    exact (isUnit_iff_ne_zero).mp hdet
end GlobalTheory.KSp
