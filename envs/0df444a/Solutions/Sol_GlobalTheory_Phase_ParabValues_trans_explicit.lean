-- Prove2me | solution 1 for GlobalTheory.Phase.ParabValues.trans_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:01:13.168353+00:00
-- url     : https://prove2.me/submissions/13571a40-b824-4828-a213-1fcffecdd430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhase
import Theorems.Thm_GlobalTheory_SW_LinChange_haar_mul
import Theorems.Thm_GlobalTheory_SW_Parab_isSB_parChar_mul
import Theorems.Thm_GlobalTheory_SW_Parab_qv_bilin
import Theorems.Thm_GlobalTheory_SW_Parab_qv_row_mul
import Theorems.Thm_GlobalTheory_SW_isSB_algebra_haar_linear
import Theorems.Thm_P2M_GlobalTheory_SW_Parab_qm_mul__cae64bfa856c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ParabValues
open GlobalTheory.SW.Parab
namespace GlobalTheory.Phase.ParabValues
theorem _root_.solution (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hC : σ.toBlocks₂₁ = 0)
    (φ : Matrix κ ι ℚ → ℂ) (hφ : IsSB φ) :
    IsSB (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) ∧
    TransS σ φ (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) := by
  classical
  set A := σ.toBlocks₁₁ with hA
  set B := σ.toBlocks₁₂ with hB
  set D := σ.toBlocks₂₂ with hD
  have hDA : D * Aᵀ = 1 := by
    have h := SymplecticGroup.mem_iff.mp hσ
    rw [← Matrix.fromBlocks_toBlocks σ, hC, Matrix.J, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
    have := congrArg Matrix.toBlocks₂₁ h
    simpa using this
  have hdet : D.det * A.det = 1 := by
    have := congrArg Matrix.det hDA
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hA0 : A.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA0
  refine ⟨?_, ?_⟩
  · have h1 := isSB_parChar_mul (B * Aᵀ) _
      ((GlobalTheory.SW.LinChange.haar_mul ℚ κ ι φ hφ).1 A hA0).1
    exact (GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ h1 h1).2.1 _
  · intro τ _ ζ
    have hden : spDen σ τ = qm D := by
      unfold spDen
      rw [hC]
      have : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
      rw [this, Matrix.zero_mul, zero_add]
    have hinv : (qm D)⁻¹ = (qm A)ᵀ := by
      apply Matrix.inv_eq_right_inv
      have e : (qm A)ᵀ = qm Aᵀ := rfl
      rw [e, ← qm_mul', hDA]
      ext i j; by_cases h : i = j <;> simp [qm, Matrix.one_apply, h]
    have hdetD : (qm D).det = (D.det : ℂ) := ((Rat.castHom ℂ).map_det D).symm
    have hC' : qm σ.toBlocks₂₁ = 0 := by rw [hC]; ext i j; simp [qm]
    unfold spAct
    rw [hden, hinv, hC', hdetD]
    simp only [Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero, Finset.sum_const_zero,
      mul_zero, Complex.exp_zero, mul_one]
    let e : Matrix κ ι ℚ ≃ Matrix κ ι ℚ :=
      { toFun := fun x => x * A
        invFun := fun x => x * A⁻¹
        left_inv := fun x => Matrix.mul_nonsing_inv_cancel_right A x hAu
        right_inv := fun x => Matrix.nonsing_inv_mul_cancel_right A x hAu }
    unfold thS
    rw [← tsum_mul_left, ← e.tsum_eq (fun x => _ * (φ x * _))]
    refine tsum_congr fun x => ?_
    show ((D.det : ℂ) ^ (Fintype.card κ / 2)) * (parChar (B * Aᵀ) x * φ (x * A)) * _ =
      _ * (φ (x * A) * cexp (Real.pi * I * ∑ k, (qv ((x * A) k) ⬝ᵥ τ *ᵥ qv ((x * A) k) +
        2 * (qv ((x * A) k) ⬝ᵥ ζ k))))
    rw [mul_assoc, mul_comm (parChar _ _), mul_assoc]
    congr 2
    unfold parChar
    rw [← Complex.exp_add]
    congr 1
    rw [← mul_neg, ← mul_add, Rat.cast_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [qv_bilin, qv_row_mul, qm_mul']
    have e1 : qm Aᵀ = (qm A)ᵀ := rfl
    beta_reduce
    rw [e1, Matrix.add_mul, Matrix.add_mulVec, dotProduct_add, Matrix.vecMul_transpose,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_transpose, Matrix.dotProduct_mulVec (qv (x k)) (qm A),
      Matrix.dotProduct_mulVec (qv (x k)) (qm A)]
    ring
end GlobalTheory.Phase.ParabValues
