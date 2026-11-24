-- Prove2me | solution 1 for GlobalTheory.SW.transS_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:41:20.681805+00:00
-- url     : https://prove2.me/submissions/7c49bffa-8c8b-49f8-a0e6-78638abd86a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
import Theorems.Thm_GlobalTheory_SW_TransComp_qm_mul
import Theorems.Thm_GlobalTheory_SW_TransComp_qm_add
import Theorems.Thm_GlobalTheory_SW_TransComp_mul_block
import Theorems.Thm_GlobalTheory_SW_TransComp_key
import Theorems.Thm_GlobalTheory_SiegelAction_qm_add
import Theorems.Thm_GlobalTheory_SiegelAction_qm_mul
import Theorems.Thm_GlobalTheory_T_symplecticSiegelAction_mem_upperHalfSpace_and_cocycle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory.SW.TransComp
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → σ' ∈ Matrix.symplecticGroup ι ℚ → ∀ φ ψ χ : Matrix κ ι ℚ → ℂ, TransS σ φ ψ → TransS σ' ψ χ → TransS (σ' * σ) φ χ := by
  intro κ ι _ _ _ σ σ' hσ hσ' φ ψ χ h1 h2 τ hτ ζ
  obtain ⟨hd, hmem, -, -, hcomp⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ τ hτ
  obtain ⟨hden, hact⟩ := hcomp σ' hσ'
  have hd' := (GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ' hσ' _ hmem).1
  rw [hden, hact]

  have hk := key hσ hτ.1 hd hmem.1
  have hD' : qm σ'.toBlocks₂₂ = spDen σ' (spAct σ τ) - qm σ'.toBlocks₂₁ * spAct σ τ := by
    rw [spDen, add_sub_cancel_left]
  have hinv' : (spDen σ' (spAct σ τ))⁻¹ * spDen σ' (spAct σ τ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd')

  have hM : (spDen σ τ)⁻¹ * ((spDen σ' (spAct σ τ))⁻¹ * qm σ'.toBlocks₂₁) * ((spDen σ τ)⁻¹)ᵀ +
      (spDen σ τ)⁻¹ * qm σ.toBlocks₂₁ =
      (spDen σ' (spAct σ τ) * spDen σ τ)⁻¹ * qm (σ' * σ).toBlocks₂₁ := by
    rw [mul_block, qm_add, qm_mul, qm_mul, hk, hD', Matrix.mul_inv_rev]
    have inner : qm σ'.toBlocks₂₁ * (spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ) +
        (spDen σ' (spAct σ τ) - qm σ'.toBlocks₂₁ * spAct σ τ) * qm σ.toBlocks₂₁ =
        qm σ'.toBlocks₂₁ * ((spDen σ τ)⁻¹)ᵀ + spDen σ' (spAct σ τ) * qm σ.toBlocks₂₁ := by
      noncomm_ring
    rw [inner, Matrix.mul_add, Matrix.mul_assoc (spDen σ τ)⁻¹ (spDen σ' (spAct σ τ))⁻¹,
      Matrix.mul_assoc (spDen σ τ)⁻¹ (spDen σ' (spAct σ τ))⁻¹, ← Matrix.mul_assoc
      (spDen σ' (spAct σ τ))⁻¹ (spDen σ' (spAct σ τ)), hinv', Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  have hq : ∀ v : ι → ℂ, v ⬝ᵥ ((spDen σ' (spAct σ τ) * spDen σ τ)⁻¹ * qm (σ' * σ).toBlocks₂₁) *ᵥ v =
      (v ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spDen σ' (spAct σ τ))⁻¹ * qm σ'.toBlocks₂₁) *ᵥ (v ᵥ* (spDen σ τ)⁻¹) +
        v ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ v := by
    intro v
    rw [← hM, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hfun : (fun k => ζ k ᵥ* (spDen σ' (spAct σ τ) * spDen σ τ)⁻¹) =
      fun k => (ζ k ᵥ* (spDen σ τ)⁻¹) ᵥ* (spDen σ' (spAct σ τ))⁻¹ := by
    funext k
    rw [Matrix.mul_inv_rev, Matrix.vecMul_vecMul]
  rw [hfun, h2 _ hmem, h1 τ hτ ζ, Matrix.det_mul, mul_pow]
  simp only [hq, Finset.sum_add_distrib, mul_add, Complex.exp_add]
  ring
end GlobalTheory.SW
