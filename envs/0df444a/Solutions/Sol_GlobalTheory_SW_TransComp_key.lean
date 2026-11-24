-- Prove2me | solution 1 for GlobalTheory.SW.TransComp.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:09.043031+00:00
-- url     : https://prove2.me/submissions/7cad0733-a25d-412f-800b-f6d7797cc7c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
import Theorems.Thm_GlobalTheory_SW_TransComp_qm_mul
import Theorems.Thm_GlobalTheory_SW_TransComp_qm_sub
import Theorems.Thm_GlobalTheory_SW_TransComp_qm_transpose
import Theorems.Thm_GlobalTheory_SW_TransComp_qm_zero
import Theorems.Thm_GlobalTheory_SW_TransComp_qm_one
import Theorems.Thm_GlobalTheory_SW_TransComp_blocks
import Theorems.Thm_GlobalTheory_SiegelAction_qm_mul


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TransComp
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SW.TransComp
theorem _root_.solution {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ)
    {τ : Matrix ι ι ℂ} (hτ : τ.IsSymm) (hd : (spDen σ τ).det ≠ 0) (hs : (spAct σ τ).IsSymm) :
    qm σ.toBlocks₁₁ = spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ := by
  have hu : IsUnit (spDen σ τ).det := isUnit_iff_ne_zero.mpr hd

  have h1 : (spDen σ τ)ᵀ * spAct σ τ = (qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂)ᵀ := by
    have hs' : (spAct σ τ)ᵀ = spAct σ τ := hs
    rw [← hs']
    unfold spAct
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.one_mul]
  have hτ' : τᵀ = τ := hτ
  obtain ⟨b1, b2⟩ := blocks h
  have e1 := congrArg qm b1
  have e2 := congrArg qm b2
  rw [qm_sub, qm_mul, qm_mul, qm_transpose, qm_transpose, qm_zero] at e1
  rw [qm_sub, qm_mul, qm_mul, qm_transpose, qm_transpose, qm_one] at e2
  have h2 : (spDen σ τ)ᵀ * (qm σ.toBlocks₁₁ - spAct σ τ * qm σ.toBlocks₂₁) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h1]
    unfold spDen
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      hτ']
    calc (τ * (qm σ.toBlocks₂₁)ᵀ + (qm σ.toBlocks₂₂)ᵀ) * qm σ.toBlocks₁₁ -
          (τ * (qm σ.toBlocks₁₁)ᵀ + (qm σ.toBlocks₁₂)ᵀ) * qm σ.toBlocks₂₁
        = τ * ((qm σ.toBlocks₂₁)ᵀ * qm σ.toBlocks₁₁ - (qm σ.toBlocks₁₁)ᵀ * qm σ.toBlocks₂₁) +
          ((qm σ.toBlocks₂₂)ᵀ * qm σ.toBlocks₁₁ - (qm σ.toBlocks₁₂)ᵀ * qm σ.toBlocks₂₁) := by
          noncomm_ring
      _ = 1 := by rw [e1, e2, Matrix.mul_zero, zero_add]
  rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv h2]
  abel
end GlobalTheory.SW.TransComp
