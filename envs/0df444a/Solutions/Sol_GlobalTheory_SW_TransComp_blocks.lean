-- Prove2me | solution 1 for GlobalTheory.SW.TransComp.blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:31.220947+00:00
-- url     : https://prove2.me/submissions/1d7f19e5-131d-4438-9855-7d6714de513b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul

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
theorem _root_.solution {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ) :
    σ.toBlocks₂₁ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₁ᵀ * σ.toBlocks₂₁ = 0 ∧
      σ.toBlocks₂₂ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₂ᵀ * σ.toBlocks₂₁ = 1 := by
  have h' := h
  rw [← Matrix.fromBlocks_toBlocks σ] at h'
  obtain ⟨h1, -, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h'
  refine ⟨sub_eq_zero.2 h1.symm, ?_⟩

  have h4 := congrArg Matrix.transpose h3
  simpa [Matrix.transpose_sub, Matrix.transpose_mul] using h4
end GlobalTheory.SW.TransComp
