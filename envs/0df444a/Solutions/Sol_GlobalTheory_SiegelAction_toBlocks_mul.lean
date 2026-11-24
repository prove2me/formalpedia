-- Prove2me | solution 1 for GlobalTheory.SiegelAction.toBlocks_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:16.313235+00:00
-- url     : https://prove2.me/submissions/aa43c83f-33d5-4954-9ae9-d410c4fe1765

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl

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
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution (σ' σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₁₁ = σ'.toBlocks₁₁ * σ.toBlocks₁₁ + σ'.toBlocks₁₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₁₂ = σ'.toBlocks₁₁ * σ.toBlocks₁₂ + σ'.toBlocks₁₂ * σ.toBlocks₂₂ ∧
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₂₂ = σ'.toBlocks₂₁ * σ.toBlocks₁₂ + σ'.toBlocks₂₂ * σ.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]
end GlobalTheory.SiegelAction
