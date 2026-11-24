-- Prove2me | solution 1 for GlobalTheory.SW.TransComp.mul_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:29:37.795296+00:00
-- url     : https://prove2.me/submissions/1709aea7-0db2-48d2-bd43-b91ba2d68277

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
theorem _root_.solution (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply,
    Fintype.sum_sum_type]
end GlobalTheory.SW.TransComp
