-- Prove2me | solution 1 for GlobalTheory.T.siegelThetaTransformationLaw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:59.069669+00:00
-- url     : https://prove2.me/submissions/c6678a9b-afad-4230-969e-753bc9f91f98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMulStatement
import Theorems.Thm_GlobalTheory_SW_transS_comp


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → σ' ∈ Matrix.symplecticGroup ι ℚ → ∀ φ ψ χ : Matrix κ ι ℚ → ℂ, TransS σ φ ψ → TransS σ' ψ χ → TransS (σ' * σ) φ χ := by
  first | exact @GlobalTheory.SW.transS_comp | exact GlobalTheory.SW.transS_comp | (intros; apply GlobalTheory.SW.transS_comp <;> assumption)
end _root_.GlobalTheory.T
