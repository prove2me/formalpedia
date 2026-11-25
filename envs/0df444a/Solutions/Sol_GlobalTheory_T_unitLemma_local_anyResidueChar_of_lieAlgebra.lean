-- Prove2me | solution 1 for GlobalTheory.T.unitLemma_local_anyResidueChar_of_lieAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:45.215658+00:00
-- url     : https://prove2.me/submissions/aa3cfb5e-ed3b-4848-b98b-4d485d0ed9e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaLocalAnyResidueCharOfLieAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaLocalAnyResidueCharOfLieAlgebraStatement
import Theorems.Thm_GlobalTheory_UnitLemma_UnrAny_unitLemma_local_of_lie_any


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any | exact GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any | (intros; apply GlobalTheory.UnitLemma.UnrAny.unitLemma_local_of_lie_any <;> assumption)
end _root_.GlobalTheory.T
