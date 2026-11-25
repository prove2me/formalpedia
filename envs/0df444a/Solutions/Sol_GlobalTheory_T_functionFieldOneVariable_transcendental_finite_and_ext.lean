-- Prove2me | solution 1 for GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:32.472262+00:00
-- url     : https://prove2.me/submissions/3dd6ee3f-8a8b-4e18-b5f8-1b15de596a06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndE
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Theorems.Thm_GlobalTheory_Nef_isFF_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F → (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧ ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  first | exact @GlobalTheory.Nef.isFF_main | exact GlobalTheory.Nef.isFF_main | (intros; apply GlobalTheory.Nef.isFF_main <;> assumption)
end _root_.GlobalTheory.T
