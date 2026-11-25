-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.exists_gaussian_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:40:38.438194+00:00
-- url     : https://prove2.me/submissions/ba070940-1a5d-4d48-9481-eaac9005c7b9

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck
namespace GlobalTheory.CyclicNormCheck
theorem _root_.solution : ∃ (E : Type) (_ : Field E) (_ : NumberField E),
    IsCyclotomicExtension {4} ℚ E :=
  ⟨CyclotomicField 4 ℚ, inferInstance, inferInstance, CyclotomicField.isCyclotomicExtension 4 ℚ⟩
end GlobalTheory.CyclicNormCheck
