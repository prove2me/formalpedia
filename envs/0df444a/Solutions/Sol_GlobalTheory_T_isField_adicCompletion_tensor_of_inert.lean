-- Prove2me | solution 1 for GlobalTheory.T.isField_adicCompletion_tensor_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:04.955166+00:00
-- url     : https://prove2.me/submissions/b0311fed-cdcb-4404-8dd7-e97f849b7fdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInertStatement
import Theorems.Thm_GlobalTheory_InertField_isField_of_inert


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime → IsField (v.adicCompletion F ⊗[F] E) := by
  first | exact @GlobalTheory.InertField.isField_of_inert | exact GlobalTheory.InertField.isField_of_inert | (intros; apply GlobalTheory.InertField.isField_of_inert <;> assumption)
end _root_.GlobalTheory.T
