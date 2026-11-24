-- Prove2me | solution 1 for GlobalTheory.T.not_isField_adicCompletion_tensor_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:41.18763+00:00
-- url     : https://prove2.me/submissions/3627df45-24b2-4aad-ad76-b89a50364761

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NotIsFieldAdicCompletionTensorOfSplit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NotIsFieldAdicCompletionTensorOfSplitStatement
import Theorems.Thm_GlobalTheory_SplitPlace_not_isField_of_split


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.primesOver (𝓞 E)).ncard = 2 → ¬ IsField (v.adicCompletion F ⊗[F] E) := by
  first | exact @GlobalTheory.SplitPlace.not_isField_of_split | exact GlobalTheory.SplitPlace.not_isField_of_split | (intros; apply GlobalTheory.SplitPlace.not_isField_of_split <;> assumption)
end _root_.GlobalTheory.T
