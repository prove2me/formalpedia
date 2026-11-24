-- Prove2me | solution 1 for GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:58.193561+00:00
-- url     : https://prove2.me/submissions/8bde1c14-2451-474b-b705-0452361e119c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensorStatement
import Theorems.Thm_GlobalTheory_isRegularLocalRing_atPrime_localization_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  first | exact @GlobalTheory.isRegularLocalRing_atPrime_localization_tensor | exact GlobalTheory.isRegularLocalRing_atPrime_localization_tensor | (intros; apply GlobalTheory.isRegularLocalRing_atPrime_localization_tensor <;> assumption)
end _root_.GlobalTheory.T
