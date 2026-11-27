-- Prove2me | solution 1 for GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:43.707872+00:00
-- url     : https://prove2.me/submissions/15c451c4-b22a-4c11-a495-bc3fb936ab89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquivStatement
import Theorems.Thm_GlobalTheory_adicCompletion_tensor_quotient_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R] [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K], Function.Surjective (algebraMap R₀ R) → Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+* AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by
  first | exact @GlobalTheory.adicCompletion_tensor_quotient_ringEquiv | exact GlobalTheory.adicCompletion_tensor_quotient_ringEquiv | (intros; apply GlobalTheory.adicCompletion_tensor_quotient_ringEquiv <;> assumption)
end _root_.GlobalTheory.T
