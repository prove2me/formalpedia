-- Prove2me | solution 1 for GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:05.816802+00:00
-- url     : https://prove2.me/submissions/ea8f47ca-951a-44c8-9011-cc5249897760

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProdStatement
import Theorems.Thm_GlobalTheory_CompletionFactor_exists_ringEquiv_completion_prod


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
theorem _root_.solution : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by
  first | exact @GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod | exact GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod | (intros; apply GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod <;> assumption)
end _root_.GlobalTheory.T
