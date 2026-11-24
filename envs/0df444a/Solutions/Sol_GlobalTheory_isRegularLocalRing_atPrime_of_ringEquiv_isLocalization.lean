-- Prove2me | solution 1 for GlobalTheory.isRegularLocalRing_atPrime_of_ringEquiv_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:12.443547+00:00
-- url     : https://prove2.me/submissions/2c5cfca0-4a01-45cc-bf04-8d08190127ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensor

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {B T T' : Type} [CommRing B]
    [IsRegularRing B] [CommRing T] [CommRing T'] [Algebra B T'] (M : Submonoid B)
    [IsLocalization M T'] (e : T ≃+* T') (𝔫 : Ideal T) [𝔫.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  letI : Algebra B T := ((e.symm : T' →+* T).comp (algebraMap B T')).toAlgebra
  let e' : T' ≃ₐ[B] T := AlgEquiv.ofRingEquiv (f := e.symm) (fun x => rfl)
  haveI : IsLocalization M T := IsLocalization.isLocalization_of_algEquiv M e'
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔫) (𝔫.comap (algebraMap B T)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔫) 𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime (𝔫.comap (algebraMap B T))) :=
    IsRegularRing.isRegularLocalRing_localization _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (𝔫.comap (algebraMap B T)).primeCompl
      (Localization.AtPrime (𝔫.comap (algebraMap B T))) (Localization.AtPrime 𝔫)).toRingEquiv
end GlobalTheory
