-- Prove2me | solution 1 for GlobalTheory.PrimeElement.isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:04.022094+00:00
-- url     : https://prove2.me/submissions/9471e657-d7d0-44b9-bf78-eb024069764b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Theorems.Thm_GlobalTheory_PrimeElement_maximalIdeal_eq_span
import Theorems.Thm_GlobalTheory_PrimeElement_algebraMap_atPrime_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
variable [(Ideal.span {π}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S (Ideal.span {π})]
namespace GlobalTheory.PrimeElement
theorem _root_.solution [IsDomain R] [IsNoetherianRing R] [IsDomain S] (hπ : π ≠ 0) :
    IsDiscreteValuationRing S := by
  have := IsLocalization.AtPrime.isLocalRing S (Ideal.span {π})
  have : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (Ideal.span {π}).primeCompl S inferInstance
  have hne : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_atPrime_injective (π := π) S)).2 hπ
  have hf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, maximalIdeal_eq_span (π := π) S, Ideal.span_singleton_eq_bot]
    exact hne
  refine ((IsDiscreteValuationRing.TFAE S hf).out 0 4).2 ?_
  exact ⟨⟨_, maximalIdeal_eq_span (π := π) S⟩⟩
end GlobalTheory.PrimeElement
