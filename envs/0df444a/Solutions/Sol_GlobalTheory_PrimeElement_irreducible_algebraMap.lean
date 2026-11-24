-- Prove2me | solution 1 for GlobalTheory.PrimeElement.irreducible_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:23.176805+00:00
-- url     : https://prove2.me/submissions/ab93081e-5420-4fe4-b347-e60685e8c7c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Theorems.Thm_GlobalTheory_PrimeElement_maximalIdeal_eq_span
import Theorems.Thm_GlobalTheory_PrimeElement_isDomain_atPrime
import Theorems.Thm_GlobalTheory_PrimeElement_isDiscreteValuationRing

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
theorem _root_.solution [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    Irreducible (algebraMap R S π) := by
  have := isDomain_atPrime (π := π) S
  have := isDiscreteValuationRing (π := π) S hπ
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (maximalIdeal_eq_span S)
end GlobalTheory.PrimeElement
