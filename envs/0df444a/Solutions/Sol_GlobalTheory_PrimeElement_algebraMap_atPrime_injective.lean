-- Prove2me | solution 1 for GlobalTheory.PrimeElement.algebraMap_atPrime_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:32.24885+00:00
-- url     : https://prove2.me/submissions/b4f49f25-c05a-4e3d-a30c-78bec7ec0fba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne

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
include π
namespace GlobalTheory.PrimeElement
theorem _root_.solution [IsDomain R] : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (Ideal.span {π}).primeCompl_le_nonZeroDivisors
end GlobalTheory.PrimeElement
