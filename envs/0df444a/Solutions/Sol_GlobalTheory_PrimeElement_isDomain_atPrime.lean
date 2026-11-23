-- Prove2me | solution 1 for GlobalTheory.PrimeElement.isDomain_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:12.575037+00:00
-- url     : https://prove2.me/submissions/11bc1083-f16e-4698-83db-b8ed820901f1

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
theorem _root_.solution [IsDomain R] : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors S (Ideal.span {π}).primeCompl_le_nonZeroDivisors
end GlobalTheory.PrimeElement
