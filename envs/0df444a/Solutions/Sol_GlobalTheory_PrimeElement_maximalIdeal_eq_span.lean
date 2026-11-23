-- Prove2me | solution 1 for GlobalTheory.PrimeElement.maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:12.722401+00:00
-- url     : https://prove2.me/submissions/a6006f42-e181-40a8-9262-a6f58a5cc39f

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
namespace GlobalTheory.PrimeElement
theorem _root_.solution [IsLocalRing S] :
    maximalIdeal S = Ideal.span {algebraMap R S π} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {π}) S, Ideal.map_span,
    Set.image_singleton]
end GlobalTheory.PrimeElement
