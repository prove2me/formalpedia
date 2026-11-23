-- Prove2me | solution 1 for GlobalTheory.PrimeElement.isPrime_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:14.173063+00:00
-- url     : https://prove2.me/submissions/066e9780-586d-4d46-846d-ec28edc54120

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
namespace GlobalTheory.PrimeElement
theorem _root_.solution (hπ : Prime π) : (Ideal.span {π}).IsPrime :=
  (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
end GlobalTheory.PrimeElement
