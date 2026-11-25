-- Prove2me | solution 1 for GlobalTheory.PrimeElement.isUnit_algebraMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:07:14.050799+00:00
-- url     : https://prove2.me/submissions/834a0062-6d11-4791-a0ad-39066e708284

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Theorems.Thm_GlobalTheory_PrimeElement_mem_primeCompl_span

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
theorem _root_.solution (x : R) : IsUnit (algebraMap R S x) ↔ ¬ π ∣ x := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff S (Ideal.span {π}), mem_primeCompl_span]
end GlobalTheory.PrimeElement
