-- Prove2me | solution 1 for GlobalTheory.T.associated_prime_localization_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:16.187701+00:00
-- url     : https://prove2.me/submissions/844ee066-77fb-4004-a7b5-71213ad2d485

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvrStatement
import Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 → (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) → ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by
  first | exact @GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient | exact GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient | (intros; apply GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient <;> assumption)
end _root_.GlobalTheory.T
