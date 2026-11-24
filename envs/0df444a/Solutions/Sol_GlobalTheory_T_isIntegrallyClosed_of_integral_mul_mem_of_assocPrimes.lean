-- Prove2me | solution 1 for GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:08.998774+00:00
-- url     : https://prove2.me/submissions/b2ff9a4f-5357-4066-9f3e-20f7a7681c2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedOfConductorNonZeroDivisorOfAss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedOfConductorNonZeroDivisorOfAssStatement
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P)) → (∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) → IsIntegrallyClosed R := by
  first | exact @GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | exact GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | (intros; apply GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes <;> assumption)
end _root_.GlobalTheory.T
