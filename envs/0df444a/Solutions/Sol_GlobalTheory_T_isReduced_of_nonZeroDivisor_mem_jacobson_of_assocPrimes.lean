-- Prove2me | solution 1 for GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:33.173799+00:00
-- url     : https://prove2.me/submissions/f21a8058-dd60-4a5b-80d7-cec23e53b648

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement
import Theorems.Thm_GlobalTheory_isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → x ∈ Ideal.jacobson (⊥ : Ideal R) → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → IsDomain (Localization.AtPrime P)) → IsReduced R := by
  first | exact @GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes | exact GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes | (intros; apply GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes <;> assumption)
end _root_.GlobalTheory.T
