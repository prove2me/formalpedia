-- Prove2me | solution 1 for GlobalTheory.T.regular_quotient_prime_element
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:01.541817+00:00
-- url     : https://prove2.me/submissions/278301a7-e4f5-45f6-a312-b73e57a957f6

import Mathlib
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RegularQuotientPrimeElement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_RegularQuotientPrimeElement
import Theorems.Thm_GlobalTheory_prime_algebraMap_localization_of_isRegularRing_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P → IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  first | exact @_root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | exact _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | (intros; apply _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient <;> assumption)
end _root_.GlobalTheory.T
