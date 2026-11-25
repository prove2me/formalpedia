-- Prove2me | solution 1 for GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:16:43.917827+00:00
-- url     : https://prove2.me/submissions/bd3e727f-81b2-4395-9ea1-d433e200f94f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CompletionIsDomainAndIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CompletionIsDomainAndIsIntegrallyClosedStatement
import Theorems.Thm_GlobalTheory_AnalyticNormality_completion_isDomain_and_isIntegrallyClosed


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  first | exact @GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | exact GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed <;> assumption)
end _root_.GlobalTheory.T
