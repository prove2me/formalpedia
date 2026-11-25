-- Prove2me | solution 1 for GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:39.014857+00:00
-- url     : https://prove2.me/submissions/e87dcd31-8bea-431f-b917-117a1c452e3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSuStatement
import Theorems.Thm_GlobalTheory_localization_isDomain_isIntegrallyClosed_of_finset_subring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | exact GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | (intros; apply GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring <;> assumption)
end _root_.GlobalTheory.T
