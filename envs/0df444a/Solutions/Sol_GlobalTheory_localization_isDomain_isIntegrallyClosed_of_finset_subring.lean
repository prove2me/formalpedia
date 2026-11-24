-- Prove2me | solution 1 for GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:04.699797+00:00
-- url     : https://prove2.me/submissions/c8d435b6-364e-44ac-a412-9f7fa5d9ee2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
import Theorems.Thm_GlobalTheory_LocalizationIntegrallyClosedDomain_noZeroDivisors
import Theorems.Thm_GlobalTheory_LocalizationIntegrallyClosedDomain_isIntegrallyClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro B _ Q _ H
  haveI : NoZeroDivisors (Localization.AtPrime Q) := LocalizationIntegrallyClosedDomain.noZeroDivisors H
  haveI : IsDomain (Localization.AtPrime Q) := NoZeroDivisors.to_isDomain _
  exact ⟨inferInstance, LocalizationIntegrallyClosedDomain.isIntegrallyClosed H⟩
end GlobalTheory
