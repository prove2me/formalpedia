-- Prove2me | solution 1 for GlobalTheory.T.isDVR_of_principal_prime_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:20:37.085561+00:00
-- url     : https://prove2.me/submissions/4b26dde6-57d7-432e-9e91-0b42529e83c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrLocPrincipalPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrLocPrincipalPrimeStatement
import Theorems.Thm_GlobalTheory_dvr_loc_principal_prime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  first | exact @GlobalTheory.dvr_loc_principal_prime | exact GlobalTheory.dvr_loc_principal_prime | (intros; apply GlobalTheory.dvr_loc_principal_prime <;> assumption)
end _root_.GlobalTheory.T
