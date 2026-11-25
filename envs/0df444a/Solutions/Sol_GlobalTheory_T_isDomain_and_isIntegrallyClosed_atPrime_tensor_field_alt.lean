-- Prove2me | solution 1 for GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:20:41.796502+00:00
-- url     : https://prove2.me/submissions/071c9af8-674b-470a-9401-522b7ef37e94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldAStatement
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_tensor_field


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
theorem _root_.solution : (∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R) → (∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field | exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field | (intros; apply GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field <;> assumption)
end _root_.GlobalTheory.T
