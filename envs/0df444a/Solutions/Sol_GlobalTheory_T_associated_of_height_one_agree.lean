-- Prove2me | solution 1 for GlobalTheory.T.associated_of_height_one_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:49.107047+00:00
-- url     : https://prove2.me/submissions/42e442c2-3018-4ed5-a67f-2152bf1deeeb

import Mathlib
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AssociatedOfHeightOneAgree
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AssociatedOfHeightOneAgree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (a b : R), a ≠ 0 → b ≠ 0 → (∀ j ∈ J, IsUnit (π j) ∨ Prime (π j)) → (∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b) → (∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) → ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) → ∃ u : Rˣ, a = u * b := by
  first | exact @_root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding | exact _root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding | (intros; apply _root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding <;> assumption)
end _root_.GlobalTheory.T
