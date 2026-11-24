-- Prove2me | solution 1 for GlobalTheory.T.finite_type_to_number_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:03:37.302809+00:00
-- url     : https://prove2.me/submissions/2d0cdca8-d98d-4be4-bb93-c5476d196758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteTypeToNumberField
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FiniteTypeToNumberField
import Theorems.Thm_GlobalTheory_exists_numberField_point_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  first | exact @_root_.GlobalTheory.exists_numberField_point_ne_zero | exact _root_.GlobalTheory.exists_numberField_point_ne_zero | (intros; apply _root_.GlobalTheory.exists_numberField_point_ne_zero <;> assumption)
end _root_.GlobalTheory.T
