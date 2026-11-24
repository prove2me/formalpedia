-- Prove2me | solution 1 for GlobalTheory.T.coset_sum_translate_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:05:29.11575+00:00
-- url     : https://prove2.me/submissions/eae9d253-eb22-43a9-914d-21d0f24b0117

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumTranslateInvariant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumTranslateInvariantStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Transversal_sum_add_eq_sum_of_transversal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  first | exact @GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal | exact GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal | (intros; apply GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal <;> assumption)
end _root_.GlobalTheory.T
