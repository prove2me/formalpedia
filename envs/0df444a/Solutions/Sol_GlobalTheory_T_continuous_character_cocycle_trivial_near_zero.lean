-- Prove2me | solution 1 for GlobalTheory.T.continuous_character_cocycle_trivial_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:15:19.609122+00:00
-- url     : https://prove2.me/submissions/c815227f-182a-4d81-890d-c111b5907ad1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousCharacterCocycleTrivialNearZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousCharacterCocycleTrivialNearZeroStatement
import Theorems.Thm_GlobalTheory_CocycleChar_cocycle_char_trivial_near_zero


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
theorem _root_.solution : ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  first | exact @GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | exact GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | (intros; apply GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero <;> assumption)
end _root_.GlobalTheory.T
