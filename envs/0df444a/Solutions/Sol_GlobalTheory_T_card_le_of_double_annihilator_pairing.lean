-- Prove2me | solution 1 for GlobalTheory.T.card_le_of_double_annihilator_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:01.885488+00:00
-- url     : https://prove2.me/submissions/3691fd51-95fd-4a3d-b59b-af4ac0b506b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardLeOfDoubleAnnihilatorPairing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardLeOfDoubleAnnihilatorPairingStatement
import Theorems.Thm_GlobalTheory_card_le_of_double_annihilator


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
theorem _root_.solution : ∀ (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X] (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O), (∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S) → (∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0) → (∀ e : E, a • e = 0 → e ∈ Es) → Nat.card X ≤ Es.card ^ F.card * Nat.card S := by
  first | exact @GlobalTheory.card_le_of_double_annihilator | exact GlobalTheory.card_le_of_double_annihilator | (intros; apply GlobalTheory.card_le_of_double_annihilator <;> assumption)
end _root_.GlobalTheory.T
