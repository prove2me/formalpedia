-- Prove2me | solution 1 for GlobalTheory.rootsOfUnityCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:49.881242+00:00
-- url     : https://prove2.me/submissions/1bccaac9-a46a-4d19-97b9-78fffbec9398

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Theorems.Thm_GlobalTheory_card_pow_eq_one_le_of_isCyclic_units
import Theorems.Thm_GlobalTheory_card_pow_eq_one_two_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.CyclotomicNorms.RootsOfUnityCount := by
  intro ℓ w d hℓ hw hd
  have : NeZero (ℓ ^ w) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  by_cases h2 : ℓ = 2
  · subst h2
    exact ⟨fun h => absurd rfl h, card_pow_eq_one_two_pow_le w hw hd⟩
  ·
    have := ZMod.isCyclic_units_of_prime_pow ℓ hℓ h2 w
    have h := card_pow_eq_one_le_of_isCyclic_units (ℓ ^ w) (d := d) hd
    exact ⟨fun _ => h.trans (Nat.le_mul_of_pos_right _ (pow_pos hℓ.pos _)), h.trans (by omega)⟩
end GlobalTheory
