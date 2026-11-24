-- Prove2me | solution 1 for GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:00.853891+00:00
-- url     : https://prove2.me/submissions/2f7c92e9-e197-4f63-99db-800695a58e93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByPowPrimePowModEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByPowPrimePowModEqStatement
import Theorems.Thm_GlobalTheory_card_fixedBy_pow_prime_pow_modEq


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
theorem _root_.solution : ∀ (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X] (x : G) (p k : ℕ), p.Prime → Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  first | exact @GlobalTheory.card_fixedBy_pow_prime_pow_modEq | exact GlobalTheory.card_fixedBy_pow_prime_pow_modEq | (intros; apply GlobalTheory.card_fixedBy_pow_prime_pow_modEq <;> assumption)
end _root_.GlobalTheory.T
