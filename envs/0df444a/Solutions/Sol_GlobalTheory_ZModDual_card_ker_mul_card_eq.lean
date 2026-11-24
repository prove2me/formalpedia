-- Prove2me | solution 1 for GlobalTheory.ZModDual.card_ker_mul_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:48:58.163396+00:00
-- url     : https://prove2.me/submissions/db074c2a-f8c7-4d8d-888d-3b6887e51028

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardKerMulCardEq
import Theorems.Thm_GlobalTheory_ZModDual_card_quot_ker_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ZModDual
namespace GlobalTheory.ZModDual
theorem _root_.solution (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A]
    [Module (ZMod n) A] [Finite A] [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (LinearMap.ker b) * Nat.card B = Nat.card (LinearMap.ker b.flip) * Nat.card A := by
  have h1 := card_quot_ker_le n A B b
  have h2 := card_quot_ker_le n B A b.flip
  rw [LinearMap.flip_flip] at h2
  have heq : Nat.card (A ⧸ LinearMap.ker b) = Nat.card (B ⧸ LinearMap.ker b.flip) := le_antisymm h1 h2
  have eA := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b)
  have eB := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b.flip)
  rw [eA, eB, heq]
  ring
end GlobalTheory.ZModDual
