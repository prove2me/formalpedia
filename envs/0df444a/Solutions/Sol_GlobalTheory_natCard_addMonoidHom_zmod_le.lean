-- Prove2me | solution 1 for GlobalTheory.natCard_addMonoidHom_zmod_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:36.844385+00:00
-- url     : https://prove2.me/submissions/2b8bce73-1495-49f8-9eb4-aee24fd763e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatCardAddMonoidHomZmodLe

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
theorem _root_.solution (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Finite A] :
    Nat.card (A →+ ZMod N) ≤ Nat.card A := by
  classical
  have : Fintype A := Fintype.ofFinite A

  have hinj : Function.Injective fun f : A →+ ZMod N ↦ (ZMod.stdAddChar (N := N)).compAddMonoidHom f :=
    AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar
  calc Nat.card (A →+ ZMod N) ≤ Nat.card (AddChar A ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card A := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
end GlobalTheory
