-- Prove2me | solution 1 for GlobalTheory.ZModDual.card_dual_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:27.881592+00:00
-- url     : https://prove2.me/submissions/23dfecd4-847a-4780-851f-9c9d08045987

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveDualAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Theorems.Thm_GlobalTheory_ZModDual_stdAddChar_comp_bijective

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
theorem _root_.solution (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A]
    [Finite A] : Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  classical
  have := Fintype.ofFinite A
  rw [Nat.card_eq_of_bijective _ (stdAddChar_comp_bijective n A),
    Nat.card_eq_fintype_card (α := AddChar A ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card]
end GlobalTheory.ZModDual
