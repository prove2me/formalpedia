-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZModDual.nat_card_dual_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:39:00.564521+00:00
-- url     : https://prove2.me/submissions/0bd04691-3880-4b12-b36d-1e4639197987

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NatCardDualEq
import Theorems.Thm_GlobalTheory_ZModDual_card_dual_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZModDual
namespace GlobalTheory.CompanionTheory.ZModDual
theorem _root_.solution : ∀ (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N] [Finite N],
    Nat.card (Module.Dual (ZMod n) N) = Nat.card N := by
  intro n _ N _ _ _
  exact GlobalTheory.ZModDual.card_dual_eq n N
end GlobalTheory.CompanionTheory.ZModDual
