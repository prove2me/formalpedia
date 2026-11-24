-- Prove2me | solution 1 for GlobalTheory.T.annihilator_intersection_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:08.763527+00:00
-- url     : https://prove2.me/submissions/b7c196da-311a-409b-bf4c-de4261941fb7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorIntersectionCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorIntersectionCardStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PairCount_card_annihilator_inf


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
theorem _root_.solution : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ I L : Submodule (ZMod n) X, Nat.card ↥((⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x))) * Nat.card ↥I * Nat.card ↥L = Nat.card X * Nat.card ↥(I ⊓ L) := by
  first | exact @GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf | exact GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf | (intros; apply GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf <;> assumption)
end _root_.GlobalTheory.T
