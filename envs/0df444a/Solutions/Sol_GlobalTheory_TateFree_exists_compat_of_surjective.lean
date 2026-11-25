-- Prove2me | solution 1 for GlobalTheory.TateFree.exists_compat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:51.632336+00:00
-- url     : https://prove2.me/submissions/4c82a7e9-6896-4f5a-81eb-ca2ca7bfe896

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.TateFree
namespace GlobalTheory.TateFree
theorem _root_.solution (n : ℕ) : ∀ (X : ℕ → Type) (π : ∀ k, X (k + 1) → X k),
    (∀ k, Function.Surjective (π k)) → ∀ x : X n,
      ∃ s : ∀ k, X k, (∀ k, π k (s (k + 1)) = s k) ∧ s n = x := by
  induction n with
  | zero =>
    intro X π hπ x
    exact ⟨fun k => Nat.rec x (fun k y => Function.surjInv (hπ k) y) k,
      fun k => Function.surjInv_eq (hπ k) _, rfl⟩
  | succ n ih =>
    intro X π hπ x
    obtain ⟨s, hs, hx⟩ := ih (fun k => X (k + 1)) (fun k => π (k + 1)) (fun k => hπ (k + 1)) x
    refine ⟨fun k => Nat.casesOn k (π 0 (s 0)) s, fun k => ?_, hx⟩
    cases k with
    | zero => rfl
    | succ k => exact hs k
end GlobalTheory.TateFree
