-- Prove2me | solution 1 for GlobalTheory.T.adjacent_selfDual_lattices_index_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:06:05.476637+00:00
-- url     : https://prove2.me/submissions/001792eb-0136-4586-90b5-9036c2072e71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AdjacentSelfDualLatticesIndexSimple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AdjacentSelfDualLatticesIndexSimpleStatement
import Theorems.Thm_GlobalTheory_FinWeil_adjacent_selfDual_simple


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → idx A B = Nat.card (R ⧸ P) ∧ idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  first | exact @GlobalTheory.FinWeil.adjacent_selfDual_simple | exact GlobalTheory.FinWeil.adjacent_selfDual_simple | (intros; apply GlobalTheory.FinWeil.adjacent_selfDual_simple <;> assumption)
end _root_.GlobalTheory.T
