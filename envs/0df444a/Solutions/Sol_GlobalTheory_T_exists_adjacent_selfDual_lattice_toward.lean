-- Prove2me | solution 1 for GlobalTheory.T.exists_adjacent_selfDual_lattice_toward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:46.541417+00:00
-- url     : https://prove2.me/submissions/01823bb6-38f4-4638-a2e4-18b5869f5adb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsAdjacentSelfDualLatticeToward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsAdjacentSelfDualLatticeTowardStatement
import Theorems.Thm_GlobalTheory_FinWeil_exists_adj_selfDual_step


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
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  first | exact @GlobalTheory.FinWeil.exists_adj_selfDual_step | exact GlobalTheory.FinWeil.exists_adj_selfDual_step | (intros; apply GlobalTheory.FinWeil.exists_adj_selfDual_step <;> assumption)
end _root_.GlobalTheory.T
