-- Prove2me | solution 1 for GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:37:16.454835+00:00
-- url     : https://prove2.me/submissions/c01c257d-5bf0-4cbf-bd5c-e4f607af1a0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedIntertwinerCompOfAdjacentLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedIntertwinerCompOfAdjacentLatticesStatement
import Theorems.Thm_GlobalTheory_FinWeil_normOp_comp_of_adj


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
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  first | exact @GlobalTheory.FinWeil.normOp_comp_of_adj | exact GlobalTheory.FinWeil.normOp_comp_of_adj | (intros; apply GlobalTheory.FinWeil.normOp_comp_of_adj <;> assumption)
end _root_.GlobalTheory.T
