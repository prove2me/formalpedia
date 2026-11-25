-- Prove2me | solution 1 for GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:18:33.030959+00:00
-- url     : https://prove2.me/submissions/3c2e66d6-4734-42b4-bb51-9303a155bd7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwinerEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwinerEqStatement
import Theorems.Thm_GlobalTheory_FinWeil_invariantForm_normOp_eq


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
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ P Q : X →ₗ[R] X, (∀ x, P (P x) = P x) → (∀ x, Q (Q x) = Q x) → (∀ x, P (Q x) = 0) → (∀ x, Q (P x) = 0) → (∀ x y, γ (P x) y = γ x (Q y)) → (∀ a ∈ A, P a ∈ A) → (∀ a ∈ A, Q a ∈ A) → (∀ x, φ (P x) = P (φ x)) → (∀ x, φ (Q x) = Q (φ x)) → (∀ x, φ x - P (φ x) - Q (φ x) = x - P x - Q x) → ∃ n : ℕ, 0 < n ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ m, ℓ (T m) = (lam (idx A (A.map φ)))⁻¹ * (n : ℂ) * ℓ m := by
  first | exact @GlobalTheory.FinWeil.invariantForm_normOp_eq | exact GlobalTheory.FinWeil.invariantForm_normOp_eq | (intros; apply GlobalTheory.FinWeil.invariantForm_normOp_eq <;> assumption)
end _root_.GlobalTheory.T
