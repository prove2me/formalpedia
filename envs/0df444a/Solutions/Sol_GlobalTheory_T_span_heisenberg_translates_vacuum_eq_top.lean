-- Prove2me | solution 1 for GlobalTheory.T.span_heisenberg_translates_vacuum_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:23.046358+00:00
-- url     : https://prove2.me/submissions/08291efd-761e-433a-a2f1-01dc041e454b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTopStatement
import Theorems.Thm_GlobalTheory_FinWeil_span_translates_vacuum


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
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, (∀ v, Fixes W A v → ∃ c : ℂ, v = c • e) → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ := by
  first | exact @GlobalTheory.FinWeil.span_translates_vacuum | exact GlobalTheory.FinWeil.span_translates_vacuum | (intros; apply GlobalTheory.FinWeil.span_translates_vacuum <;> assumption)
end _root_.GlobalTheory.T
