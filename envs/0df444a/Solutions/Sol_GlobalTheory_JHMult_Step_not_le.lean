-- Prove2me | solution 1 for GlobalTheory.JHMult.Step.not_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:19.569104+00:00
-- url     : https://prove2.me/submissions/cf79c38d-841c-41ac-80ef-6f9499f4bee4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
namespace GlobalTheory.JHMult
namespace Step
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) {S T : Subrepresentation ρ} (h : Step σ S T) : ¬ S ≤ T := by
  intro hle
  obtain ⟨f, h1, -, h3⟩ := h
  refine (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤) (le_antisymm bot_le fun w _ => ?_)
  obtain ⟨v, hv, rfl⟩ := h1 w
  exact (h3 v hv).2 (hle hv)
end Step
end GlobalTheory.JHMult
