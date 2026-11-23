-- Prove2me | solution 1 for GlobalTheory.JHMult.step_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:58.094837+00:00
-- url     : https://prove2.me/submissions/5c602947-9273-4c67-91a0-7d225e23a34f

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
variable {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
  {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
namespace GlobalTheory.JHMult
theorem _root_.solution (hp : Function.Surjective p) {S T : Subrepresentation ρ₂} (h : Step σ S T) :
    Step σ (subComap p S) (subComap p T) := by
  obtain ⟨f, h1, h2, h3⟩ := h
  refine ⟨f ∘ₗ p.toLinearMap, fun w => ?_, fun g u hu => ?_, fun u hu => h3 _ hu⟩
  · obtain ⟨v, hv, rfl⟩ := h1 w
    obtain ⟨u, rfl⟩ := hp v
    exact ⟨u, hv, rfl⟩
  · show f (p (ρ g u)) = σ g (f (p u))
    rw [p.isIntertwining, h2 g (p u) hu]
end GlobalTheory.JHMult
