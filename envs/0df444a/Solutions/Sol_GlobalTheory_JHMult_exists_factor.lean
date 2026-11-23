-- Prove2me | solution 1 for GlobalTheory.JHMult.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:55.470129+00:00
-- url     : https://prove2.me/submissions/7b21f627-037a-4ac6-b82b-f6e8bd750fbf

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
theorem _root_.solution (g : V →ₗ[F] V₁) (h : V →ₗ[F] W) (hk : ∀ v, g v = 0 → h v = 0) :
    ∃ k : V₁ →ₗ[F] W, ∀ v, k (g v) = h v := by
  obtain ⟨k, hk'⟩ := LinearMap.exists_extend
    ((LinearMap.ker g).liftQ h hk ∘ₗ g.quotKerEquivRange.symm.toLinearMap)
  refine ⟨k, fun v => ?_⟩
  have := congr($hk' (g.quotKerEquivRange (Submodule.Quotient.mk v)))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
  exact this
end GlobalTheory.JHMult
