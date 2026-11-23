-- Prove2me | solution 1 for GlobalTheory.JHMult.step_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:01.872043+00:00
-- url     : https://prove2.me/submissions/7fa8f709-dff4-4733-8847-3964e6e2556a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V} {S T : Subrepresentation ρ} :
    Nonempty ((subQuot S T).Equiv σ) ↔ Step σ S T := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨f, hf⟩ := LinearMap.exists_extend (e.toLinearEquiv.toLinearMap ∘ₗ Submodule.mkQ _)
    have hf' : ∀ v (hv : v ∈ S.toSubmodule), f v = e.toLinearEquiv (Submodule.Quotient.mk ⟨v, hv⟩) :=
      fun v hv => congr($hf ⟨v, hv⟩)
    refine ⟨f, fun w => ?_, fun g v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective w
      obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨v, hv, hf' v hv⟩
    · rw [hf' v hv, hf' _ (S.apply_mem_toSubmodule g hv)]
      exact e.toIntertwiningMap.isIntertwining _ _ g (Submodule.Quotient.mk ⟨v, hv⟩)
    · rw [hf' v hv, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
      rfl
  · rintro ⟨f, h1, h2, h3⟩
    have hs : Function.Surjective (f ∘ₗ S.toSubmodule.subtype) := fun w => by
      obtain ⟨v, hv, rfl⟩ := h1 w
      exact ⟨⟨v, hv⟩, rfl⟩
    have hk : T.toSubmodule.comap S.toSubmodule.subtype =
        LinearMap.ker (f ∘ₗ S.toSubmodule.subtype) := by
      ext v
      exact (h3 v.1 v.2).symm
    refine ⟨.mk ((Submodule.quotEquivOfEq _ _ hk).trans
      (LinearMap.quotKerEquivOfSurjective _ hs)) fun g => ?_⟩
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    exact h2 g v.1 v.2
end GlobalTheory.JHMult
