-- Prove2me | solution 1 for GlobalTheory.JHMult.step_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:00.059143+00:00
-- url     : https://prove2.me/submissions/80ff0468-cbf7-43ae-bbe5-dbdfeaf3189d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Theorems.Thm_GlobalTheory_JHMult_exists_factor
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
variable {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
  {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
namespace GlobalTheory.JHMult
theorem _root_.solution (hσ : σ.IsIrreducible) (hker : ∀ v, p v = 0 → ∃ u, ι u = v)
    {S T : Subrepresentation ρ} (hTS : T ≤ S) (h : Step σ S T) :
    Step σ (subComap ι S) (subComap ι T) ∨ Step σ (subMap p S) (subMap p T) := by
  obtain ⟨f, h1, h2, h3⟩ := h
  let R : Subrepresentation σ := ⟨(subComap ι S).toSubmodule.map (f ∘ₗ ι.toLinearMap), by
    rintro g _ ⟨u, hu, rfl⟩
    refine ⟨ρ₁ g u, (subComap ι S).apply_mem_toSubmodule g hu, ?_⟩
    show f (ι (ρ₁ g u)) = σ g (f (ι u))
    rw [ι.isIntertwining, h2 g (ι u) hu]⟩
  rcases eq_bot_or_eq_top R with hR | hR
  · right
    obtain ⟨k, hk⟩ := exists_factor (p.toLinearMap ∘ₗ S.toSubmodule.subtype)
      (f ∘ₗ S.toSubmodule.subtype) (by
        rintro ⟨v, hv⟩ h0
        obtain ⟨u, rfl⟩ := hker v h0
        have : f (ι u) ∈ R.toSubmodule := ⟨u, hv, rfl⟩
        rw [hR] at this
        exact this)
    have hk' : ∀ v ∈ S.toSubmodule, k (p v) = f v := fun v hv => hk ⟨v, hv⟩
    refine ⟨k, fun w => ?_, ?_, ?_⟩
    · obtain ⟨v, hv, rfl⟩ := h1 w
      exact ⟨p v, ⟨v, hv, rfl⟩, hk' v hv⟩
    · rintro g _ ⟨v, hv, rfl⟩
      show k (ρ₂ g (p v)) = σ g (k (p v))
      rw [← p.isIntertwining, hk' v hv, hk' _ (S.apply_mem_toSubmodule g hv), h2 g v hv]
    · rintro _ ⟨v, hv, rfl⟩
      constructor
      · intro h0
        exact ⟨v, (h3 v hv).1 ((hk' v hv).symm.trans h0), rfl⟩
      · rintro ⟨t, ht, h0⟩
        rw [← h0]
        exact (hk' t (hTS ht)).trans ((h3 t (hTS ht)).2 ht)
  · left
    refine ⟨f ∘ₗ ι.toLinearMap, fun w => ?_, fun g u hu => ?_, fun u hu => h3 _ hu⟩
    · have : w ∈ R.toSubmodule := by rw [hR]; trivial
      exact this
    · show f (ι (ρ₁ g u)) = σ g (f (ι u))
      rw [ι.isIntertwining, h2 g (ι u) hu]
end GlobalTheory.JHMult
