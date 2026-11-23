-- Prove2me | solution 1 for GlobalTheory.JHMult.step_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:45.722168+00:00
-- url     : https://prove2.me/submissions/2e7da5be-5fbc-478d-b4a3-d03d0b1ee5bd

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
theorem _root_.solution (hι : Function.Injective ι) {S T : Subrepresentation ρ₁} (h : Step σ S T) :
    Step σ (subMap ι S) (subMap ι T) := by
  obtain ⟨f, h1, h2, h3⟩ := h
  obtain ⟨k, hk⟩ := exists_factor ι.toLinearMap f (fun v hv => by
    have : v = 0 := hι (hv.trans (map_zero ι).symm)
    rw [this, map_zero])
  have hk' : ∀ v, k (ι v) = f v := hk
  refine ⟨k, fun w => ?_, ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := h1 w
    exact ⟨ι v, ⟨v, hv, rfl⟩, hk v⟩
  · rintro g _ ⟨v, hv, rfl⟩
    show k (ρ g (ι v)) = σ g (k (ι v))
    rw [← ι.isIntertwining, hk', hk', h2 g v hv]
  · rintro _ ⟨v, hv, rfl⟩
    rw [hk, h3 v hv]
    constructor
    · exact fun h => ⟨v, h, rfl⟩
    · rintro ⟨t, ht, h0⟩
      exact (hι h0 : t = v) ▸ ht
end GlobalTheory.JHMult
