-- Prove2me | solution 1 for GlobalTheory.FlatDescent.isPullback_resLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:51.590393+00:00
-- url     : https://prove2.me/submissions/e5b56d55-4519-4833-bf24-013d5bf845e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution {p : Y ⟶ X} {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens)
    (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) :
    IsPullback (f.resLE _ W hf) (g.resLE _ W hg) (p ∣_ U) (p ∣_ U) := by
  subst hW
  have hc : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      (s.fst ≫ (p ⁻¹ᵁ U).ι) ≫ p = (s.snd ≫ (p ⁻¹ᵁ U).ι) ≫ p := fun s => by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, s.condition_assoc]
  have hr : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      Set.range (h.lift _ _ (hc s)) ⊆ Set.range (f ⁻¹ᵁ p ⁻¹ᵁ U).ι := fun s => by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (h.lift _ _ _ x) ∈ p ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_apply, h.lift_fst, Scheme.Hom.comp_apply]
    exact (s.fst x).2
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => IsOpenImmersion.lift (f ⁻¹ᵁ p ⁻¹ᵁ U).ι
    (h.lift _ _ (hc s)) (hr s)) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono U.ι]
    simp [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, h.w]
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (f ⁻¹ᵁ p ⁻¹ᵁ U).ι, IsOpenImmersion.lift_fac]
    refine h.hom_ext ?_ ?_
    · simp [← h₁]
    · simp [← h₂]
end GlobalTheory.FlatDescent
