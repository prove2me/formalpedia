-- Prove2me | solution 1 for GlobalTheory.graphClosure.isIso_fst_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:28.441797+00:00
-- url     : https://prove2.me/submissions/4ad12fce-6d14-4d2e-a9a1-ba5755acc6ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {S Z₁ Z₂ U T T' : Scheme.{u}} (f₁ : Z₁ ⟶ S) (f₂ : Z₂ ⟶ S) (u : U ⟶ Z₁) (φ : U ⟶ Z₂)
  (h : u ≫ f₁ = φ ≫ f₂)
open GlobalTheory.graphClosure
namespace GlobalTheory.graphClosure
theorem _root_.solution [IsSchemeTheoreticallyDominant u] [IsSeparated f₂]
    (ψ : Z₁ ⟶ Z₂) (hψ : f₁ = ψ ≫ f₂) (hu : u ≫ ψ = φ) : IsIso (fst f₁ f₂ u φ h) := by
  let c : Z₁ ⟶ pullback f₁ f₂ := pullback.lift (𝟙 Z₁) ψ (by simpa using hψ)
  have hc₁ : c ≫ pullback.fst _ _ = 𝟙 Z₁ := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = ψ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst _ _) := by rw [hc₁]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.fst _ _)
  have hc : u ≫ c = graphMap f₁ f₂ u φ h := by
    apply pullback.hom_ext <;> simp [hc₁, hc₂, hu]
  have e : fst f₁ f₂ u φ h = closureToClosed _ u c hc := by
    rw [← Category.comp_id (closureToClosed _ u c hc), ← hc₁, closureToClosed_comp_assoc]
    rfl
  rw [e]
  exact isIso_closureToClosed _ u c hc
end GlobalTheory.graphClosure
