-- Prove2me | solution 1 for GlobalTheory.graphClosure.existsUnique_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:43.932473+00:00
-- url     : https://prove2.me/submissions/6824d7da-0cf1-4798-92d1-0721c112dc73

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
variable (t₁ : T ⟶ Z₁) (t₂ : T ⟶ Z₂) (ht : t₁ ≫ f₁ = t₂ ≫ f₂) (d : T' ⟶ T)
  [IsSchemeTheoreticallyDominant d] (w : T' ⟶ U) (h₁ : d ≫ t₁ = w ≫ u) (h₂ : d ≫ t₂ = w ≫ φ)
include ht h₁ h₂
namespace GlobalTheory.graphClosure
theorem _root_.solution : ∃! l : T ⟶ graphClosure f₁ f₂ u φ h,
    l ≫ fst f₁ f₂ u φ h = t₁ ∧ l ≫ snd f₁ f₂ u φ h = t₂ :=
  ⟨lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂, by simp,
    fun _ hl ↦ hom_ext f₁ f₂ u φ h (by simp [hl.1]) (by simp [hl.2])⟩
end GlobalTheory.graphClosure
