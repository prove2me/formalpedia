-- Prove2me | solution 1 for GlobalTheory.graphClosure.exists_extension_of_isIso_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:58:55.942326+00:00
-- url     : https://prove2.me/submissions/28611d0b-bf22-4a7a-9e2c-c57697c156ab

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
theorem _root_.solution [IsIso (fst f₁ f₂ u φ h)] :
    ∃ ψ : Z₁ ⟶ Z₂, f₁ = ψ ≫ f₂ ∧ u ≫ ψ = φ := by
  refine ⟨inv (fst f₁ f₂ u φ h) ≫ snd f₁ f₂ u φ h, by simp [← condition], ?_⟩
  have : u ≫ inv (fst f₁ f₂ u φ h) = incl f₁ f₂ u φ h := by simp
  rw [reassoc_of% this, incl_snd]
end GlobalTheory.graphClosure
