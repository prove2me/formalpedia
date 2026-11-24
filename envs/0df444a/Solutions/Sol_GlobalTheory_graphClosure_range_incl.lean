-- Prove2me | solution 1 for GlobalTheory.graphClosure.range_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:58:56.793022+00:00
-- url     : https://prove2.me/submissions/476b1b67-1151-4c63-93d6-2e85df12aca1

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
theorem _root_.solution [Flat u] [Mono u] [QuasiCompact u] [IsSeparated f₂] :
    Set.range (incl f₁ f₂ u φ h) = fst f₁ f₂ u φ h ⁻¹' Set.range u := by
  have H := isPullback_incl f₁ f₂ u φ h
  rw [← H.isoPullback_hom_snd, ← Scheme.Pullback.range_snd, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, H.isoPullback.hom.surjective.range_eq, Set.image_univ]
end GlobalTheory.graphClosure
