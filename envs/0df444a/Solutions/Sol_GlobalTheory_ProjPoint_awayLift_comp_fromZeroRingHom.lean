-- Prove2me | solution 1 for GlobalTheory.ProjPoint.awayLift_comp_fromZeroRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:51.173355+00:00
-- url     : https://prove2.me/submissions/168895d4-f93c-4120-a000-1c2d4fa2b65d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
namespace GlobalTheory.ProjPoint
theorem _root_.solution (φ : A →+* B) (f : A) (hf : IsUnit (φ f)) :
    (awayLift 𝒜 φ f hf).comp (fromZeroRingHom 𝒜 _) = φ.comp (algebraMap (𝒜 0) A) := by
  ext a
  change IsLocalization.Away.lift (S := Localization.Away f) f hf
    (algebraMap (Away 𝒜 f) _ (algebraMap (𝒜 0) _ a)) = _
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝒜 0) A,
    IsLocalization.Away.lift_eq]
  rfl
end GlobalTheory.ProjPoint
