-- Prove2me | solution 1 for GlobalTheory.ProjPoint.ofHom_toSpecZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:25.587799+00:00
-- url     : https://prove2.me/submissions/16b48ee6-7930-456b-b3bc-b35dcfff1fad

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
theorem _root_.solution (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) :
    ofHom 𝒜 φ hφ ≫ Proj.toSpecZero 𝒜 =
      Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (𝒜 0) A))) := by
  rw [ofHom, Proj.fromOfGlobalSections_toSpecZero, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  simp
end GlobalTheory.ProjPoint
