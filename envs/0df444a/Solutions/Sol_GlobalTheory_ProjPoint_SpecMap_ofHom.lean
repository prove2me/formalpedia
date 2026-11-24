-- Prove2me | solution 1 for GlobalTheory.ProjPoint.SpecMap_ofHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:17.163189+00:00
-- url     : https://prove2.me/submissions/99b76c33-37b5-4b06-9734-6a7aff25a10c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Theorems.Thm_P2M_GlobalTheory_ProjPoint_SpecMap_ofHom_eq_away__97605d53820a
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.ProjPoint.SpecMap_ofHom_eq_awayι

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
namespace GlobalTheory.ProjPoint
theorem _root_.solution (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ofHom 𝒜 φ hφ =
      ofHom 𝒜 (ψ.comp φ) (map_irrelevant_comp 𝒜 hφ ψ) := by
  refine hom_ext 𝒜 _ (map_irrelevant_comp 𝒜 hφ ψ) fun D _ χ f n hn hf hu => ?_
  rw [SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    SpecMap_ofHom_eq_awayι 𝒜 φ hφ (χ.comp ψ) hn hf hu]
end GlobalTheory.ProjPoint
