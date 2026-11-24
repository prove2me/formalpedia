-- Prove2me | solution 1 for GlobalTheory.ProjPoint.ofHom_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:48.299931+00:00
-- url     : https://prove2.me/submissions/b96b56e8-e484-4d8c-95f5-eb5fc7a46f5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Theorems.Thm_GlobalTheory_ProjPoint_awayLift_mk_mul
import Theorems.Thm_GlobalTheory_ProjPoint_eq_awayLift
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
variable {A' τ τ' : Type u} {A₀ : Type u} [CommRing A₀] [CommRing A'] [SetLike τ A₀]
  [AddSubgroupClass τ A₀] [SetLike τ' A'] [AddSubgroupClass τ' A']
  {𝒜₀ : ℕ → τ} {ℬ : ℕ → τ'} [GradedRing 𝒜₀] [GradedRing ℬ]
namespace GlobalTheory.ProjPoint
theorem _root_.solution (g : 𝒜₀ →+*ᵍ ℬ) (hg : irrelevant ℬ ≤ (irrelevant 𝒜₀).map g)
    (φ : A' →+* B) (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    ofHom ℬ φ hφ ≫ Proj.map g hg =
      ofHom 𝒜₀ (φ.comp g.toRingHom) (map_irrelevant_comp_graded g hg hφ) := by
  refine hom_ext 𝒜₀ _ (map_irrelevant_comp_graded g hg hφ) fun D _ χ f n hn hf hu => ?_
  rw [SpecMap_ofHom_eq_awayι 𝒜₀ _ _ χ hn hf hu,
    SpecMap_ofHom_eq_awayι_assoc ℬ φ hφ χ hn (g.2 hf) hu]
  erw [Proj.awayι_comp_map g hg hn f hf]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  refine eq_awayLift 𝒜₀ _ _ hf _ fun m a ha => ?_
  rw [RingHom.comp_apply]
  erw [Away.map_mk]
  exact awayLift_mk_mul ℬ (χ.comp φ) hu (g.2 hf) m _ _
end GlobalTheory.ProjPoint
