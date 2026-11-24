-- Prove2me | solution 1 for GlobalTheory.ProjPoint.ofHom_eq_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:51.965269+00:00
-- url     : https://prove2.me/submissions/6371a2bc-f75f-4fa3-aac1-114a80bf6df7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Theorems.Thm_GlobalTheory_ProjPoint_awayLift_mk_mul
import Theorems.Thm_GlobalTheory_ProjPoint_eq_awayLift
import Theorems.Thm_GlobalTheory_ProjPoint_ofHom_toSpecZero
import Theorems.Thm_P2M_GlobalTheory_ProjPoint_SpecMap_ofHom_eq_away__97605d53820a
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
import Theorems.Thm_GlobalTheory_ProjPoint_SpecMap_ofHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.ProjPoint.ofHom_toSpecZero
attribute [reassoc] GlobalTheory.ProjPoint.SpecMap_ofHom_eq_awayι
attribute [reassoc] GlobalTheory.ProjPoint.SpecMap_ofHom

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
namespace GlobalTheory.ProjPoint
theorem _root_.solution {φ φ' : A →+* B} (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    (hφ' : (irrelevant 𝒜).toIdeal.map φ' = ⊤) (c : B)
    (hc : ∀ n, ∀ a ∈ 𝒜 n, φ' a = c ^ n * φ a) : ofHom 𝒜 φ' hφ' = ofHom 𝒜 φ hφ := by
  refine hom_ext 𝒜 _ hφ' fun D _ χ f n hn hf hu => ?_
  have hu2 := hu
  rw [hc n f hf, map_mul, IsUnit.mul_iff] at hu2
  rw [SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu, SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu2.2]
  congr 3
  symm
  refine eq_awayLift 𝒜 _ _ hf _ fun m a ha => ?_
  have := awayLift_mk_mul 𝒜 (χ.comp φ) hu2.2 hf m a ha
  simp only [RingHom.comp_apply] at this ⊢
  generalize awayLift 𝒜 (χ.comp φ) f hu2.2 (Away.mk 𝒜 hf m a ha) = t at this ⊢
  rw [hc _ a ha, hc n f hf, map_mul, map_mul, ← this, mul_pow, smul_eq_mul, map_pow, map_pow]
  ring
end GlobalTheory.ProjPoint
