-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.basicOpen_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:11:02.108023+00:00
-- url     : https://prove2.me/submissions/56b8e941-63da-49b8-8df2-d0b4e98ac6c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {t t' : A} (ht : t ∈ 𝒜 1) (ht' : t' ∈ 𝒜 1) :
    (Proj.basicOpen 𝒜 t).toScheme.basicOpen
      (sec 𝒜 t (HomogeneousLocalization.Away.isLocalizationElem ht ht')) =
      (Proj.basicOpen 𝒜 t).ι ⁻¹ᵁ Proj.basicOpen 𝒜 t' := by
  have h : (Proj.basicOpen 𝒜 t).ι =
      Proj.basicOpenToSpec 𝒜 t ≫ Proj.awayι 𝒜 t ht one_pos := by
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 t ht one_pos, Proj.awayι, Iso.hom_inv_id_assoc]
  rw [sec, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine, h, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 ht one_pos ht' one_pos]
end GlobalTheory.DenseClosedAffineSubsets
