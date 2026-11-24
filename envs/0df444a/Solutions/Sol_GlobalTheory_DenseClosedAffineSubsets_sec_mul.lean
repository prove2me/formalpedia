-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.sec_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:52.259936+00:00
-- url     : https://prove2.me/submissions/e876b3f6-9ddc-47ca-89af-ed518f845e9f

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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {t t' : A} (ht : t ∈ 𝒜 1) (ht' : t' ∈ 𝒜 1)
    {U : Scheme.{0}} (F : A →+* Γ(U, ⊤)) :
    (Proj.toBasicOpenOfGlobalSections 𝒜 F rfl one_pos ht).appTop
      (sec 𝒜 t (HomogeneousLocalization.Away.isLocalizationElem ht ht')) *
      (U.basicOpen (F t)).ι.appTop (F t) = (U.basicOpen (F t)).ι.appTop (F t') := by
  let e : (U.basicOpen (F t)).toScheme ⟶ Spec (.of (Localization.Away (F t))) :=
    (U.isoOfEq (U.toSpecΓ_preimage_basicOpen (F t))).inv ≫ U.toSpecΓ ∣_ _ ≫
      (basicOpenIsoSpecAway (F t)).hom
  have he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) (Localization.Away (F t)))) =
      (U.basicOpen (F t)).ι ≫ U.toSpecΓ := by
    simp only [e, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap, morphismRestrict_ι,
      Scheme.isoOfEq_inv_ι_assoc]
  let ε : Localization.Away (F t) →+* Γ((U.basicOpen (F t)).toScheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Localization.Away (F t)))).inv ≫ e.appTop).hom
  have hε (y : Γ(U, ⊤)) : ε (algebraMap _ _ y) = (U.basicOpen (F t)).ι.appTop y := by
    have h1 := congrArg (fun φ ↦ ((Scheme.ΓSpecIso Γ(U, ⊤)).inv ≫ Scheme.Hom.appTop φ) y) he
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc,
      ← Scheme.ΓSpecIso_inv_naturality_assoc] at h1
    exact h1
  let G : Localization.Away t →+* Localization.Away (F t) :=
    IsLocalization.map (M := .powers t) (T := .powers (F t)) _ F (by
      rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])
  have h2 : Proj.toBasicOpenOfGlobalSections 𝒜 F rfl one_pos ht ≫ Proj.basicOpenToSpec 𝒜 t =
      e ≫ Spec.map (CommRingCat.ofHom (G.comp (algebraMap (HomogeneousLocalization.Away 𝒜 t)
        (Localization.Away t)))) := by
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 t ht one_pos, Proj.toBasicOpenOfGlobalSections]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, e, G]
  have h3 (z : HomogeneousLocalization.Away 𝒜 t) :
      (Proj.toBasicOpenOfGlobalSections 𝒜 F rfl one_pos ht).appTop (sec 𝒜 t z) = ε (G z.val) := by
    have h1 := congrArg (fun φ ↦ ((Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop φ) z) h2
    simp only [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc] at h1
    exact h1
  rw [h3, ← hε, ← hε, ← map_mul]
  congr 1
  simp only [G, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    pow_one]
  exact IsLocalization.mk'_spec _ _ _
end GlobalTheory.DenseClosedAffineSubsets
