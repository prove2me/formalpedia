-- Prove2me | solution 1 for GlobalTheory.extension_descends_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:48:58.556604+00:00
-- url     : https://prove2.me/submissions/0b25e2f9-b09a-4033-afd3-fbedfe818c43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSpecMapFromSpecOfRangeSubset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (R R₂ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (g : R →+* R₂) (gam : FractionRing R →+* FractionRing R₂), (∀ r, gam (algebraMap R _ r) = algebraMap R₂ _ (g r)) → g.IsIntegral → ∀ (X : Scheme.{0}) (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing R) ⟶ X) (χ₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R₂ ⟶ X), _root_.ReciprocityTheory.ChartRestriction.G.Out.jK R₂ ≫ χ₂ = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap gam ≫ y → ∃ χ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X, _root_.ReciprocityTheory.ChartRestriction.G.Out.jK R ≫ χ = y ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap g ≫ χ = χ₂ := by
  intro R R₂ _ _ _ _ _ _ g gam hgam hint X y χ₂ hcomm
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap _root_.ReciprocityTheory.ChartRestriction.G.Out.jK at *
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := χ₂ (IsLocalRing.closedPoint R₂)) (U := ⊤) trivial
  have hmem : ∀ p, χ₂ p ∈ U := fun p =>
    ((IsLocalRing.specializes_closedPoint (R := R₂) p).map χ₂.continuous).mem_open U.2 hxU
  have h₂ : Set.range χ₂ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hy : Set.range y ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    let q : ↥(Spec (CommRingCat.of (FractionRing R₂))) :=
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
    have hp : (Spec.map (CommRingCat.ofHom gam)) q = p := Subsingleton.elim _ _
    have e := Scheme.Hom.comp_apply
      (Spec.map (CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂)))) χ₂ q
    rw [hcomm, Scheme.Hom.comp_apply, hp] at e
    rw [e]
    exact hmem _
  set χ₂' := IsOpenImmersion.lift U.ι χ₂ h₂ with hχ₂'
  set y' := IsOpenImmersion.lift U.ι y hy with hy'
  have hc' : Spec.map (CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂))) ≫ χ₂' =
      Spec.map (CommRingCat.ofHom gam) ≫ y' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hχ₂', hy', IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hcomm]
  set a₂ := Spec.preimage (χ₂' ≫ hU.isoSpec.hom) with ha₂
  set b := Spec.preimage (y' ≫ hU.isoSpec.hom) with hb
  have hab : a₂ ≫ CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂)) =
      b ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha₂, hb, Spec.map_preimage, Spec.map_preimage,
      ← Category.assoc, ← Category.assoc, hc']
  have e1 : ∀ a, gam (b.hom a) = algebraMap R₂ _ (a₂.hom a) := fun a =>
    (congrArg (fun f => f.hom a) hab).symm
  have hcomp : gam.comp (algebraMap R (FractionRing R)) =
      (algebraMap R₂ (FractionRing R₂)).comp g :=
    RingHom.ext hgam
  have hpt : ∀ a, b.hom a ∈ (algebraMap R (FractionRing R)).range := by
    intro a
    obtain ⟨p, hpm, hp⟩ := hint (a₂.hom a)
    rw [RingHom.mem_range]
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨p, hpm, gam.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, e1, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  let e := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨fun u v h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  let φ : Γ(X, U) →+* R := e.symm.toRingHom.comp (b.hom.codRestrict _ hpt)
  have hφ : ∀ a, algebraMap R (FractionRing R) (φ a) = b.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨b.hom a, hpt a⟩)
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv ≫ U.ι, ?_, ?_⟩
  · have hφb : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = b := by
      ext a
      exact hφ a
    rw [← Category.assoc, ← Spec.map_comp, hφb, hb, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hy', IsOpenImmersion.lift_fac]
  · have hφa : CommRingCat.ofHom φ ≫ CommRingCat.ofHom g = a₂ := by
      ext a
      apply IsFractionRing.injective R₂ (FractionRing R₂)
      change algebraMap R₂ _ (g (φ a)) = algebraMap R₂ _ (a₂.hom a)
      rw [← hgam, hφ, e1]
    rw [← Category.assoc, ← Spec.map_comp, hφa, ha₂, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hχ₂', IsOpenImmersion.lift_fac]
end _root_.GlobalTheory
end GlobalTheory
