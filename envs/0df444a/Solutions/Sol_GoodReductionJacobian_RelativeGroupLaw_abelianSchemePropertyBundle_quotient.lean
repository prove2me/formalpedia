-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/52648806-86b6-5582-8776-5e4d48945475

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient.AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient.GoodReductionJacobian"

universe u v w

section Descent
set_option autoImplicit false

open TensorProduct

namespace Module
p2m_export "Module" "Flat Injective Flat.iff_lTensor_injectiveₛ FaithfullyFlat FaithfullyFlat.lTensor_injective_iff_injective finite_def FaithfullyFlat.of_flat_of_isLocalHom Flat.lTensor_preserves_injective_linearMap"
namespace Flat
p2m_export "Module.Flat" "iff_lTensor_injectiveₛ lTensor_preserves_injective_linearMap"
p2m_open "Module.Flat Module"

open _root_.TensorProduct.AlgebraTensorModule in

theorem of_flat_of_faithfullyFlat' (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Module.Flat R B] : Module.Flat R A := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  rw [← coe_lTensor (A := A),
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective A B,
    ← coe_lTensor (A := B),
    ← EquivLike.comp_injective _ (cancelBaseChange R A B B P),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp,
    ← lTensor_comp_cancelBaseChange,
    LinearMap.coe_comp, LinearEquiv.coe_coe,
    EquivLike.injective_comp,
    coe_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

end Module.Flat

namespace RingHom
p2m_export "RingHom" "coe_coe snd Smooth coe_comp FiniteType comp_id Flat surjective Finite ext comp_apply FaithfullyFlat.iff_flat_and_comap_surjective FaithfullyFlat range comp fst FiniteType.of_comp_of_finite_of_injective"
p2m_open "RingHom"

namespace FaithfullyFlat p2m_export "RingHom.FaithfullyFlat" "injective iff_flat_and_comap_surjective flat" end FaithfullyFlat
p2m_open_scoped "RingHom.FaithfullyFlat" in

theorem FaithfullyFlat.of_flat_of_isLocalHom' {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] {f : A →+* B} (hf : f.Flat) [IsLocalHom f] :
    f.FaithfullyFlat := by
  algebraize [f]
  exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ hf ‹IsLocalHom f›

namespace Flat p2m_export "RingHom.Flat" "comp" end Flat
p2m_open_scoped "RingHom.Flat" in

theorem Flat.of_comp_of_faithfullyFlat {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] {φ : R →+* A} {ψ : A →+* B}
    (hψ : ψ.FaithfullyFlat) (hcomp : (ψ.comp φ).Flat) : φ.Flat := by
  algebraize [φ, ψ, ψ.comp φ]
  exact Module.Flat.of_flat_of_faithfullyFlat' R A B

end RingHom

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "HasRingHomProperty.iff_of_isAffine arrowIsoSpecΓOfIsAffine Surjective GeometricallyReduced HasAffineProperty Flat.of_stalkMap IsClosedImmersion.of_isPreimmersion IsProper Scheme.Hom UniversallyClosed.of_comp_of_isSeparated stalkwise UniversallyClosed IsFinite isAffine_of_isAffineHom IsAffine LocallyOfFiniteType Spec Scheme.Hom.stalkMap_comp Spec.map Scheme Smooth GeometricallyReduced.geometrically_isReduced isReduced_of_isReduced_stalk Scheme.Hom.comp_base HasAffineProperty.iff_of_isAffine Scheme.Hom.comp_appTop Flat.stalkMap Flat isProper_iff IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.iff_of_source_openCover Smooth.of_smooth_fiberToSpecResidueField UniversallyClosed.of_comp_surjective LocallyOfFinitePresentation HasRingHomProperty isReduced_stalk_of_isReduced geometrically Scheme.ΓSpecIso isReduced_of_smooth_of_field"
p2m_open "AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits

namespace Flat p2m_export "AlgebraicGeometry.Flat" "of_stalkMap stalkMap comp" end Flat
p2m_open_scoped "AlgebraicGeometry.Flat" in

theorem Flat.stalkMap_faithfullyFlat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    (f.stalkMap x).hom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.of_flat_of_isLocalHom' (Flat.stalkMap f x)

namespace Flat
p2m_open_scoped "AlgebraicGeometry.Flat" in

private theorem _root_.AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective {Y X Z : Scheme.{u}} (c : Y ⟶ X) (g : X ⟶ Z)
    [Flat c] [Surjective c] [Flat (c ≫ g)] : Flat g := by
  refine Flat.of_stalkMap g fun x => ?_
  obtain ⟨y, rfl⟩ := c.surjective x
  have hcomp : ((c.stalkMap y).hom.comp ((g.stalkMap (c y)).hom)).Flat := by
    have h := Flat.stalkMap (c ≫ g) y
    rw [Scheme.Hom.stalkMap_comp] at h
    exact h
  exact RingHom.Flat.of_comp_of_faithfullyFlat (Flat.stalkMap_faithfullyFlat c y) hcomp

end Flat
p2m_export "AlgebraicGeometry" "Flat.of_comp_of_flat_of_surjective"
p2m_open_scoped "AlgebraicGeometry.IsReduced" in

theorem IsReduced.of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsReduced X] : IsReduced Y := by
  haveI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    obtain ⟨x, rfl⟩ := f.surjective y
    haveI : _root_.IsReduced (X.presheaf.stalk x) := isReduced_stalk_of_isReduced X x
    exact isReduced_of_injective (f.stalkMap x).hom (Flat.stalkMap_faithfullyFlat f x).injective
  exact isReduced_of_isReduced_stalk Y

namespace GeometricallyReduced p2m_export "AlgebraicGeometry.GeometricallyReduced" "geometrically_isReduced" end GeometricallyReduced
namespace GeometricallyReduced
p2m_open_scoped "AlgebraicGeometry.GeometricallyReduced" in

private theorem _root_.AlgebraicGeometry.GeometricallyReduced.of_comp_of_flat_of_surjective {J P S : Scheme.{u}} (p : J ⟶ P) (g : P ⟶ S)
    [Flat p] [Surjective p] [GeometricallyReduced (p ≫ g)] : GeometricallyReduced g := by
  refine ⟨fun K _ y Z fst snd hsq => ?_⟩

  have h1 : IsPullback (pullback.fst p fst) (pullback.snd p fst) p fst := IsPullback.of_hasPullback p fst

  have hbig : IsPullback (pullback.fst p fst) (pullback.snd p fst ≫ snd) (p ≫ g) y :=
    (h1.flip.paste_horiz hsq.flip).flip
  haveI : IsReduced (pullback p fst) := GeometricallyReduced.geometrically_isReduced (f := p ≫ g) y _ _ hbig
  exact IsReduced.of_flat_of_surjective (pullback.snd p fst)

end GeometricallyReduced
p2m_export "AlgebraicGeometry" "GeometricallyReduced.of_comp_of_flat_of_surjective"
end AlgebraicGeometry

end Descent

section DescentB

set_option autoImplicit false

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "HasRingHomProperty.iff_of_isAffine arrowIsoSpecΓOfIsAffine Surjective GeometricallyReduced HasAffineProperty Flat.of_stalkMap IsClosedImmersion.of_isPreimmersion IsProper Scheme.Hom UniversallyClosed.of_comp_of_isSeparated stalkwise UniversallyClosed IsFinite isAffine_of_isAffineHom IsAffine LocallyOfFiniteType Spec Scheme.Hom.stalkMap_comp Spec.map Scheme Smooth GeometricallyReduced.geometrically_isReduced isReduced_of_isReduced_stalk Scheme.Hom.comp_base HasAffineProperty.iff_of_isAffine Scheme.Hom.comp_appTop Flat.stalkMap Flat isProper_iff IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.iff_of_source_openCover Smooth.of_smooth_fiberToSpecResidueField UniversallyClosed.of_comp_surjective LocallyOfFinitePresentation HasRingHomProperty isReduced_stalk_of_isReduced geometrically Scheme.ΓSpecIso isReduced_of_smooth_of_field"
p2m_open "AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits

p2m_open_scoped "AlgebraicGeometry.GeometricallyReduced" in

theorem GeometricallyReduced.of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] : GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd hsq => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) hsq ‹Smooth f›
  exact isReduced_of_smooth_of_field snd

p2m_open_scoped "AlgebraicGeometry.GeometricallyReduced" in

theorem GeometricallyReduced.of_comp_smooth_of_flat_of_surjective {J P S : Scheme.{u}} (p : J ⟶ P) (g : P ⟶ S)
    [Flat p] [Surjective p] [Smooth (p ≫ g)] : GeometricallyReduced g :=
  haveI := GeometricallyReduced.of_smooth (p ≫ g)
  GeometricallyReduced.of_comp_of_flat_of_surjective p g

section Separated

variable {J P S : Scheme.{u}} (p : J ⟶ P) (g : P ⟶ S)

noncomputable abbrev pullbackMapBoth : pullback (p ≫ g) (p ≫ g) ⟶ pullback g g :=
  pullback.map (p ≫ g) (p ≫ g) g g p p (𝟙 S) (by rw [Category.comp_id]) (by rw [Category.comp_id])

theorem mapDesc_comp_pullbackMapBoth :
    pullback.mapDesc p p g ≫ pullbackMapBoth p g = pullback.fst p p ≫ p ≫ pullback.diagonal g := by
  apply pullback.hom_ext
  · simp only [pullbackMapBoth, pullback.mapDesc, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst_assoc]
    simp
  · simp only [pullbackMapBoth, pullback.mapDesc, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc]
    simp [pullback.condition]

theorem diagonal_comp_mapDesc_comp_pullbackMapBoth :
    pullback.diagonal p ≫ pullback.mapDesc p p g ≫ pullbackMapBoth p g = p ≫ pullback.diagonal g := by
  rw [mapDesc_comp_pullbackMapBoth, pullback.diagonal_fst_assoc]

theorem range_diagonal_eq_image_range_mapDesc [Surjective p] :
    Set.range (pullback.diagonal g).base
      = (pullbackMapBoth p g).base '' Set.range (pullback.mapDesc p p g).base := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := p.surjective y
    refine ⟨(pullback.mapDesc p p g).base ((pullback.diagonal p).base x), ⟨_, rfl⟩, ?_⟩
    have h := congrArg (fun φ => φ.base x) (diagonal_comp_mapDesc_comp_pullbackMapBoth p g)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h
  · rintro ⟨w, ⟨v, rfl⟩, rfl⟩
    refine ⟨p.base ((pullback.fst p p).base v), ?_⟩
    have h := congrArg (fun φ => φ.base v) (mapDesc_comp_pullbackMapBoth p g)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h.symm

p2m_open_scoped "AlgebraicGeometry.IsSeparated" in

theorem IsSeparated.of_isClosed_range_mapDesc [Surjective p] [UniversallyClosed p]
    (h : IsClosed (Set.range (pullback.mapDesc p p g).base)) : IsSeparated g := by
  have hπ : UniversallyClosed (pullbackMapBoth p g) :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹UniversallyClosed p› ‹UniversallyClosed p› rfl rfl
  have hclosed : IsClosed (Set.range (pullback.diagonal g).base) := by
    rw [range_diagonal_eq_image_range_mapDesc p g]
    exact (pullbackMapBoth p g).isClosedMap _ h
  haveI : IsClosedImmersion (pullback.diagonal g) := IsClosedImmersion.of_isPreimmersion _ hclosed
  exact ⟨inferInstance⟩

end Separated

end AlgebraicGeometry

end DescentB

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw RelativeGroupLaw.fibreStr RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "one inv mul action fibreStr fibre smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace QuotFin
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

private theorem _root_.RingHom.FiniteType.of_comp_of_finite_of_injective
    {A B C : Type v} [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
    (f : A →+* B) (g : B →+* C) (hg : g.Finite) (hinj : Function.Injective g)
    (hfg : (g.comp f).FiniteType) : f.FiniteType := by
  algebraize [f, g, g.comp f]
  have hC : (⊤ : Subalgebra A C).FG := hfg.1
  have hBC : (⊤ : Submodule B C).FG := Module.finite_def.mp hg
  exact ⟨fg_of_fg_of_fg A B C hC hBC hinj⟩

p2m_alias "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient.RingHom.FiniteType.of_comp_of_finite_of_injective" "RingHom.FiniteType.of_comp_of_finite_of_injective"

theorem appTop_injective_of_flat_of_surjective
    {X Y : Scheme.{v}} [IsAffine X] [IsAffine Y] (q : X ⟶ Y) [Flat q] [Surjective q] :
    Function.Injective q.appTop.hom := by
  have hflat : q.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance
  have hsurj : Surjective (Spec.map q.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine q)).mp inferInstance
  have hcomap : Function.Surjective (PrimeSpectrum.comap q.appTop.hom) := by
    intro x
    obtain ⟨y, hy⟩ := hsurj.surj x
    exact ⟨y, hy⟩
  exact (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hflat, hcomap⟩).injective

theorem locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
    {R₀ : Type v} [CommRing R₀] [IsNoetherianRing R₀]
    {J P : Scheme.{v}} (p : J ⟶ P) (g : P ⟶ Spec (CommRingCat.of R₀))
    [IsFinite p] [Flat p] [Surjective p] [LocallyOfFiniteType (p ≫ g)] :
    LocallyOfFiniteType g := by
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of R₀), ⊤) :=
    isNoetherianRing_of_ringEquiv R₀ (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv
  rw [HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType) P.affineCover]
  intro i

  let u := P.affineCover.f i
  let q := pullback.snd p u
  haveI : IsAffine (pullback p u) := isAffine_of_isAffineHom q

  have hcomp : LocallyOfFiniteType (q ≫ (u ≫ g)) := by
    have : q ≫ (u ≫ g) = pullback.fst p u ≫ (p ≫ g) := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    rw [this]
    infer_instance
  have hC : ((q ≫ (u ≫ g)).appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hcomp
  have hfin : q.appTop.hom.Finite :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp inferInstance).2
  have hinj : Function.Injective q.appTop.hom := appTop_injective_of_flat_of_surjective q
  rw [Scheme.Hom.comp_appTop] at hC
  exact RingHom.FiniteType.of_comp_of_finite_of_injective _ _ hfin hinj hC

theorem isConnected_preimage_singleton_of_comp_surjective
    {J P S : Scheme.{v}} (p : J ⟶ P) (g : P ⟶ S) [Surjective p]
    (hconn : ∀ s : S, _root_.IsConnected ((p ≫ g).base ⁻¹' {s})) (s : S) :
    _root_.IsConnected (g.base ⁻¹' {s}) := by
  have hsurj : Function.Surjective p.base := p.surjective
  have heq : g.base ⁻¹' {s} = p.base '' ((p ≫ g).base ⁻¹' {s}) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Scheme.Hom.comp_base,
      TopCat.coe_comp, Function.comp_apply]
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [heq]
  exact (hconn s).image _ p.base.hom.continuous.continuousOn

end GoodReductionJacobian.RelativeGroupLaw.QuotFin

open _root_.GoodReductionJacobian.RelativeGroupLaw _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient.GoodReductionJacobian.RelativeGroupLaw in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
    [IsFinite (ι ≫ f)] [Flat (ι ≫ f)] [LocallyOfFinitePresentation (ι ≫ f)]
    (hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      ∃ e : T ⟶ E, e ≫ ι = (L.one t).1)
    (hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) →
        ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1)
    (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)
    (hJ : AbelianSchemePropertyBundle R f)
    {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
    (g : P ⟶ Spec (CommRingCat.of R)) (hg : p ≫ g = f) (LP : RelativeGroupLaw R g)
    (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩) :
    AbelianSchemePropertyBundle R g := by

  haveI : Smooth f := hJ.smooth
  haveI : IsProper f := hJ.proper

  haveI : UniversallyClosed (p ≫ g) := by rw [hg]; infer_instance
  haveI : UniversallyClosed g := UniversallyClosed.of_comp_surjective p g

  haveI : Flat (p ≫ g) := by rw [hg]; infer_instance
  haveI : Flat g := Flat.of_comp_of_flat_of_surjective p g

  haveI : LocallyOfFiniteType (p ≫ g) := by rw [hg]; infer_instance
  haveI : LocallyOfFiniteType g :=
    QuotFin.locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective p g
  haveI : LocallyOfFinitePresentation g := inferInstance

  haveI : IsSeparated (p ≫ g) := by rw [hg]; infer_instance
  haveI : IsSeparated g := by
    refine IsSeparated.of_isClosed_range_mapDesc p g ?_

    have e1 : pullback.mapDesc p p g ≫ pullback.fst (p ≫ g) (p ≫ g) = pullback.fst p p := by
      simp only [pullback.mapDesc]
      erw [pullback.lift_fst]
      simp
    haveI : UniversallyClosed (pullback.mapDesc p p g ≫ (pullback.fst (p ≫ g) (p ≫ g) ≫ (p ≫ g))) := by
      rw [← Category.assoc, e1]
      infer_instance
    haveI : UniversallyClosed (pullback.mapDesc p p g) :=
      UniversallyClosed.of_comp_of_isSeparated _ (pullback.fst (p ≫ g) (p ≫ g) ≫ (p ≫ g))
    exact (pullback.mapDesc p p g).isClosedMap.isClosed_range

  haveI : Smooth (p ≫ g) := by rw [hg]; infer_instance
  haveI : GeometricallyReduced g := GeometricallyReduced.of_comp_smooth_of_flat_of_surjective p g
  haveI : Smooth g := by
    refine Smooth.of_smooth_fiberToSpecResidueField g fun y => ?_
    change Smooth (RelativeGroupLaw.fibreStr g y)
    exact RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType (LP.fibre y)
  exact
    { smooth := inferInstance
      proper := (isProper_iff g).2 ⟨inferInstance, inferInstance, inferInstance⟩
      connectedFibres := fun s =>
        QuotFin.isConnected_preimage_singleton_of_comp_surjective p g (by rw [hg]; exact hJ.connectedFibres) s
      hasGroupLaw := ⟨LP⟩ }

end S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient (solution)
