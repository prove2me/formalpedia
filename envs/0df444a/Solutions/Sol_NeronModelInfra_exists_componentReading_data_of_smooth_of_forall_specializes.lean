-- Prove2me | solution 1 for NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b102d204-bab6-59c5-88d0-81bbaaef64ea

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import Theorems.Thm_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_genericFibre
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace P2mReadingExists

theorem smoothOfRelativeDimension_genericFibre_of_chart
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d gK]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1] :
    SmoothOfRelativeDimension d (pullback.snd f (specGenericFibreInclusion R K)) := by
  rw [← e.2]
  have : SmoothOfRelativeDimension (0 + d) (e.1 ≫ gK) := inferInstance
  simpa using this

theorem injective_algebraMap_of_isIndexOneExtension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R O] [IsLocalHom (algebraMap R O)]
    (h : IsIndexOneExtension R O) : Function.Injective (algebraMap R O) := by
  rw [RingHom.injective_iff_ker_eq_bot]

  by_contra hne
  have hprime : (RingHom.ker (algebraMap R O)).IsPrime := RingHom.ker_isPrime _
  have hmax : RingHom.ker (algebraMap R O) = IsLocalRing.maximalIdeal R :=

    IsLocalRing.eq_maximalIdeal (hprime.isMaximal hne)

  have hmap : Ideal.map (algebraMap R O) (IsLocalRing.maximalIdeal R) = ⊥ := by
    rw [← hmax, Ideal.map_eq_bot_iff_le_ker]
  apply IsDiscreteValuationRing.not_a_field O
  rw [← h.map_maximalIdeal, hmap]

theorem exists_omegaU {K : Type u} [Field K] {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ(gK.topDifferentials d, ⊤)) (U : XK.Opens) (hU : IsAffineOpen U) :
    ∃ ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)),
      gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω :=
  (Scheme.Hom.topToSections_bijective_of_isAffineOpen gK d hU).2 _

section A

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
  (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
  (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
  (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y)
  [algR : Algebra R (Y.presheaf.stalk y)]
  (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))))

include f y hy hmax algR halg

theorem stalk_facts : ∃ (_ : IsDomain (Y.presheaf.stalk y)) (_ : IsDiscreteValuationRing (Y.presheaf.stalk y)),
    Function.Injective (algebraMap R (Y.presheaf.stalk y)) := by
  obtain ⟨hdom, hdvr, hloc, hidx⟩ :=
    NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes f y hy hmax halg
  exact ⟨hdom, hdvr, injective_algebraMap_of_isIndexOneExtension (Y.presheaf.stalk y) hidx⟩

theorem injective_toFrac : Function.Injective (algebraMap R (FractionRing (Y.presheaf.stalk y))) := by
  obtain ⟨hdom, hdvr, hinj⟩ := stalk_facts f y hy hmax halg
  rw [IsScalarTower.algebraMap_eq R (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))]
  exact (IsFractionRing.injective (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))).comp hinj

variable [hdomI : IsDomain (Y.presheaf.stalk y)]

include K hdomI

@[reducible] def algK : Algebra K (FractionRing (Y.presheaf.stalk y)) :=
  (IsFractionRing.lift (K := K) (g := algebraMap R (FractionRing (Y.presheaf.stalk y)))
    (injective_toFrac f y hy hmax halg)).toAlgebra

theorem tower_RKF : letI := algK K f y hy hmax halg
    IsScalarTower R K (FractionRing (Y.presheaf.stalk y)) :=
  letI := algK K f y hy hmax halg
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (K := K) (injective_toFrac f y hy hmax halg) x).symm

include gK e

@[reducible] def xF : letI := algK K f y hy hmax halg; letI := tower_RKF K f y hy hmax halg
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K (FractionRing (Y.presheaf.stalk y))))) gK :=
  letI := algK K f y hy hmax halg; letI := tower_RKF K f y hy hmax halg
  NeronModelInfra.schemeHomOverComp
    (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
      (⟨Y.fromSpecStalk y, halg⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f)) e

@[reducible] def xpt : XK := (xF K gK f e y hy hmax halg).1.base (IsLocalRing.closedPoint (FractionRing (Y.presheaf.stalk y)))

theorem exists_chart (U₀ : XK.Opens) (hxU₀ : xpt K gK f e y hy hmax halg ∈ U₀) :
    letI := algK K f y hy hmax halg
    ∃ (U : XK.Opens) (hU : IsAffineOpen U) (algU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : letI := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
        (xF K gK f e y hy hmax halg).1),
      xpt K gK f e y hy hmax halg ∈ U ∧ U ≤ U₀ := by
  letI algK' := algK K f y hy hmax halg
  haveI := tower_RKF K f y hy hmax halg
  obtain ⟨U'', hUmem, hxU, hUU₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp XK.isBasis_affineOpens) hxU₀
  let U : XK.Opens := U''
  have hUaff : IsAffineOpen U := hUmem
  change xpt K gK f e y hy hmax halg ∈ U at hxU
  change U ≤ U₀ at hUU₀

  have hrange : Set.range (xF K gK f e y hy hmax halg).1.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : p = IsLocalRing.closedPoint (FractionRing (Y.presheaf.stalk y)) := Subsingleton.elim _ _
    rw [this]; exact hxU
  let xU : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ (U : Scheme.{u}) :=
    IsOpenImmersion.lift U.ι (xF K gK f e y hy hmax halg).1 hrange
  have hxU_fac : xU ≫ U.ι = (xF K gK f e y hy hmax halg).1 := IsOpenImmersion.lift_fac U.ι _ hrange
  let φ : Γ(XK, U) ⟶ CommRingCat.of (FractionRing (Y.presheaf.stalk y)) := Spec.homEquiv (xU ≫ hUaff.isoSpec.hom)
  have hφ : Spec.map φ = xU ≫ hUaff.isoSpec.hom := Spec.homEquiv.symm_apply_apply (xU ≫ hUaff.isoSpec.hom)
  letI algU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y))) = φ := rfl
  have hxfac : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫
      hUaff.fromSpec = (xF K gK f e y hy hmax halg).1 := by
    rw [hφ', hφ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hxU_fac]

  letI algKU : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
  have halgKU : algebraMap K Γ(XK, U) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U le_top).hom :=
    rfl
  have key : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U le_top ≫ φ =
      CommRingCat.ofHom (algebraMap K (FractionRing (Y.presheaf.stalk y))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← (xF K gK f e y hy hmax halg).2, ← hxfac, hφ']
    simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec gK (isAffineOpen_top _) hUaff le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have ecomp : (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y))).comp (algebraMap K Γ(XK, U)) =
      algebraMap K (FractionRing (Y.presheaf.stalk y)) := by
    have h := congrArg CommRingCat.Hom.hom key
    rw [halgKU]
    first | exact h | (simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc] at h ⊢; exact h)
  haveI towKUF := IsScalarTower.of_algebraMap_eq' (R := K) (S := Γ(XK, U))
    (A := FractionRing (Y.presheaf.stalk y)) ecomp.symm
  exact ⟨U, hUaff, algU, towKUF, hxfac, hxU, hUU₀⟩

end A

theorem topToSections_smul {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) (U : X.Opens) (g : Γ(X, U)) (s : ⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U))) :
    f.topToSections d U (g • s) = g • f.topToSections d U s := by
  unfold Scheme.Hom.topToSections
  rw [LinearMap.map_smul]
  exact LinearMap.map_smul _ g _

noncomputable def basisKaehlerPresheaf {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (bU : Module.Basis (Fin d) Γ(X, U) Γ(f.kaehler, U)) :
    Module.Basis (Fin d) Γ(X, U) (f.kaehlerPresheaf.obj (op U)) :=
  bU.map (LinearEquiv.ofBijective (f.kaehlerToSectionsₗ U)
    (Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hU)).symm

theorem bijective_smul_of_isFrameOn {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (ω : Γ(f.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (ωU : ⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U)))
    (hωU : f.topToSections d U ωU = (f.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    Function.Bijective fun g : Γ(X, U) => g • ωU := by
  have hbij := Scheme.Hom.topToSections_bijective_of_isAffineOpen f d hU
  have hfr := hω.bijective (W := U) le_top le_top
  have hcomp : (f.topToSections d U) ∘ (fun g : Γ(X, U) => g • ωU) =
      fun g : Γ(X, U) => g • ((f.topDifferentials d).presheaf.map (homOfLE le_top).op ω : Γ(f.topDifferentials d, U)) := by
    funext g
    simp only [Function.comp_apply, topToSections_smul, hωU]
  have h2 : Function.Bijective ((f.topToSections d U) ∘ (fun g : Γ(X, U) => g • ωU)) := by rw [hcomp]; exact hfr
  exact ⟨fun a b hab => h2.1 (by simp only [Function.comp_apply, hab]),
    fun s => by obtain ⟨g, hg⟩ := h2.2 (f.topToSections d U s); exact ⟨g, hbij.1 hg⟩⟩

end P2mReadingExists

theorem P2mReadingExists.topFormMap_ne_zero_of_isFrameOn
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))))
    [IsDomain (Y.presheaf.stalk y)] [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    [Algebra K (FractionRing (Y.presheaf.stalk y))] [IsScalarTower R K (FractionRing (Y.presheaf.stalk y))]
    (U : XK.Opens) (hU : IsAffineOpen U)
    (bU : Module.Basis (Fin d) Γ(XK, U) Γ(gK.kaehler, U))
    [Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y))]
    (hT : letI := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
      (NeronModelInfra.schemeHomOverComp
        (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
          (⟨Y.fromSpecStalk y, halg⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
        e).1)
    (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
    (hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    letI := gK.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU ≠ 0 := by
  classical
  letI algKU : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
  haveI := hT

  haveI : Smooth gK := SmoothOfRelativeDimension.smooth (n := d) (f := gK)
  haveI : IsReduced XK := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian gK

  let y₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f :=
    ⟨Y.fromSpecStalk y, halg⟩
  let pG := NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y)) y₀
  let xF := NeronModelInfra.schemeHomOverComp pG e
  have hxF : xF.1 = pG.1 ≫ e.1 := rfl
  let pt := IsLocalRing.closedPoint (FractionRing (Y.presheaf.stalk y))
  let x : XK := xF.1.base pt

  have happ : ∀ {A B C : Scheme.{u}} (f₁ : A ⟶ B) (f₂ : B ⟶ C) (z : A), (f₁ ≫ f₂).base z = f₂.base (f₁.base z) :=
    fun _ _ _ => rfl
  have hxU : x ∈ U := by
    have : x ∈ Set.range hU.fromSpec.base := by
      refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y))))).base pt, ?_⟩
      exact (happ (Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y))))) hU.fromSpec pt).symm.trans
        (congrArg (fun h : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ XK => h.base pt) hx)
    rwa [IsAffineOpen.range_fromSpec] at this

  haveI : IsPreimmersion (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq]; exact IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hpG : pG.1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))) ≫
        Y.fromSpecStalk y :=
    NeronModelInfra.pointGenericFibre_coe_comp_fst y₀
  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (Y.presheaf.stalk y))
  haveI : IsPreimmersion (pG.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) := by
    rw [hpG]; infer_instance
  haveI : IsPreimmersion pG.1 := IsPreimmersion.of_comp _ (pullback.fst f (specGenericFibreInclusion R K))
  haveI : IsPreimmersion xF.1 := by rw [hxF]; infer_instance

  have hxmax : ∀ y' : XK, y' ⤳ x → y' = x := by
    intro y' hy'

    have hy'range : y' ∈ Set.range e.1.base :=
      hy'.mem_open e.1.isOpenEmbedding.isOpen_range ⟨pG.1.base pt, by show _ = xF.1.base pt; rw [hxF, happ]⟩
    obtain ⟨z', rfl⟩ := hy'range
    have hxz : x = e.1.base (pG.1.base pt) := by
      show xF.1.base pt = _; rw [hxF, happ]
    rw [hxz] at hy' ⊢
    have hz' : z' ⤳ pG.1.base pt := e.1.isEmbedding.isInducing.specializes_iff.mp hy'

    let fst := pullback.fst f (specGenericFibreInclusion R K)
    let sp := Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))))
    let η : Y := fst.base (pG.1.base pt)
    have hηeq : η = (Y.fromSpecStalk y).base (sp.base pt) :=
      (happ pG.1 fst pt).symm.trans ((congrArg (fun h : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ Y => h.base pt) hpG).trans (happ sp (Y.fromSpecStalk y) pt))
    have hηy : η ⤳ y := by
      rw [hηeq]; exact (Scheme.range_fromSpecStalk (x := y)).le ⟨_, rfl⟩

    have hpt : pt.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have hp : (sp.base pt).asIdeal = ⊥ := by
      show (PrimeSpectrum.comap _ pt).asIdeal = ⊥
      rw [PrimeSpectrum.comap_asIdeal, hpt]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))
    have hmaxη : ∀ w : Y, w ⤳ η → w = η := by
      intro w hw
      obtain ⟨q, hq⟩ : w ∈ Set.range (Y.fromSpecStalk y).base := by
        rw [Scheme.range_fromSpecStalk]; exact hw.trans hηy
      by_cases hqbot : q.asIdeal = ⊥
      · rw [← hq, hηeq]; congr 1; apply PrimeSpectrum.ext; rw [hqbot, hp]
      · have hqmax : q = IsLocalRing.closedPoint (Y.presheaf.stalk y) := by
          apply PrimeSpectrum.ext
          exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal (hpi := q.2) hqbot)
        have hwy : w = y := by rw [← hq, hqmax]; exact Scheme.fromSpecStalk_closedPoint
        rw [hwy] at hw ⊢
        exact ((hw.antisymm hηy).eq).symm ▸ rfl
    have h1 : fst.base z' ⤳ η := hz'.map fst.continuous
    have h2 : fst.base z' = fst.base (pG.1.base pt) := hmaxη _ h1
    have h3 : z' = pG.1.base pt := fst.isEmbedding.injective h2
    rw [h3]

  haveI hloc := AlgebraicGeometry.IsAffineOpen.isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
    hU x hxU hxmax (FractionRing (Y.presheaf.stalk y)) xF.1 rfl hx

  have hbij := bijective_smul_of_isFrameOn gK d hU ω hω ωU hωU
  let b := basisKaehlerPresheaf gK d hU bU
  exact NeronModelInfra.TopFormOrder.topFormMap_ne_zero_of_bijective_smul_of_isLocalization K Γ(XK, U)
    (FractionRing (Y.presheaf.stalk y)) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl d b ωU hbij

open P2mReadingExists in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    ∃ (_ : IsDomain (Y.presheaf.stalk y)) (_ : IsDiscreteValuationRing (Y.presheaf.stalk y))
      (algebra : Algebra R (Y.presheaf.stalk y))
      (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))))
      (algebraK : Algebra K (FractionRing (Y.presheaf.stalk y)))
      (_ : IsScalarTower R K (FractionRing (Y.presheaf.stalk y)))
      (b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R]))
      (U : XK.Opens) (hU : IsAffineOpen U)
      (algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : letI := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
        (schemeHomOverComp
          (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
            (⟨Y.fromSpecStalk y, halg⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
          e).1)
      (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
      (_ : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
      (a : FractionRing (Y.presheaf.stalk y)),
      (letI := gK.sectionsAlgebra U;
        TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
          a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
            (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)) ∧
      a ≠ 0 := by
  classical
  letI algR : Algebra R (Y.presheaf.stalk y) := stalkAlgebra f y
  have halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))) :=
    fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra f y
  obtain ⟨hdom, hdvr, hinj⟩ := stalk_facts f y hy hmax halg

  haveI := smoothOfRelativeDimension_genericFibre_of_chart K gK d f e
  haveI : SmoothOfRelativeDimension d f := AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_genericFibre K f d
  obtain ⟨b⟩ := AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
    f d y halg

  letI algK' := algK K f y hy hmax halg
  haveI towRKF := tower_RKF K f y hy hmax halg

  obtain ⟨U₀, hxU₀, eΩ, hbasis⟩ :=
    AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension gK d
      (xpt K gK f e y hy hmax halg)
  obtain ⟨U, hU, algU, towKUF, hx, hxU, hUU₀⟩ := exists_chart K gK f e y hy hmax halg U₀ hxU₀
  letI := algU

  have hω' := exists_omegaU gK d ω U hU
  cases hω' with
  | intro ωU hωU =>

  have hline := (NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
    R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d b).2
    (letI := gK.sectionsAlgebra U; TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU)
  cases hline with
  | intro a ha =>
  have hbU := hbasis U hUU₀ hU
  cases hbU with
  | intro bU _ =>
  have hne := topFormMap_ne_zero_of_isFrameOn K gK d ω hω f e y hy hmax halg U hU bU towKUF hx ωU hωU
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hne
    rw [ha, zero_smul]
  exact ⟨hdom, hdvr, algR, halg, algK', towRKF, b, U, hU, algU, towKUF, hx, ωU, hωU, a, ha, ha0⟩

end

end S_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes
end P2MW
export P2MW.S_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes (solution)
