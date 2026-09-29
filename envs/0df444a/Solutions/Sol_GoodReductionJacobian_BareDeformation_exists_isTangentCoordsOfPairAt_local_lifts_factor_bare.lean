-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_factor_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/881bb500-1b94-5c3b-8df1-07019e414826

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_factor_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

universe u

namespace RG1Aux

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem comp_toSpecΓ {X : Scheme.{u}} (U : X.Opens) {R : CommRingCat.{u}} (g : Spec R ⟶ (U : Scheme.{u})) :
    g ≫ U.toSpecΓ = Spec.map (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc]

theorem appLE_topIso_inv {X : Scheme.{u}} (U : X.Opens) {K : CommRingCat.{u}} (c : X ⟶ Spec K) :
    c.appLE ⊤ U le_top ≫ U.topIso.inv = (U.ι ≫ c).appTop := by
  rw [Scheme.Opens.topIso_inv]
  erw [Scheme.Hom.appLE_map]
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop]
  rfl

theorem ext_to_Spec' {R K : CommRingCat.{u}} {f g : Spec R ⟶ Spec K}
    (h : (Scheme.ΓSpecIso K).inv ≫ f.appTop ≫ (Scheme.ΓSpecIso R).hom = (Scheme.ΓSpecIso K).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom) :
    f = g := by
  have h' := congrArg (fun q => q ≫ (Scheme.ΓSpecIso R).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  exact AlgebraicGeometry.ext_to_Spec (by rw [Scheme.Γ_map_op, Scheme.Γ_map_op]; exact h')

variable {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (U : X.Opens)

theorem chart_algebraMap_of_over {R : Type u} [CommRing R] (g : Spec (CommRingCat.of R) ⟶ (U : Scheme.{u}))
    (F : B →+* R) (hg : (g ≫ U.ι) ≫ f = Spec.map (CommRingCat.ofHom F)) (r : B) :
    letI := algebraOfHom f U
    (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (algebraMap B Γ(X, U) r) = F r := by
  letI := algebraOfHom f U
  rw [algebraMap_algebraOfHom]
  show ((f.appLE ⊤ U le_top ≫ U.topIso.inv) ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom r) = F r
  rw [appLE_topIso_inv, ← Category.assoc, ← Scheme.Hom.comp_appTop, ← Category.assoc, hg]
  have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom F))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Spec.map (CommRingCat.ofHom F)).appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom r)) = F r
  rw [← this]
  exact CategoryTheory.Iso.inv_hom_id_apply _ _

theorem over_of_chart_algebraMap {R : Type u} [CommRing R] (g : Spec (CommRingCat.of R) ⟶ (U : Scheme.{u}))
    (F : B →+* R)
    (hg : letI := algebraOfHom f U
      ∀ r : B, (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (algebraMap B Γ(X, U) r) = F r) :
    (g ≫ U.ι) ≫ f = Spec.map (CommRingCat.ofHom F) := by
  letI := algebraOfHom f U
  apply ext_to_Spec'
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  rw [CommRingCat.hom_ofHom, ← hg r, algebraMap_algebraOfHom]
  show _ = ((f.appLE ⊤ U le_top ≫ U.topIso.inv) ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom r)
  rw [appLE_topIso_inv, ← Scheme.Hom.comp_appTop_assoc, Category.assoc g]
  rfl

theorem bijective_of_sub_mem_of_fix {C : Type u} [CommRing C] (J : Ideal C)
    (ψ : C →+* C) (hmod : ∀ c, ψ c - c ∈ J) (hfix : ∀ c ∈ J, ψ c = c) : Function.Bijective ψ := by
  constructor
  · intro a b hab
    have h1 : ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : a - b ∈ J := by have := hmod (a - b); rwa [h1, zero_sub, neg_mem_iff] at this
    have h3 := hfix _ h2
    rw [h1] at h3
    exact sub_eq_zero.mp h3.symm
  · intro c
    refine ⟨c - (ψ c - c), ?_⟩
    rw [map_sub, hfix _ (hmod c)]; abel

theorem fromSpec_comp_eq {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (U : X.Opens) (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) := by
  letI := algebraOfHom f U
  rw [← hU.isoSpec_inv_ι]
  apply over_of_chart_algebraMap f U hU.isoSpec.inv (algebraMap B Γ(X, U))
  intro r
  have hid : U.topIso.inv ≫ hU.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).hom = 𝟙 _ := by
    apply Spec.map_injective
    have hc := comp_toSpecΓ (R := CommRingCat.of Γ(X, U)) U hU.isoSpec.inv
    rw [Spec.map_id, ← hc]
    exact hU.isoSpec_inv_toSpecΓ
  rw [hid]; rfl

theorem flat_sections {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat B Γ(X, U) := by
  letI := algebraOfHom f U
  have h1 : Flat (hU.fromSpec ≫ f) := inferInstance
  rw [fromSpec_comp_eq f U hU, HasRingHomProperty.Spec_iff (P := @Flat)] at h1
  exact h1

end RG1Aux

set_option maxHeartbeats 6400000 in
theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι)
    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))

    (φ₁ : A₁ ⟶ A₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)

    (D : BareDeformation f₁ L₁ B)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hιf : ∀ i, ιD i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpf : ∀ i, mp i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)

    (i j : 𝒰.ι) (W : D₀.A.Opens) (hW : IsAffineOpen W) (hWj : W ≤ 𝒰.U j)
    (nn nn' : (↑W : Scheme.{0}) ⟶ ↑(𝒰.U i))
    (hnn : nn ≫ (𝒰.U i).ι = D₀.A.homOfLE hWj ≫ m j)
    (hnn' : nn' ≫ ιD i = D₀.A.homOfLE hWj ≫ mp j) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    letI := algebraOfHom D₀.f W
    ∃ es : Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).U i₀) →
        (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, W))),
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, W)
        (hW.isoSpec.inv ≫ nn ≫ ιD i) (hW.isoSpec.inv ≫ nn' ≫ ιD i)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) es := by
  classical
  letI instE : Algebra (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).U i₀) := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
  letI instC : Algebra B Γ(D₀.A, W) := algebraOfHom D₀.f W
  haveI : Smooth D₀.f := D₀.bundle.smooth
  haveI : Module.Flat B Γ(D₀.A, W) := RG1Aux.flat_sections D₀.f W hW
  have hI2 : RingHom.ker (algebraMap B B₁) * RingHom.ker (algebraMap B B₁) = ⊥ :=
    le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
  have hker : IsNilpotent (RingHom.ker (algebraMap B B₁)) := ⟨2, by rw [pow_two, hI2]; rfl⟩
  have hfrom : hW.fromSpec ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, W))) := RG1Aux.fromSpec_comp_eq D₀.f W hW

  have hu : (hW.isoSpec.inv ≫ nn ≫ ιD i) ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, W))) := by
    simp only [Category.assoc]
    rw [hιf i, ← Category.assoc nn, hnn, Category.assoc, hmf j, ← Category.assoc (D₀.A.homOfLE hWj),
      Scheme.homOfLE_ι, ← Category.assoc, hW.isoSpec_inv_ι]
    exact hfrom
  have hv : (hW.isoSpec.inv ≫ nn' ≫ ιD i) ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, W))) := by
    simp only [Category.assoc]
    rw [← Category.assoc nn', hnn', Category.assoc, hmpf j, ← Category.assoc (D₀.A.homOfLE hWj),
      Scheme.homOfLE_ι, ← Category.assoc, hW.isoSpec_inv_ι]
    exact hfrom

  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : B₁ →+* (ResidueField B), r₁.comp (algebraMap B B₁) = residue B := by
    refine ⟨(Ideal.Quotient.lift (RingHom.ker (algebraMap B B₁)) (residue B)
      (fun x hx => (Ideal.Quotient.eq_zero_iff_mem).mpr (hI hx))).comp
        (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom, RingHom.ext fun x => ?_⟩
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.quotientKerEquivOfSurjective_symm_apply,
      Ideal.Quotient.lift_mk]
  have hbase : Spec.map (CommRingCat.ofHom r₁) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)) = Spec.map (CommRingCat.ofHom (residue B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr₁]
  have hbig : IsPullback (jκ ≫ D₀.g) (pullback.snd D₀.f (specMap B (ResidueField B))) D₀.f (Spec.map (CommRingCat.ofHom r₁) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
    rw [hjκ, hbase]
    exact IsPullback.of_hasPullback D₀.f (specMap B (ResidueField B))
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap B B₁)) hπ
  have hleftw : jκ ≫ f₁ = (pullback.snd D₀.f (specMap B (ResidueField B))) ≫ Spec.map (CommRingCat.ofHom r₁) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap B B₁))), Category.assoc, Category.assoc, ← D₀.cart.w,
      ← Category.assoc, hjκ, hbase]
    exact pullback.condition
  have hleft : IsPullback jκ (pullback.snd D₀.f (specMap B (ResidueField B))) f₁ (Spec.map (CommRingCat.ofHom r₁)) := IsPullback.of_right hbig hleftw D₀.cart
  have hak : IsPullback (jκ ≫ D.g) (pullback.snd D₀.f (specMap B (ResidueField B))) D.f (Spec.map (CommRingCat.ofHom (residue B))) := by
    rw [← hbase]; exact IsPullback.paste_horiz hleft D.cart

  obtain ⟨-, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq (algebraMap B B₁) hπ hker
    D₀.f f₁ D₀.g D₀.cart W hW
  have hγ : ε.hom ≫ (D₀.g ∣_ W) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, W))))) ≫ hW.isoSpec.inv := by
    rw [← hε, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

  have hPj := isPullback_morphismRestrict D₀.g (𝒰.U j)
  have hPi := isPullback_morphismRestrict D₀.g (𝒰.U i)
  have wj : ((D₀.g ∣_ W) ≫ D₀.A.homOfLE hWj) ≫ (𝒰.U j).ι = (D₀.g ⁻¹ᵁ W).ι ≫ D₀.g := by
    rw [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  have hδj1 := hPj.lift_fst _ _ wj
  have hδj2 := hPj.lift_snd _ _ wj

  have hm : (D₀.g ∣_ W) ≫ D₀.A.homOfLE hWj ≫ m j = (D₀.g ⁻¹ᵁ W).ι ≫ φ₁ ≫ D₀.g := by
    rw [← Category.assoc, ← hδj1, Category.assoc, hmμ j, ← Category.assoc, hδj2]
  have hmp : (D₀.g ∣_ W) ≫ D₀.A.homOfLE hWj ≫ mp j = (D₀.g ⁻¹ᵁ W).ι ≫ φ₁ ≫ D.g := by
    rw [← Category.assoc, ← hδj1, Category.assoc, hmpμ j, ← Category.assoc, hδj2]

  have wi : ((D₀.g ∣_ W) ≫ nn) ≫ (𝒰.U i).ι = ((D₀.g ⁻¹ᵁ W).ι ≫ φ₁) ≫ D₀.g := by
    rw [Category.assoc, hnn, hm, Category.assoc]
  have hδi1 := hPi.lift_fst _ _ wi
  have hδi2 := hPi.lift_snd _ _ wi
  have hn : (D₀.g ∣_ W) ≫ nn ≫ ιD i = (D₀.g ⁻¹ᵁ W).ι ≫ φ₁ ≫ D.g := by
    rw [← Category.assoc, ← hδi1, Category.assoc, hιg i, ← Category.assoc, hδi2, Category.assoc]
  have hn' : (D₀.g ∣_ W) ≫ nn' ≫ ιD i = (D₀.g ⁻¹ᵁ W).ι ≫ φ₁ ≫ D.g := by
    rw [hnn']; exact hmp
  have huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, W))))) ≫
        (hW.isoSpec.inv ≫ nn ≫ ιD i) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, W))))) ≫
        (hW.isoSpec.inv ≫ nn' ≫ ιD i) := by
    rw [← Category.assoc, ← hγ, Category.assoc, hn, ← Category.assoc _ hW.isoSpec.inv, ← hγ, Category.assoc ε.hom, hn']
  exact AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
    Γ(D₀.A, W) D.f _ hu (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak _ hU e₁ he₁ _ hv huv

end S_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_factor_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_factor_bare (solution)
