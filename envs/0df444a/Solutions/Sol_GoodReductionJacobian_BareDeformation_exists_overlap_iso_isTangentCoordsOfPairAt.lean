-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_overlap_iso_isTangentCoordsOfPairAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/609fdbc8-294f-5130-9e66-89336f73e0aa

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt_of_pointDerivations
import Theorems.Thm_AlgebraicGeometry_exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_overlap_iso_isTangentCoordsOfPairAt

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
    {q : ℕ} [Fact q.Prime]
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    (hq : IsNilpotent ((q : ℕ) : B))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (F : MvFormalGroup 2 B) [F.IsComm]
    (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates (F.map (algebraMap B B₁)) θ₁)
    (hinf₁ : ∀ (C : Type) [CommRing C] [Algebra B₁ C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B₁) C) f₁),
      nsmulPt L₁ (Scheme.specOver (𝒪 := B₁) C) (q ^ m) P = L₁.one (Scheme.specOver (𝒪 := B₁) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L₁.IsInfinitesimal J P)
    (hheight : ∀ (k : Type) [Field k] (ρ : B →+* k), Function.Surjective ρ →
      Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range ((F.map ρ).nthSeries q))) = q ^ 4)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (he₀ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)

    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (σ : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s))
    (hσ₁ : ∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
        ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
          (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x))
    (hσ₂ : ∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
      σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a)
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))
    (s : 𝒰.Idx 1) :
    ∃ τs : ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      τs.hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f ∧
      (D₀.g ∣_ 𝒰.inter s) ≫ τs.hom = D₀.g ∣_ 𝒰.inter s ∧
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
        AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
          ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
          ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ τs.hom ≫ (𝒰.inter s).ι)
          (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
        ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
          σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s := by
  classical
  letI instC : Algebra B Γ(D₀.A, 𝒰.inter s) := algebraOfHom D₀.f (𝒰.inter s)
  letI instE : Algebra (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
  letI instS : Algebra (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) :=
    algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
  have hUs : IsAffineOpen (𝒰.inter s) := Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s
  haveI : Smooth D₀.f := D₀.bundle.smooth
  haveI : Module.Flat B Γ(D₀.A, 𝒰.inter s) := RG1Aux.flat_sections D₀.f (𝒰.inter s) hUs
  have hI2 : RingHom.ker (algebraMap B B₁) * RingHom.ker (algebraMap B B₁) = ⊥ :=
    le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
  have hu : hUs.fromSpec ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) := RG1Aux.fromSpec_comp_eq D₀.f (𝒰.inter s) hUs
  have hak : IsPullback (pullback.fst D₀.f (specMap B (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))) D₀.f
      (Spec.map (CommRingCat.ofHom (residue B))) :=
    IsPullback.of_hasPullback D₀.f (specMap B (ResidueField B))
  have hUe : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) := (𝒰.baseChange D₀.f (ResidueField B)).isAffineOpen i₀

  have hσsmul : ∀ (r : (ResidueField B)) (y : Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s)),
      (σ s).symm (r • y) = r • (σ s).symm y := by
    intro r y
    apply (σ s).injective
    rw [RingEquiv.apply_symm_apply, Algebra.smul_def, Algebra.smul_def, map_mul, RingEquiv.apply_symm_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hσ₂]
  let δ₀ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))) := fun a =>
    { toFun := fun ξ => (σ s).symm (c.1 a ξ s)
      map_add' := fun ξ ξ' => by
        rw [(c.1 a).map_add ξ ξ']
        change (σ s).symm (c.1 a ξ s + c.1 a ξ' s) = _
        exact (σ s).symm.map_add _ _
      map_smul' := fun r ξ => by
        rw [(c.1 a).map_smul r ξ, RingHom.id_apply]
        change (σ s).symm (r • c.1 a ξ s) = r • (σ s).symm (c.1 a ξ s)
        exact hσsmul r _ }
  have hδ₀ : ∀ a ξ, δ₀ a ξ = (σ s).symm (c.1 a ξ s) := fun a ξ => rfl
  let δ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))) :=
    { toFun := δ₀
      map_add' := fun a b => LinearMap.ext fun ξ => by
        rw [LinearMap.add_apply, hδ₀, hδ₀, hδ₀, c.1.map_add a b]
        change (σ s).symm (c.1 a ξ s + c.1 b ξ s) = _
        exact (σ s).symm.map_add _ _
      map_smul' := fun r a => LinearMap.ext fun ξ => by
        rw [LinearMap.smul_apply, hδ₀, hδ₀, c.1.map_smul r a, RingHom.id_apply]
        change (σ s).symm (r • c.1 a ξ s) = r • (σ s).symm (c.1 a ξ s)
        exact hσsmul r _ }
  have hδapply : ∀ a, δ a = δ₀ a := fun a => rfl
  have hδ : δ ∈ Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))
      ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom)
      (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))) := by
    intro a b
    refine LinearMap.ext fun ξ => ?_
    rw [hδapply, hδapply, hδapply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hδ₀, hδ₀, hδ₀]
    rw [c.2 a b, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    change (σ s).symm (((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) a • c.1 b ξ s + ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) b • c.1 a ξ s) = _
    have e1 := hσsmul (((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) a) (c.1 b ξ s)
    have e2 := hσsmul (((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) b) (c.1 a ξ s)
    rw [← e1, ← e2]
    exact (σ s).symm.map_add _ _

  obtain ⟨v, hv, hvu, hcoords⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt_of_pointDerivations (RingHom.ker (algebraMap B B₁)) hI hsmall
      V ι hι hιI Γ(D₀.A, 𝒰.inter s) D₀.f hUs.fromSpec hu (pullback.snd D₀.f (specMap B (ResidueField B)))
      (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hUe e₁ he₁ ⟨δ, hδ⟩

  obtain ⟨τs, h1, h2, h3⟩ :=
    AlgebraicGeometry.exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq hπ hI2 D₀.f f₁ D₀.g D₀.cart (𝒰.inter s) hUs v hv hvu
  refine ⟨τs, h2, h3, fun a => δ a, ?_, ?_⟩
  · rw [h1]; exact hcoords
  · intro a ξ
    show σ s (δ₀ a ξ) = _
    rw [hδ₀, RingEquiv.apply_symm_apply]

end S_GoodReductionJacobian_BareDeformation_exists_overlap_iso_isTangentCoordsOfPairAt
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_overlap_iso_isTangentCoordsOfPairAt (solution)
