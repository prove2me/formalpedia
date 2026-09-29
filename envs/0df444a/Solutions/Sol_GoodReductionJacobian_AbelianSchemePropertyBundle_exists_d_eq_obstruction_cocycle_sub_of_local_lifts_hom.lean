-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1b861327-b70c-5025-88ec-9e32d03b8f0b

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 320000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom.GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw"
namespace P2mHomObWD
p2m_open "GoodReductionJacobian"

def linOfAdd {R : Type*} [Semiring R] {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    (φ : M₁ →+ M₂) (h : ∀ (r : R) (x : M₁), φ (r • x) = r • φ x) : M₁ →ₗ[R] M₂ :=
  { toFun := φ, map_add' := φ.map_add, map_smul' := h }

@[scoped simp] theorem linOfAdd_apply {R : Type*} [Semiring R] {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (φ : M₁ →+ M₂) (h : ∀ (r : R) (x : M₁), φ (r • x) = r • φ x) (x : M₁) :
    linOfAdd φ h x = φ x := rfl

theorem exists_pointDerivations_pi {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] (ev : A →+* k)
    {W : Type*} [AddCommGroup W] [Module k W] {ι' : Type*} {N : ι' → Type*} {M : ι' → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    (D : ∀ i, ↥(Algebra.PointDerivations k A ev (W →ₗ[k] N i))) (L : ∀ i, N i →ₗ[k] M i) :
    ∃ B : ↥(Algebra.PointDerivations k A ev (W →ₗ[k] ((i : ι') → M i))),
      ∀ (a : A) (w : W) (i : ι'), B.1 a w i = L i ((D i).1 a w) := by
  let B₀ : A →ₗ[k] (W →ₗ[k] ((i : ι') → M i)) :=
    { toFun := fun a => LinearMap.pi fun i => (L i).comp ((D i).1 a)
      map_add' := fun a a' => by
        apply LinearMap.ext; intro w; funext i
        simp only [LinearMap.pi_apply, LinearMap.comp_apply, map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro w; funext i
        simp only [LinearMap.pi_apply, LinearMap.comp_apply, map_smul, LinearMap.smul_apply, Pi.smul_apply,
          RingHom.id_apply] }
  refine ⟨⟨B₀, fun a a' => ?_⟩, fun a w i => rfl⟩
  apply LinearMap.ext; intro w; funext i
  show L i ((D i).1 (a * a') w) = (ev a • B₀ a' + ev a' • B₀ a) w i
  rw [(D i).2 a a']
  simp only [B₀, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply, LinearMap.comp_apply]

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem specMap_res_comp_isoSpec_inv {X : Scheme.{u}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ X.homOfLE h := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact IsAffineOpen.map_fromSpec hU hV (homOfLE h).op

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

theorem specMap_mk_comp_eq_of_isTangentOfPair {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} {u v : Spec (CommRingCat.of C) ⟶ Y} {w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y}
    (h : IsTangentOfPair I V ι C u v w) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v := by
  obtain ⟨ϑ, _, φ, hu, hv, _⟩ := h
  rw [← hu, ← hv, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact x.2

theorem specMap_mk_comp_eq_of_isTangentCoordsOfPairAt {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} {u v : Spec (CommRingCat.of C) ⟶ Y}
    {Ak : Scheme.{u}} {xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))} {Lk : RelativeGroupLaw (ResidueField T') xk}
    {ak : Ak ⟶ Y} {Ue : Ak.Opens}
    {c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))}
    (h : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v := by
  obtain ⟨w₀, hw₀, w₁, hpair, -, -⟩ := h
  exact specMap_mk_comp_eq_of_isTangentOfPair I V ι C hpair

end GoodReductionJacobian.P2mHomObWD
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom.GoodReductionJacobian P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom.GoodReductionJacobian.P2mHomObWD"
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom.GoodReductionJacobian"

open GoodReductionJacobian.P2mHomObWD

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))

    {A₀' : Scheme.{u}} (f₀' : A₀' ⟶ Spec (CommRingCat.of T)) (L₀' : RelativeGroupLaw T f₀') (hc₀' : L₀'.IsCommutative)
    (h₀' : AbelianSchemePropertyBundle T f₀')
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of T')) (hs' : Smooth f') (hp' : IsProper f')
    (g' : A₀' ⟶ A') (hg' : IsPullback g' f₀' f' (Spec.map (CommRingCat.ofHom π)))
    (e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f')
    (he' : Spec.map (CommRingCat.ofHom π) ≫ e'.1 = (L₀'.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g')

    (u₀ : A₀ ⟶ A₀') (hu₀ : u₀ ≫ f₀' = f₀)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    [IsSeparated f]
    (𝒲 : A.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A')
    (hmf : ∀ i, m i ≫ f' = (𝒲.U i).ι ≫ f)
    (hmμ : ∀ i, morphismRestrict g (𝒲.U i) ≫ m i = (g ⁻¹ᵁ (𝒲.U i)).ι ≫ u₀ ≫ g')

    (m' : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A')
    (hmf' : ∀ i, m' i ≫ f' = (𝒲.U i).ι ≫ f)
    (hmμ' : ∀ i, morphismRestrict g (𝒲.U i) ≫ m' i = (g ⁻¹ᵁ (𝒲.U i)).ι ≫ u₀ ≫ g')

    {Ak' : Scheme.{u}} (fk' : Ak' ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk' : RelativeGroupLaw (ResidueField T') fk')
    (i₀' : Ak' ⟶ A₀') (hi₀' : IsPullback i₀' fk' f₀' (Spec.map (CommRingCat.ofHom ρ)))
    (Ue' : Ak'.Opens) (hUe' : IsAffineOpen Ue')
    (e₁' : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue' : Scheme.{u})) (he₁' : e₁' ≫ Ue'.ι = (Lk'.one (𝟙 _)).1)

    {Ak : Scheme.{u}} (bk : Ak ⟶ A) [IsAffineHom bk] (yk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hbk : IsPullback bk yk f (Spec.map (CommRingCat.ofHom (residue T'))))
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom f (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s)) ≃+* Γ(Ak, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(A, 𝒲.inter s)),
      letI := algebraOfHom f (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Ak.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom f (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(A, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Ak, (𝒲.comap bk).inter s) a)

    (c : letI := algebraOfHom fk' Ue'
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 1)))
    (hc : letI := algebraOfHom fk' Ue'
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom f (𝒲.inter s)
        ∃ cs : Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk' Lk' (i₀' ≫ g') Ue' cs ∧
          ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s))
    (c' : letI := algebraOfHom fk' Ue'
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 1)))
    (hc' : letI := algebraOfHom fk' Ue'
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom f (𝒲.inter s)
        ∃ cs : Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 0) ≫ m' (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 1) ≫ m' (s.1 1))
            fk' Lk' (i₀' ≫ g') Ue' cs ∧
          ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c'.1 a ξ s)) :
    letI := algebraOfHom fk' Ue'
    ∃ b : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 0)),
      ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit yk).d (𝒲.comap bk) 0 (b.1 a ξ) = c.1 a ξ - c'.1 a ξ := by
  classical

  haveI hflat : Flat f := by haveI := hs; infer_instance
  have hres : Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom π)
      = Spec.map (CommRingCat.ofHom (residue T')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have hak' : IsPullback (i₀' ≫ g') fk' f' (Spec.map (CommRingCat.ofHom (residue T'))) := by
    rw [← hres]; exact hi₀'.paste_horiz hg'
  letI instUe := algebraOfHom fk' Ue'
  have haff : ∀ {n : ℕ} (s : 𝒲.Idx n), IsAffineOpen (𝒲.inter s) := fun s =>
    Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s
  have hU : ∀ i : 𝒲.ι, IsAffineOpen (𝒲.U i) := fun i => 𝒲.isAffineOpen i

  let u : ∀ i : 𝒲.ι, Spec (CommRingCat.of Γ(A, 𝒲.U i)) ⟶ A' := fun i => (hU i).isoSpec.inv ≫ m i
  let u' : ∀ i : 𝒲.ι, Spec (CommRingCat.of Γ(A, 𝒲.U i)) ⟶ A' := fun i => (hU i).isoSpec.inv ≫ m' i
  have hu_of : ∀ (i : 𝒲.ι) (mm : (↑(𝒲.U i) : Scheme.{u}) ⟶ A'), mm ≫ f' = (𝒲.U i).ι ≫ f →
      (letI := algebraOfHom f (𝒲.U i);
        ((hU i).isoSpec.inv ≫ mm) ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.U i)))) := by
    intro i mm hmm
    letI := algebraOfHom f (𝒲.U i)
    rw [← fromSpec_comp_eq f (hU i), ← IsAffineOpen.isoSpec_inv_ι, Category.assoc, Category.assoc, hmm]
  have hu : ∀ i, (letI := algebraOfHom f (𝒲.U i);
      u i ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.U i)))) := fun i => hu_of i (m i) (hmf i)
  have hu' : ∀ i, (letI := algebraOfHom f (𝒲.U i);
      u' i ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.U i)))) := fun i => hu_of i (m' i) (hmf' i)

  have huu' : ∀ i, (letI := algebraOfHom f (𝒲.U i);
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, 𝒲.U i))))) ≫ u i
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, 𝒲.U i))))) ≫ u' i) := by
    intro i
    letI := algebraOfHom f (𝒲.U i)
    obtain ⟨-, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq π hπ hker
      f f₀ g hg (𝒲.U i) (hU i)
    have hε' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, 𝒲.U i)))))
        ≫ (hU i).isoSpec.inv = ε.hom ≫ (g ∣_ 𝒲.U i) := by
      rw [← hε, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have key : ∀ mm : (↑(𝒲.U i) : Scheme.{u}) ⟶ A',
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, 𝒲.U i)))))
          ≫ (hU i).isoSpec.inv ≫ mm = ε.hom ≫ (g ∣_ 𝒲.U i) ≫ mm := fun mm => by
      rw [← Category.assoc, hε', Category.assoc]
    show Spec.map _ ≫ (hU i).isoSpec.inv ≫ m i = Spec.map _ ≫ (hU i).isoSpec.inv ≫ m' i
    rw [key, key, hmμ i, hmμ' i]
  have hδ : ∀ i, (letI := algebraOfHom f (𝒲.U i);
      ∃ δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(A, 𝒲.U i)))),
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.U i) (u i) (u' i) fk' Lk' (i₀' ≫ g') Ue'
          (fun a => (δ : Γ(Ak', Ue') →ₗ[ResidueField T']
            (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(A, 𝒲.U i)))) a)) := by
    intro i
    letI := algebraOfHom f (𝒲.U i)
    haveI : Module.Flat T' Γ(A, 𝒲.U i) := flat_sections f (hU i)
    exact AlgebraicGeometry.SmallExtension.exists_pointDerivations_isTangentCoordsOfPairAt_of_flat (RingHom.ker π) hI hsmall
      V ι hι hιI Γ(A, 𝒲.U i) f' (u i) (hu i) (u' i) (hu' i) (huu' i) fk' Lk' (i₀' ≫ g') hak' Ue' hUe' e₁' he₁'
  choose δ hδ using hδ

  have hsmul : ∀ (t : (𝒲.comap bk).Idx 0) (r : ResidueField T')
      (y : letI := algebraOfHom f (𝒲.inter t); ResidueField T' ⊗[T'] Γ(A, 𝒲.inter t)),
      (show (OModulePresheaf.unit yk).obj ((𝒲.comap bk).inter t) from σ t (r • y))
        = r • (show (OModulePresheaf.unit yk).obj ((𝒲.comap bk).inter t) from σ t y) := by
    intro t r y
    letI := algebraOfHom f (𝒲.inter t)
    letI := algebraOfHom yk ((𝒲.comap bk).inter t)
    rw [Algebra.smul_def r y, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      hσ₂ t r]
    rfl
  let σL : ∀ t : (𝒲.comap bk).Idx 0,
      (letI := algebraOfHom f (𝒲.inter t); ResidueField T' ⊗[T'] Γ(A, 𝒲.inter t)) →ₗ[ResidueField T']
        (OModulePresheaf.unit yk).obj ((𝒲.comap bk).inter t) := fun t =>
    linOfAdd (σ t).toRingHom.toAddMonoidHom (hsmul t)
  let rL : ∀ t : (𝒲.comap bk).Idx 0,
      (letI := algebraOfHom f (𝒲.U (t.1 0)); ResidueField T' ⊗[T'] Γ(A, 𝒲.U (t.1 0))) →ₗ[ResidueField T']
        (letI := algebraOfHom f (𝒲.inter t); ResidueField T' ⊗[T'] Γ(A, 𝒲.inter t)) := fun t =>
    letI := algebraOfHom f (𝒲.U (t.1 0)); letI := algebraOfHom f (𝒲.inter t)
    (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f (𝒲.inter_le t 0))).toLinearMap
  obtain ⟨B, hB⟩ := exists_pointDerivations_pi
    ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
    (M := fun t : (𝒲.comap bk).Idx 0 => (OModulePresheaf.unit yk).obj ((𝒲.comap bk).inter t))
    (fun t : (𝒲.comap bk).Idx 0 => δ (t.1 0)) (fun t => -((σL t).comp (rL t)))
  refine ⟨B, fun a ξ => ?_⟩
  funext s

  letI := algebraOfHom f (𝒲.inter s)
  letI := algebraOfHom yk ((𝒲.comap bk).inter s)
  haveI : Module.Flat T' Γ(A, 𝒲.inter s) := flat_sections f (haff s)
  have hus : (haff s).fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.inter s))) :=
    fromSpec_comp_eq f (haff s)
  have hιs : (haff s).isoSpec.inv ≫ (𝒲.inter s).ι = (haff s).fromSpec := IsAffineOpen.isoSpec_inv_ι _

  let ρr : ∀ j : Fin 2, Γ(A, 𝒲.U (s.1 j)) →+* Γ(A, 𝒲.inter s) := fun j =>
    (A.presheaf.map (homOfLE (𝒲.inter_le s j)).op).hom
  have hρr : ∀ j : Fin 2, (letI := algebraOfHom f (𝒲.U (s.1 j)); (restrictAlgHom f (𝒲.inter_le s j)).toRingHom = ρr j) :=
    fun j => rfl
  have hSpec_res : ∀ j : Fin 2, Spec.map (CommRingCat.ofHom (ρr j)) = Spec.map (A.presheaf.map (homOfLE (𝒲.inter_le s j)).op) :=
    fun j => rfl

  let x : ∀ j : Fin 2, Spec (CommRingCat.of Γ(A, 𝒲.inter s)) ⟶ A' := fun j =>
    (haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s j) ≫ m (s.1 j)
  let x' : ∀ j : Fin 2, Spec (CommRingCat.of Γ(A, 𝒲.inter s)) ⟶ A' := fun j =>
    (haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s j) ≫ m' (s.1 j)
  have hx_of : ∀ (j : Fin 2) (mm : (↑(𝒲.U (s.1 j)) : Scheme.{u}) ⟶ A'), mm ≫ f' = (𝒲.U (s.1 j)).ι ≫ f →
      ((haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s j) ≫ mm) ≫ f'
        = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.inter s))) := by
    intro j mm hmm
    rw [← hus, ← hιs, ← Scheme.homOfLE_ι A (𝒲.inter_le s j)]
    simp only [Category.assoc]
    rw [hmm]
  have hx : ∀ j, x j ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.inter s))) :=
    fun j => hx_of j (m (s.1 j)) (hmf (s.1 j))
  have hx' : ∀ j, x' j ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.inter s))) :=
    fun j => hx_of j (m' (s.1 j)) (hmf' (s.1 j))
  have hxu_of : ∀ (j : Fin 2) (mm : (↑(𝒲.U (s.1 j)) : Scheme.{u}) ⟶ A'),
      Spec.map (CommRingCat.ofHom (ρr j)) ≫ ((hU (s.1 j)).isoSpec.inv ≫ mm)
        = (haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s j) ≫ mm := by
    intro j mm
    rw [← Category.assoc, hSpec_res, specMap_res_comp_isoSpec_inv (hU (s.1 j)) (haff s) (𝒲.inter_le s j), Category.assoc]
  have hxu : ∀ j, Spec.map (CommRingCat.ofHom (ρr j)) ≫ u (s.1 j) = x j := fun j => hxu_of j (m (s.1 j))
  have hxu' : ∀ j, Spec.map (CommRingCat.ofHom (ρr j)) ≫ u' (s.1 j) = x' j := fun j => hxu_of j (m' (s.1 j))

  let β : ∀ j : Fin 2, Γ(Ak', Ue') →
      (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(A, 𝒲.inter s))) := fun j a =>
    (letI := algebraOfHom f (𝒲.U (s.1 j));
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f (𝒲.inter_le s j))).toLinearMap
        ∘ₗ ((δ (s.1 j)).1 a))
  have hcor : ∀ j : Fin 2,
      IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s) (x j) (x' j) fk' Lk' (i₀' ≫ g') Ue' (β j) := by
    intro j
    letI := algebraOfHom f (𝒲.U (s.1 j))
    have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      Γ(A, 𝒲.U (s.1 j)) Γ(A, 𝒲.inter s) (restrictAlgHom f (𝒲.inter_le s j)) (u (s.1 j)) (u' (s.1 j))
      fk' Lk' (i₀' ≫ g') Ue' _ (hδ (s.1 j))
    rwa [hρr, hxu, hxu'] at h

  obtain ⟨cs, hcs, hσcs⟩ := hc s
  obtain ⟨cs', hcs', hσcs'⟩ := hc' s

  have h01 := specMap_mk_comp_eq_of_isTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s) hcs
  have h0'1' := specMap_mk_comp_eq_of_isTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s) hcs'
  have h00' := specMap_mk_comp_eq_of_isTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s) (hcor 0)
  have h11' := specMap_mk_comp_eq_of_isTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s) (hcor 1)

  obtain ⟨γ, hγ⟩ := AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt (RingHom.ker π) hI hsmall V ι hι hιI
    Γ(A, 𝒲.inter s) f' (x 0) (hx 0) fk' Lk' (i₀' ≫ g') hak' Ue' hUe' e₁' he₁' (x' 1) (hx' 1) (h01.trans h11')
  have add1 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add (RingHom.ker π) hI hsmall V ι hι hιI
    Γ(A, 𝒲.inter s) f' (x 0) (x 1) (x' 1) (hx 0) (hx 1) (hx' 1) h01 h11' fk' Lk' (i₀' ≫ g') hak' Ue' hUe' e₁' he₁'
    cs (β 1) γ hcs (hcor 1) hγ
  have add2 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add (RingHom.ker π) hI hsmall V ι hι hιI
    Γ(A, 𝒲.inter s) f' (x 0) (x' 0) (x' 1) (hx 0) (hx' 0) (hx' 1) h00' h0'1' fk' Lk' (i₀' ≫ g') hak' Ue' hUe' e₁' he₁'
    (β 0) cs' γ (hcor 0) hcs' hγ
  have hsq : cs + β 1 = β 0 + cs' := add1.symm.trans add2
  have hsq' := congrArg (fun φ => φ a ξ) hsq
  simp only [β, Pi.add_apply, LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at hsq'

  have hbres : ∀ (t : 𝒲.Idx 0) (i : 𝒲.ι) (e : t.1 0 = i) (ht : (𝒲.comap bk).inter s ≤ (𝒲.comap bk).inter t)
      (ht' : 𝒲.inter s ≤ 𝒲.inter t) (hi : 𝒲.inter s ≤ 𝒲.U i),
      (OModulePresheaf.unit yk).res ht (B.1 a ξ t) = -(σ s ((letI := algebraOfHom f (𝒲.U i);
        Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f hi))
          ((δ i).1 a ξ))) := by
    intro t i e ht ht' hi
    subst e
    letI := algebraOfHom f (𝒲.inter t)
    letI := algebraOfHom yk ((𝒲.comap bk).inter t)
    letI := algebraOfHom f (𝒲.U (t.1 0))
    have hσn : ∀ y : ResidueField T' ⊗[T'] Γ(A, 𝒲.inter t),
        σ s (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f ht') y)
          = (Ak.presheaf.map (homOfLE ht).op).hom (σ t y) := fun y =>
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
        f bk yk ht' (𝒲.comap_inter_le bk t) (𝒲.comap_inter_le bk s) ht
        (σ t).toRingHom (σ s).toRingHom
        (fun z => hσ₁ t z) (fun r => hσ₂ t r) (fun z => hσ₁ s z) (fun r => hσ₂ s r) y
    have hcm : ∀ y : ResidueField T' ⊗[T'] Γ(A, 𝒲.U (t.1 0)),
        Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f ht')
            (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f (𝒲.inter_le t 0)) y)
          = Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f hi) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul r z =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact congrArg (fun w => r ⊗ₜ[T'] w) (Scheme.TwoAffineOpenCover.res_res (𝒲.inter_le t 0) ht' z)
    rw [hB a ξ t]
    show (Ak.presheaf.map (homOfLE ht).op).hom
        (-(σ t (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f (𝒲.inter_le t 0))
          ((δ (t.1 0)).1 a ξ)))) = _
    rw [map_neg, ← hσn, hcm]

  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, Pi.sub_apply]
  rw [hbres ((𝒲.comap bk).face s 0) (s.1 1) rfl ((𝒲.comap bk).inter_le_inter_face s 0) (𝒲.inter_le_inter_face s 0)
      (𝒲.inter_le s 1),
    hbres ((𝒲.comap bk).face s 1) (s.1 0) rfl ((𝒲.comap bk).inter_le_inter_face s 1) (𝒲.inter_le_inter_face s 1)
      (𝒲.inter_le s 0),
    ← hσcs a ξ, ← hσcs' a ξ]
  have key := congrArg (σ s) hsq'
  rw [map_add, map_add] at key
  show -(σ s _) + -(-(σ s _)) = σ s (cs a ξ) - σ s (cs' a ξ)
  rw [neg_neg, neg_add_eq_sub, sub_eq_sub_iff_add_eq_add]
  exact key.symm

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom (solution)
