-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_iff_forall_mem_range_d_of_local_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3f350508-c46c-51d1-8b43-c77646c69155

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_of_pointDerivations_coboundary
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_iff_forall_mem_range_d_of_local_lifts

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 320000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_iff_forall_mem_range_d_of_local_lifts.GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw AbelianSchemePropertyBundle.exists_hom_lift_of_pointDerivations_coboundary AbelianSchemePropertyBundle.exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom"
namespace P2mLiftIffClassZero
p2m_open "GoodReductionJacobian"

theorem exists_linear_section {k : Type*} [Field k] {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (d : M →ₗ[k] N) :
    ∃ G : N →ₗ[k] M, ∀ y : N, y ∈ LinearMap.range d → d (G y) = y := by
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range d).subtype
    (Submodule.ker_subtype _)
  obtain ⟨G, hG⟩ := Module.projective_lifting_property d.rangeRestrict p d.surjective_rangeRestrict
  refine ⟨G, fun y hy => ?_⟩
  have h1 : p y = ⟨y, hy⟩ := by
    have h := LinearMap.congr_fun hp ⟨y, hy⟩
    simpa using h
  have h2 : d.rangeRestrict (G y) = p y := LinearMap.congr_fun hG y
  have h3 := congrArg Subtype.val (h2.trans h1)
  exact h3

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

end GoodReductionJacobian.P2mLiftIffClassZero

open GoodReductionJacobian.P2mLiftIffClassZero

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
    :
    letI := algebraOfHom fk' Ue'
    (∃ u : A ⟶ A', u ≫ f' = f ∧ g ≫ u = u₀ ≫ g') ↔
      ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        c.1 a ξ ∈ LinearMap.range ((OModulePresheaf.unit yk).d (𝒲.comap bk) 0) := by
  classical
  letI instUe := algebraOfHom fk' Ue'
  haveI hflat : Flat f := by haveI := hs; infer_instance
  have hres : Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom π)
      = Spec.map (CommRingCat.ofHom (residue T')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have hak' : IsPullback (i₀' ≫ g') fk' f' (Spec.map (CommRingCat.ofHom (residue T'))) := by
    rw [← hres]; exact hi₀'.paste_horiz hg'
  have haff : ∀ {n : ℕ} (s : 𝒲.Idx n), IsAffineOpen (𝒲.inter s) := fun s =>
    Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s
  constructor
  ·
    rintro ⟨u, huf, hgu⟩ a ξ
    let m' : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A' := fun i => (𝒲.U i).ι ≫ u
    have hmf' : ∀ i : 𝒲.ι, m' i ≫ f' = (𝒲.U i).ι ≫ f := fun i => by
      show ((𝒲.U i).ι ≫ u) ≫ f' = (𝒲.U i).ι ≫ f
      rw [Category.assoc, huf]
    have hmμ' : ∀ i : 𝒲.ι, morphismRestrict g (𝒲.U i) ≫ m' i = (g ⁻¹ᵁ (𝒲.U i)).ι ≫ u₀ ≫ g' := fun i => by
      show morphismRestrict g (𝒲.U i) ≫ ((𝒲.U i).ι ≫ u) = (g ⁻¹ᵁ (𝒲.U i)).ι ≫ u₀ ≫ g'
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hgu]
    have hcoords : ∀ s : 𝒲.Idx 1, letI := algebraOfHom f (𝒲.inter s)
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
          ((haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s 0) ≫ m' (s.1 0))
          ((haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s 1) ≫ m' (s.1 1))
          fk' Lk' (i₀' ≫ g') Ue' 0 := by
      intro s
      letI := algebraOfHom f (𝒲.inter s)
      haveI : Module.Flat T' Γ(A, 𝒲.inter s) := flat_sections f (haff s)
      have hwf : ((haff s).isoSpec.inv ≫ (𝒲.inter s).ι ≫ u) ≫ f'
          = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.inter s))) := by
        rw [Category.assoc, Category.assoc, huf, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
        exact fromSpec_comp_eq f (haff s)
      have hv0 : (haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s 0) ≫ m' (s.1 0)
          = (haff s).isoSpec.inv ≫ (𝒲.inter s).ι ≫ u := by
        show (haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s 0) ≫ ((𝒲.U (s.1 0)).ι ≫ u) = _
        rw [Scheme.homOfLE_ι_assoc]
      have hv1 : (haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s 1) ≫ m' (s.1 1)
          = (haff s).isoSpec.inv ≫ (𝒲.inter s).ι ≫ u := by
        show (haff s).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le s 1) ≫ ((𝒲.U (s.1 1)).ι ≫ u) = _
        rw [Scheme.homOfLE_ι_assoc]
      have hδ' := AlgebraicGeometry.SmallExtension.exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
        (RingHom.ker π) hI hsmall V ι hι hιI Γ(A, 𝒲.inter s) f' _ hwf _ hwf rfl
        fk' Lk' (i₀' ≫ g') hak' Ue' hUe' e₁' he₁'
      obtain ⟨δ, hδ⟩ := hδ'
      have hsum := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add
        (RingHom.ker π) hI hsmall V ι hι hιI Γ(A, 𝒲.inter s) f' _ _ _ hwf hwf hwf rfl rfl
        fk' Lk' (i₀' ≫ g') hak' Ue' hUe' e₁' he₁' _ _ _ hδ hδ hδ
      have hzero := left_eq_add.mp hsum
      rw [hv0, hv1, ← hzero]
      exact hδ
    have key := GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom
      T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg f₀' L₀' hc₀' h₀' f' hs' hp' g' hg' e' he' u₀ hu₀ hI ρ hρ
      V ι hι hιI 𝒲 m hmf hmμ m' hmf' hmμ' fk' Lk' i₀' hi₀' Ue' hUe' e₁' he₁' bk yk hbk σ hσ₁ hσ₂ c hc 0
      (fun s => ⟨0, hcoords s, fun a ξ => by simp <;> rfl⟩)
    obtain ⟨b, hb⟩ := key
    refine LinearMap.mem_range.mpr ⟨b.1 a ξ, ?_⟩
    rw [hb a ξ]
    simp
  ·
    intro h
    obtain ⟨G, hG⟩ := exists_linear_section ((OModulePresheaf.unit yk).d (𝒲.comap bk) 0)
    let b : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 0)) :=
      Algebra.PointDerivations.map _ (LinearMap.llcomp (ResidueField T') (Module.Dual (ResidueField T') V) _ _ G) c
    have hb : ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit yk).d (𝒲.comap bk) 0 (b.1 a ξ) = c.1 a ξ := fun a ξ =>
      hG _ (h a ξ)
    exact GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_of_pointDerivations_coboundary
      T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg f₀' L₀' hc₀' h₀' f' hs' hp' g' hg' e' he' u₀ hu₀ hI ρ hρ
      V ι hι hιI 𝒲 m hmf hmμ fk' Lk' i₀' hi₀' Ue' hUe' e₁' he₁' bk yk hbk σ hσ₁ hσ₂ c hc b hb

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_iff_forall_mem_range_d_of_local_lifts
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_iff_forall_mem_range_d_of_local_lifts (solution)
