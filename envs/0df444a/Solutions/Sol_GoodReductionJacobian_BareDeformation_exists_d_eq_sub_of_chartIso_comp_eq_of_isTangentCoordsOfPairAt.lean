-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/84e13411-f486-5fc2-a13a-c317edb22484

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

import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_eq_add_of_specMap_comp_eq
import Theorems.Thm_AlgebraicGeometry_specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 320000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt.GoodReductionJacobian IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.SmallExtension"

open scoped TensorProduct

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw BareDeformation RelativeGroupLaw.baseChange"
namespace P2mChartAutos
p2m_open "GoodReductionJacobian"

universe u

def idx0 {X : Scheme.{u}} (K : X.OrderedAffineCover) (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, fun a b hab => by
    exfalso; have ha := a.isLt; have hb := b.isLt; have := Fin.lt_def.mp hab; omega⟩

theorem inter_idx0 {X : Scheme.{u}} (K : X.OrderedAffineCover) (i : K.ι) : K.inter (idx0 K i) = K.U i :=
  le_antisymm (iInf_le _ 0) (le_iInf fun _ => le_rfl)

theorem face_zero_eq {X : Scheme.{u}} (K : X.OrderedAffineCover) (s : K.Idx 1) : K.face s 0 = idx0 K (s.1 1) := by
  apply Subtype.ext; funext x
  have hx : x = 0 := Fin.ext (by have := x.isLt; omega)
  subst hx
  show s.1 (Fin.succAbove 0 0) = s.1 1
  rfl

theorem face_one_eq {X : Scheme.{u}} (K : X.OrderedAffineCover) (s : K.Idx 1) : K.face s 1 = idx0 K (s.1 0) := by
  apply Subtype.ext; funext x
  have hx : x = 0 := Fin.ext (by have := x.isLt; omega)
  subst hx
  show s.1 (Fin.succAbove 1 0) = s.1 0
  rfl

theorem res_congr_idx {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} (F : OModulePresheaf π)
    (K : X.OrderedAffineCover) {t t' : K.Idx 0} (e : t = t') {W : X.Opens} (h : W ≤ K.inter t) (h' : W ≤ K.inter t')
    (b : F.cochain K 0) : F.res h (b t) = F.res h' (b t') := by
  subst e; rfl

theorem transport_iso {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) {U W : X.Opens} (e : W = U)
    (αW : (W : Scheme.{u}) ≅ W) (h2 : αW.hom ≫ W.ι ≫ f = W.ι ≫ f) (h3 : (g ∣_ W) ≫ αW.hom = g ∣_ W) :
    ∃ αU : (U : Scheme.{u}) ≅ U, αU.hom ≫ U.ι ≫ f = U.ι ≫ f ∧ (g ∣_ U) ≫ αU.hom = g ∣_ U ∧
      X.homOfLE e.le ≫ αU.hom = αW.hom ≫ X.homOfLE e.le := by
  subst e
  exact ⟨αW, h2, h3, by rw [Scheme.homOfLE_rfl, Category.id_comp, Category.comp_id]⟩

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

theorem exists_algHom_specMap_eq {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    (θ : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of C))
    (hθ : θ ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    ∃ ψ : C →ₐ[B] C, Spec.map (CommRingCat.ofHom ψ.toRingHom) = θ := by
  have hφ : Spec.map (Spec.preimage θ) = θ := Spec.map_preimage θ
  have hcomm : CommRingCat.ofHom (algebraMap B C) ≫ Spec.preimage θ = CommRingCat.ofHom (algebraMap B C) := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap B C) ≫ Spec.preimage θ) = Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [Spec.map_comp, hφ, hθ]
    have h2 := congrArg Spec.preimage h1
    rwa [Spec.preimage_map, Spec.preimage_map] at h2
  refine ⟨{ toRingHom := (Spec.preimage θ).hom, commutes' := fun b => ?_ }, ?_⟩
  · have := congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of C => φ.hom b) hcomm
    simpa using this
  · show Spec.map (CommRingCat.ofHom (Spec.preimage θ).hom) = θ
    rw [CommRingCat.ofHom_hom, hφ]

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

theorem tensorMap_eq_id_of_congr {B : Type u} [CommRing B] [IsLocalRing B] (I : Ideal B) (hI : I ≤ maximalIdeal B)
    {C : Type u} [CommRing C] [Algebra B C] (ψ : C →ₐ[B] C)
    (hψ : ∀ c, Ideal.Quotient.mk (I.map (algebraMap B C)) (ψ c) = Ideal.Quotient.mk (I.map (algebraMap B C)) c) :
    Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) ψ = AlgHom.id (ResidueField B) _ := by
  apply Algebra.TensorProduct.ext'
  intro a c
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply]
  have hmem : ψ c - c ∈ I.map (algebraMap B C) := by
    rw [← Ideal.Quotient.eq]; exact hψ c
  have key : ∀ y ∈ I.map (algebraMap B C), a ⊗ₜ[B] y = (0 : ResidueField B ⊗[B] C) := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => a ⊗ₜ[B] y = (0 : ResidueField B ⊗[B] C)) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨b, hb, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
        (IsLocalRing.residue_eq_zero_iff b).mpr (hI hb), zero_mul, TensorProduct.zero_tmul]
    · exact TensorProduct.tmul_zero _ _
    · intro x y _ _ hx hy; rw [TensorProduct.tmul_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, show a ⊗ₜ[B] (r * x) = ((1 : ResidueField B) ⊗ₜ[B] r) * (a ⊗ₜ[B] x) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], hx, mul_zero]
  have : a ⊗ₜ[B] ψ c - a ⊗ₜ[B] c = 0 := by rw [← TensorProduct.tmul_sub]; exact key _ hmem
  exact sub_eq_zero.mp this

end GoodReductionJacobian.P2mChartAutos

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw BareDeformation RelativeGroupLaw.baseChange"
namespace P2mChartAutos
p2m_open "GoodReductionJacobian"

section Abbrevs
variable {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
  {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}

abbrev AkS (D₀ : BareDeformation f₁ L₁ B) : Scheme.{0} := pullback D₀.f (specMap B (ResidueField B))

abbrev akS (D₀ : BareDeformation f₁ L₁ B) : AkS D₀ ⟶ D₀.A := pullback.fst D₀.f (specMap B (ResidueField B))

abbrev xkS (D₀ : BareDeformation f₁ L₁ B) : AkS D₀ ⟶ Spec (CommRingCat.of (ResidueField B)) :=
  pullback.snd D₀.f (specMap B (ResidueField B))

abbrev LkS (D₀ : BareDeformation f₁ L₁ B) : RelativeGroupLaw (ResidueField B) (xkS D₀) :=
  RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L

abbrev UkS (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover) : (AkS D₀).OrderedAffineCover :=
  𝒰.baseChange D₀.f (ResidueField B)

abbrev FS (D₀ : BareDeformation f₁ L₁ B) : OModulePresheaf (xkS D₀) := OModulePresheaf.unit (xkS D₀)
end Abbrevs

end GoodReductionJacobian.P2mChartAutos

open GoodReductionJacobian.P2mChartAutos

theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
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
    (c' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))
    (τ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D D' : BareDeformation f₁ L₁ B)
    (hD : D₀.IsRegluingBy 𝒰 τ D) (hD' : D₀.IsRegluingBy 𝒰 τ' D')
    (hτ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)
    (hτ' : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ' s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)
    (α : ∀ i : 𝒰.ι, ((↑(𝒰.U i) : Scheme.{0}) ≅ ↑(𝒰.U i)))
    (hαf : ∀ i : 𝒰.ι, (α i).hom ≫ (𝒰.U i).ι ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hαg : ∀ i : 𝒰.ι, (D₀.g ∣_ 𝒰.U i) ≫ (α i).hom = D₀.g ∣_ 𝒰.U i)
    (αr : ∀ (s : 𝒰.Idx 1) (_ : Fin 2), ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hαr : ∀ (s : 𝒰.Idx 1) (j : Fin 2),
      (αr s j).hom ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom)
    (hcomm : ∀ s : 𝒰.Idx 1, (αr s 0).hom ≫ (τ' s).hom = (τ s).hom ≫ (αr s 1).hom) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      ∃ b : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 0,
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0 b =
          (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
          - (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ  := by
  classical

  haveI hflatf : Flat D₀.f := by haveI := D₀.bundle.smooth; infer_instance
  have hak : IsPullback (akS D₀) (xkS D₀) D₀.f (Spec.map (CommRingCat.ofHom (residue B))) := by
    rw [← IsLocalRing.ResidueField.algebraMap_eq]; exact IsPullback.of_hasPullback _ _
  have hUe : IsAffineOpen ((UkS D₀ 𝒰).U i₀) := (UkS D₀ 𝒰).isAffineOpen i₀
  letI instUe := algebraOfHom (xkS D₀) ((UkS D₀ 𝒰).U i₀)
  have haff : ∀ {i : ℕ} (s : 𝒰.Idx i), IsAffineOpen (𝒰.inter s) := fun s => Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s
  have hU : ∀ i : 𝒰.ι, IsAffineOpen (𝒰.U i) := fun i => 𝒰.isAffineOpen i
  intro a ξ

  let v : ∀ i : 𝒰.ι, Spec (CommRingCat.of Γ(D₀.A, 𝒰.U i)) ⟶ D₀.A := fun i => (hU i).isoSpec.inv ≫ (α i).hom ≫ (𝒰.U i).ι
  have hv : ∀ i, (letI := algebraOfHom D₀.f (𝒰.U i)
      v i ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.U i)))) := fun i => by
    letI := algebraOfHom D₀.f (𝒰.U i)
    rw [← fromSpec_comp_eq D₀.f (hU i), ← IsAffineOpen.isoSpec_inv_ι]
    simp only [v, Category.assoc]
    rw [hαf i]
  have huv : ∀ i, (letI := algebraOfHom D₀.f (𝒰.U i)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.U i)))))
          ≫ (hU i).fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.U i)))))
          ≫ v i) := fun i =>
    AlgebraicGeometry.specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq hπ D₀.f f₁ D₀.g D₀.cart
      (𝒰.U i) (hU i) (α i).hom (hαg i)
  have hbco : ∀ i, (letI := algebraOfHom D₀.f (𝒰.U i)
      ∃ bc : Γ(AkS D₀, (UkS D₀ 𝒰).U i₀) →
          (Module.Dual (ResidueField B) V →ₗ[ResidueField B] (ResidueField B ⊗[B] Γ(D₀.A, 𝒰.U i))),
        IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.U i) (hU i).fromSpec (v i)
          (xkS D₀) (LkS D₀) (akS D₀) ((UkS D₀ 𝒰).U i₀) bc) := fun i => by
    letI := algebraOfHom D₀.f (𝒰.U i)
    haveI : Module.Flat B Γ(D₀.A, 𝒰.U i) := flat_sections D₀.f (hU i)
    exact AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
      Γ(D₀.A, 𝒰.U i) D₀.f (hU i).fromSpec (fromSpec_comp_eq D₀.f (hU i)) (xkS D₀) (LkS D₀) (akS D₀) hak
      ((UkS D₀ 𝒰).U i₀) hUe e₁ he₁ (v i) (hv i) (huv i)
  choose bco hbco using hbco

  have hCF := fun t : 𝒰.Idx 0 =>
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter D₀.f 𝒰 (ResidueField B) t
  choose σ0 hσ0₁ hσ0₂ using hCF
  let b : (FS D₀).cochain (UkS D₀ 𝒰) 0 := fun t =>
    -(σ0 t ((letI := algebraOfHom D₀.f (𝒰.U (t.1 0)); letI := algebraOfHom D₀.f (𝒰.inter t);
      Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒰.inter_le t 0)))
        (bco (t.1 0) a ξ)))
  refine ⟨b, ?_⟩
  funext s

  letI := algebraOfHom D₀.f (𝒰.inter s)
  letI := algebraOfHom (xkS D₀) ((UkS D₀ 𝒰).inter s)
  haveI : Module.Flat B Γ(D₀.A, 𝒰.inter s) := flat_sections D₀.f (haff s)
  have hus : (haff s).fromSpec ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) :=
    fromSpec_comp_eq D₀.f (haff s)
  have hιs : (haff s).isoSpec.inv ≫ (𝒰.inter s).ι = (haff s).fromSpec := IsAffineOpen.isoSpec_inv_ι _

  let ρ : ∀ j : Fin 2, Γ(D₀.A, 𝒰.U (s.1 j)) →+* Γ(D₀.A, 𝒰.inter s) := fun j =>
    (D₀.A.presheaf.map (homOfLE (𝒰.inter_le s j)).op).hom
  have hρ : ∀ j : Fin 2, (letI := algebraOfHom D₀.f (𝒰.U (s.1 j)); (restrictAlgHom D₀.f (𝒰.inter_le s j)).toRingHom = ρ j) :=
    fun j => rfl
  have hSpec_res : ∀ j : Fin 2, Spec.map (CommRingCat.ofHom (ρ j)) = Spec.map (D₀.A.presheaf.map (homOfLE (𝒰.inter_le s j)).op) :=
    fun j => rfl
  have hres_u : ∀ j : Fin 2, Spec.map (CommRingCat.ofHom (ρ j)) ≫ (hU (s.1 j)).fromSpec = (haff s).fromSpec := fun j => by
    rw [hSpec_res]; exact IsAffineOpen.map_fromSpec _ _ _

  let vA : ∀ j : Fin 2, Spec (CommRingCat.of Γ(D₀.A, 𝒰.inter s)) ⟶ D₀.A := fun j =>
    (haff s).isoSpec.inv ≫ (αr s j).hom ≫ (𝒰.inter s).ι
  have hvA : ∀ j : Fin 2, Spec.map (CommRingCat.ofHom (ρ j)) ≫ v (s.1 j) = vA j := fun j => by
    calc Spec.map (CommRingCat.ofHom (ρ j)) ≫ v (s.1 j)
        = (Spec.map (CommRingCat.ofHom (ρ j)) ≫ (hU (s.1 j)).isoSpec.inv) ≫ (α (s.1 j)).hom ≫ (𝒰.U (s.1 j)).ι := by
            simp only [v, Category.assoc]
      _ = (haff s).isoSpec.inv ≫ (D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom) ≫ (𝒰.U (s.1 j)).ι := by
            rw [hSpec_res, specMap_res_comp_isoSpec_inv (hU (s.1 j)) (haff s) (𝒰.inter_le s j)]; simp only [Category.assoc]
      _ = (haff s).isoSpec.inv ≫ ((αr s j).hom ≫ D₀.A.homOfLE (𝒰.inter_le s j)) ≫ (𝒰.U (s.1 j)).ι := by rw [hαr s j]
      _ = vA j := by simp only [vA, Category.assoc, Scheme.homOfLE_ι]
  have hαrf : ∀ j : Fin 2, (αr s j).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f := fun j => by
    rw [← Scheme.homOfLE_ι D₀.A (𝒰.inter_le s j)]
    simp only [Category.assoc]
    rw [← Category.assoc, hαr s j, Category.assoc, hαf (s.1 j)]
  have hvAB : ∀ j : Fin 2, vA j ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) := fun j => by
    rw [← hus, ← hιs]; simp only [vA, Category.assoc]; rw [hαrf j]

  have hcor : ∀ j : Fin 2, (letI := algebraOfHom D₀.f (𝒰.U (s.1 j))
      IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s) (haff s).fromSpec (vA j)
        (xkS D₀) (LkS D₀) (akS D₀) ((UkS D₀ 𝒰).U i₀)
        (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B))
          (restrictAlgHom D₀.f (𝒰.inter_le s j))).toLinearMap ∘ₗ (bco (s.1 j) x))) :=
      fun j => by
    letI := algebraOfHom D₀.f (𝒰.U (s.1 j))
    have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
      Γ(D₀.A, 𝒰.U (s.1 j)) Γ(D₀.A, 𝒰.inter s) (restrictAlgHom D₀.f (𝒰.inter_le s j)) (hU (s.1 j)).fromSpec (v (s.1 j))
      (xkS D₀) (LkS D₀) (akS D₀) ((UkS D₀ 𝒰).U i₀) _ (hbco (s.1 j))
    rwa [hρ, hres_u, hvA] at h

  obtain ⟨cs, hcs, hσcs⟩ := hτ s
  obtain ⟨cs', hcs', hσcs'⟩ := hτ' s
  have hvT'B : ((haff s).isoSpec.inv ≫ (τ' s).hom ≫ (𝒰.inter s).ι) ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) := by
    rw [← hus, ← hιs]; simp only [Category.assoc]; rw [hD'.1 s]

  have hmod_of_coords : ∀ {c₀ : Γ(AkS D₀, (UkS D₀ 𝒰).U i₀) →
        (Module.Dual (ResidueField B) V →ₗ[ResidueField B] (ResidueField B ⊗[B] Γ(D₀.A, 𝒰.inter s)))}
      {vv : Spec (CommRingCat.of Γ(D₀.A, 𝒰.inter s)) ⟶ D₀.A},
      IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s) (haff s).fromSpec vv (xkS D₀) (LkS D₀) (akS D₀)
        ((UkS D₀ 𝒰).U i₀) c₀ →
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)))))
          ≫ (haff s).fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)))))
          ≫ vv := by
    intro c₀ vv h
    obtain ⟨w₀, hw₀, w₁, hpair, -, -⟩ := h
    exact specMap_mk_comp_eq_of_isTangentOfPair _ V ι _ hpair

  obtain ⟨ψ₀, hψ₀⟩ := exists_algHom_specMap_eq (B := B)
    ((haff s).isoSpec.inv ≫ (αr s 0).hom ≫ (haff s).isoSpec.hom) (by
      rw [← hus, ← hιs]; simp only [Category.assoc, Iso.hom_inv_id_assoc]; rw [hαrf 0])
  obtain ⟨ψτ, hψτ⟩ := exists_algHom_specMap_eq (B := B)
    ((haff s).isoSpec.inv ≫ (τ s).hom ≫ (haff s).isoSpec.hom) (by
      rw [← hus, ← hιs]; simp only [Category.assoc, Iso.hom_inv_id_assoc]; rw [hD.1 s])
  have hA₀ : vA 0 = Spec.map (CommRingCat.ofHom ψ₀.toRingHom) ≫ (haff s).fromSpec := by
    rw [hψ₀, ← hιs]; simp only [vA, Category.assoc, Iso.hom_inv_id_assoc]
  have hT : ((haff s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι) = Spec.map (CommRingCat.ofHom ψτ.toRingHom) ≫ (haff s).fromSpec := by
    rw [hψτ, ← hιs]; simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hcomm' : Spec.map (CommRingCat.ofHom ψ₀.toRingHom) ≫ ((haff s).isoSpec.inv ≫ (τ' s).hom ≫ (𝒰.inter s).ι)
      = Spec.map (CommRingCat.ofHom ψτ.toRingHom) ≫ vA 1 := by
    rw [hψ₀, hψτ]
    simp only [vA, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (τ s).hom, ← hcomm s, Category.assoc]

  have hmodψ : ∀ (ψ : Γ(D₀.A, 𝒰.inter s) →ₐ[B] Γ(D₀.A, 𝒰.inter s)),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)))))
          ≫ (haff s).fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)))))
          ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (haff s).fromSpec →
      ∀ c₁, Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))) (ψ c₁)
        = Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))) c₁ := by
    intro ψ h c₁
    rw [← Category.assoc, cancel_mono (haff s).fromSpec, ← Spec.map_comp] at h
    have h2 := congrArg Spec.preimage h
    rw [Spec.preimage_map, Spec.preimage_map] at h2
    exact (congrArg (fun φ : CommRingCat.of _ ⟶ CommRingCat.of _ => φ.hom c₁) h2).symm
  have hψ₀mod := hmodψ ψ₀ (by rw [← hA₀]; exact hmod_of_coords (hcor 0))
  have hψτmod := hmodψ ψτ (by rw [← hT]; exact hmod_of_coords hcs)

  have hsq := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add_eq_add_of_specMap_comp_eq
    (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒰.inter s) D₀.f (haff s).fromSpec hus
    (xkS D₀) (LkS D₀) (akS D₀) hak ((UkS D₀ 𝒰).U i₀) hUe e₁ he₁ ψ₀ ψτ hψ₀mod hψτmod
    ((haff s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι) ((haff s).isoSpec.inv ≫ (τ' s).hom ≫ (𝒰.inter s).ι) (vA 0) (vA 1)
    hvT'B (hvAB 1) hA₀ hT hcomm' cs cs' _ _ hcs hcs' (hcor 0) (hcor 1)
  have hsq' := congrArg (fun f => f a ξ) hsq
  simp only [Pi.add_apply, LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at hsq'

  have hbres : ∀ (t : 𝒰.Idx 0) (i : 𝒰.ι) (e : t.1 0 = i) (ht : (UkS D₀ 𝒰).inter s ≤ (UkS D₀ 𝒰).inter t)
      (ht' : 𝒰.inter s ≤ 𝒰.inter t) (hi : 𝒰.inter s ≤ 𝒰.U i),
      (FS D₀).res ht (b t) = -(σ s ((letI := algebraOfHom D₀.f (𝒰.U i);
        Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hi)) (bco i a ξ))) := by
    intro t i e ht ht' hi
    subst e
    letI := algebraOfHom D₀.f (𝒰.inter t)
    letI := algebraOfHom (xkS D₀) ((UkS D₀ 𝒰).inter t)
    have hσn : ∀ y : ResidueField B ⊗[B] Γ(D₀.A, 𝒰.inter t),
        σ s (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f ht') y)
          = ((AkS D₀).presheaf.map (homOfLE ht).op).hom (σ0 t y) := fun y =>
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
        D₀.f (akS D₀) (xkS D₀) ht'
        (𝒰.baseChange_inter_le D₀.f (ResidueField B) t) (𝒰.baseChange_inter_le D₀.f (ResidueField B) s) ht
        (σ0 t).toRingHom (σ s).toRingHom
        (fun x => hσ0₁ t x) (fun a' => hσ0₂ t a') (fun x => hσ₁ s x) (fun a' => hσ₂ s a') y
    have hcm : ∀ y : (letI := algebraOfHom D₀.f (𝒰.U (t.1 0)); ResidueField B ⊗[B] Γ(D₀.A, 𝒰.U (t.1 0))),
        (letI := algebraOfHom D₀.f (𝒰.U (t.1 0));
          Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f ht')
            (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒰.inter_le t 0)) y)
          = Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hi) y) := by
      letI := algebraOfHom D₀.f (𝒰.U (t.1 0))
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul a' x =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact congrArg (fun z => a' ⊗ₜ[B] z) (Scheme.TwoAffineOpenCover.res_res (𝒰.inter_le t 0) ht' x)
    show ((AkS D₀).presheaf.map (homOfLE ht).op).hom
        (-(σ0 t ((letI := algebraOfHom D₀.f (𝒰.U (t.1 0));
          Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒰.inter_le t 0)))
            (bco (t.1 0) a ξ)))) = _
    rw [map_neg, ← hσn, hcm]

  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, Pi.sub_apply]
  rw [hbres ((UkS D₀ 𝒰).face s 0) (s.1 1) rfl ((UkS D₀ 𝒰).inter_le_inter_face s 0) (𝒰.inter_le_inter_face s 0) (𝒰.inter_le s 1),
    hbres ((UkS D₀ 𝒰).face s 1) (s.1 0) rfl ((UkS D₀ 𝒰).inter_le_inter_face s 1) (𝒰.inter_le_inter_face s 1) (𝒰.inter_le s 0),
    ← hσcs a ξ, ← hσcs' a ξ]
  have key := congrArg (σ s) hsq'
  rw [map_add, map_add] at key
  show -(σ s _) + -(-(σ s _)) = σ s (cs a ξ) - σ s (cs' a ξ)
  rw [neg_neg, neg_add_eq_sub, sub_eq_sub_iff_add_eq_add]
  exact key

end
end S_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt (solution)
