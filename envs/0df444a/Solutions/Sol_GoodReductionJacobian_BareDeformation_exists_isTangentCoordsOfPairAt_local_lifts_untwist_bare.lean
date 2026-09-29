-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/85193731-dddb-52b2-88bc-b3a0a406aec6

import Mathlib
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
import Theorems.Thm_Algebra_PointDerivations_exists_eq_and_map_eq_map_of_forall_apply_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_pointDerivations_map_symm_map_rTensor_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 320000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

noncomputable section

namespace K1bJAux

open Opposite TopologicalSpace AlgebraicGeometry.SmallExtension

theorem spec_map_comp_isoSpec_inv {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ U) :
    Spec.map (Y.presheaf.map (homOfLE e).op) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ Y.homOfLE e := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact hU.map_fromSpec hV (homOfLE e).op

theorem fromSpec_comp_eq {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem isoSpec_inv_comp_eq {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.isoSpec.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]; exact fromSpec_comp_eq f hU

theorem flat_sections {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

theorem isPullback_comp_of_factor {B B₁ : Type} [CommRing B] [IsLocalRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    {A₁ X₀ X Xκ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (.of B₁))
    (f₀ : X₀ ⟶ Spec (.of B)) (g₀ : A₁ ⟶ X₀) (hg₀ : IsPullback g₀ f₁ f₀ (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (f : X ⟶ Spec (.of B)) (g : A₁ ⟶ X) (hg : IsPullback g f₁ f (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (bκ : Xκ ⟶ X₀) (pκ : Xκ ⟶ Spec (.of (ResidueField B)))
    (hκ : IsPullback bκ pκ f₀ (Spec.map (CommRingCat.ofHom (algebraMap B (ResidueField B)))))
    (jκ : Xκ ⟶ A₁) (hjκ : jκ ≫ g₀ = bκ) :
    IsPullback (jκ ≫ g) pκ f (Spec.map (CommRingCat.ofHom (residue B))) := by
  have hk : RingHom.ker (algebraMap B B₁) ≤ RingHom.ker (residue B) := by rwa [ker_residue]
  let ρ : B₁ →+* ResidueField B := RingHom.liftOfSurjective (algebraMap B B₁) hπ ⟨residue B, hk⟩
  have hρ : ρ.comp (algebraMap B B₁) = residue B := RingHom.liftOfRightInverse_comp _ _ _ _
  have e1 : Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)) =
      Spec.map (CommRingCat.ofHom (residue B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have e2 : Spec.map (CommRingCat.ofHom (algebraMap B (ResidueField B))) = Spec.map (CommRingCat.ofHom (residue B)) := rfl
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have hcomm : jκ ≫ f₁ = pκ ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap B B₁))), Category.assoc, Category.assoc, e1,
      ← hg₀.w, ← Category.assoc, hjκ, hκ.w, e2]
  have big : IsPullback (jκ ≫ g₀) pκ f₀ (Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
    rw [hjκ, e1, ← e2]; exact hκ
  have sqL : IsPullback jκ pκ f₁ (Spec.map (CommRingCat.ofHom ρ)) := IsPullback.of_right big hcomm hg₀
  have := IsPullback.paste_horiz sqL hg
  rwa [e1] at this

theorem specMap_mk_comp_eq_of_isTangentCoordsOfPairAt {T' : Type} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type) [CommRing C] [Algebra T' C]
    {Y : Scheme.{0}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{0}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v := by
  obtain ⟨w₀, hw₀, w₁, ⟨ϑ, _, φ, hu, hv, -⟩, -, -⟩ := h
  rw [← hu, ← hv, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  have : (Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (pairFst I C) =
      (Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (pairSnd I C) := RingHom.ext fun x => x.2
  rw [this]

def sigmaLin {B : Type} [CommRing B] [IsLocalRing B] {C R : Type} [CommRing C] [Algebra B C] [CommRing R]
    [Algebra (ResidueField B) R]
    (σ : (ResidueField B) ⊗[B] C ≃+* R) (hσ₂ : ∀ a : ResidueField B, σ (a ⊗ₜ[B] (1 : C)) = algebraMap (ResidueField B) R a) :
    (ResidueField B) ⊗[B] C →ₗ[ResidueField B] R where
  toFun := σ
  map_add' := fun x y => map_add σ x y
  map_smul' := fun a x => by
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, hσ₂,
      ← Algebra.smul_def]

theorem sigmaLin_apply {B : Type} [CommRing B] [IsLocalRing B] {C R : Type} [CommRing C] [Algebra B C] [CommRing R]
    [Algebra (ResidueField B) R]
    (σ : (ResidueField B) ⊗[B] C ≃+* R) (hσ₂ : ∀ a : ResidueField B, σ (a ⊗ₜ[B] (1 : C)) = algebraMap (ResidueField B) R a)
    (x : (ResidueField B) ⊗[B] C) : sigmaLin σ hσ₂ x = σ x := rfl

end K1bJAux

end

open K1bJAux Opposite TopologicalSpace AlgebraicGeometry.SmallExtension in
theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
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

    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B)

    (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A) (hιopen : ∀ i, IsOpenImmersion (ιD i))
    (hιf : ∀ i, ιD i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hιsurj : ∀ x : D.A, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ιD i).base y = x)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)
    (hιglue : ∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιD (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιD (s.1 1))
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

    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))
    (W : Type) [AddCommGroup W] [Module (ResidueField B) W]
    (τW : W → SchemeHomOver (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))), P ∈ Set.range τW ↔ IsTangentVector (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (ResidueField B) (RingHom.id (ResidueField B)) P)
    (hWadd : ∀ v w : W, τW (v + w) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (τW v) (τW w))
    (hWsmul : ∀ (a : (ResidueField B)) (v : W), (τW (a • v)).1 = tangentScale (ResidueField B) a ≫ (τW v).1)

    (Φ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (M : Type) [AddCommGroup M] [Module (ResidueField B) M], ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) M) ≃ₗ[(ResidueField B)] (W ⊗[(ResidueField B)] M))
    (hΦnat : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (M M' : Type) [AddCommGroup M] [Module (ResidueField B) M] [AddCommGroup M'] [Module (ResidueField B) M'] (g : M →ₗ[(ResidueField B)] M') (δ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) g δ) = TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) g (Φ M δ))
    (hΦpin : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (δ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (ResidueField B))) (χ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →+* DualNumber (ResidueField B)),
        (∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)), TrivSqZeroExt.fst (χ a) = ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) a) →
        (∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)), TrivSqZeroExt.snd (χ a) = (δ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (ResidueField B)) a) →
        (τW (TensorProduct.rid (ResidueField B) W (Φ (ResidueField B) δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec)

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ : ψ ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)
    (hψhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField B))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap B (ResidueField B)))),
      pushPt ψ hψ ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)
    (c₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = (c₀ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) a ξ s)
    (hc₀Z : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀.1 a ξ) = 0)

    (θψ : W →ₗ[(ResidueField B)] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpf : ∀ i, mp i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)
    (c' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ mp (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ mp (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c'.1 a ξ s)

    (t : 𝒰.Idx 1) (Wo : D₀.A.Opens) (hWo : IsAffineOpen Wo) (hWt : Wo ≤ 𝒰.inter t)
    (cs' : letI := algebraOfHom D₀.f (𝒰.inter t)
      Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t))))
    (hcs' : letI := algebraOfHom D₀.f (𝒰.inter t)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter t)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 0) ≫ mp (t.1 0))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1))
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs') :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    letI := algebraOfHom D₀.f (𝒰.inter t)
    letI := algebraOfHom D₀.f Wo
    ∃ (y : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, Wo))))
      (xθ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t)))),
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, Wo)
        (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 0)) ≫ mp (t.1 0))
        (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 1)) ≫ mp (t.1 1))
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) y ∧
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ t (xθ a ξ) = (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c)))).1 a ξ t) ∧
      ∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)),
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hWt)).toLinearMap ∘ₗ cs' a =
          y a + (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hWt)).toLinearMap ∘ₗ xθ a := by
  classical

  haveI : Smooth D₀.f := D₀.bundle.smooth
  haveI := hιopen
  letI instUe := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
  letI algC := algebraOfHom D₀.f (𝒰.inter t)
  letI algW := algebraOfHom D₀.f Wo
  letI algκt := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter t)
  have haffU : IsAffineOpen (𝒰.inter t) := Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t
  haveI : Module.Flat B Γ(D₀.A, Wo) := flat_sections D₀.f hWo

  obtain ⟨cs, hcsAt, hcsσ⟩ := hτ t
  let σL : (ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t) →ₗ[ResidueField B]
      Γ(pullback D₀.f (specMap B (ResidueField B)), (𝒰.baseChange D₀.f (ResidueField B)).inter t) := sigmaLin (σ t) (hσ₂ t)
  let σLL : (Module.Dual (ResidueField B) V →ₗ[ResidueField B] (ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t)) →ₗ[ResidueField B]
      (Module.Dual (ResidueField B) V →ₗ[ResidueField B] Γ(pullback D₀.f (specMap B (ResidueField B)), (𝒰.baseChange D₀.f (ResidueField B)).inter t)) :=
    LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) _ _ σL
  let gL : (Module.Dual (ResidueField B) V →ₗ[ResidueField B] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1) →ₗ[ResidueField B]
      (Module.Dual (ResidueField B) V →ₗ[ResidueField B] Γ(pullback D₀.f (specMap B (ResidueField B)), (𝒰.baseChange D₀.f (ResidueField B)).inter t)) :=
    LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) _ _
      (LinearMap.proj t : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1 →ₗ[ResidueField B]
        Γ(pullback D₀.f (specMap B (ResidueField B)), (𝒰.baseChange D₀.f (ResidueField B)).inter t))
  have hσLL : ∀ (f : Module.Dual (ResidueField B) V →ₗ[ResidueField B] (ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t)) (ξ : Module.Dual (ResidueField B) V),
      σLL f ξ = σ t (f ξ) := fun f ξ => rfl
  have hgL : ∀ (f : Module.Dual (ResidueField B) V →ₗ[ResidueField B] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)
      (ξ : Module.Dual (ResidueField B) V), gL f ξ = f ξ t := fun f ξ => rfl
  have hinjσ : Function.Injective σLL := by
    intro f g hfg
    ext ξ
    apply (σ t).injective
    rw [← hσLL, ← hσLL, hfg]
  have hpin : ∀ a, σLL (cs a) = gL (c.1 a) := by
    intro a; ext ξ; rw [hσLL, hgL]; exact hcsσ a ξ
  obtain ⟨δt, hδt, hδmap⟩ := Algebra.PointDerivations.exists_eq_and_map_eq_map_of_forall_apply_eq _ _ _ _ c gL σLL hinjσ cs hpin
  have hδfun : (fun a => δt.1 a) = cs := funext hδt

  have hδAt : IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter t)
      (haffU.isoSpec.inv ≫ (𝒰.inter t).ι) ((haffU.isoSpec.inv ≫ (τ t).hom) ≫ (𝒰.inter t).ι)
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) (fun a => δt.1 a) := by
    rw [hδfun, IsAffineOpen.isoSpec_inv_ι, Category.assoc]; exact hcsAt
  have huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t))))) ≫ haffU.isoSpec.inv =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t))))) ≫ haffU.isoSpec.inv ≫ (τ t).hom := by
    have h := specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hcsAt
    rw [← IsAffineOpen.isoSpec_inv_ι] at h
    rw [← cancel_mono (𝒰.inter t).ι]
    simpa only [Category.assoc] using h
  have hzψ : ∀ {S : Scheme.{0}} (g : S ⟶ ↑(𝒰.inter t)) (gk : S ⟶ pullback D₀.f (specMap B (ResidueField B))),
      g ≫ (𝒰.inter t).ι = gk ≫ pullback.fst D₀.f (specMap B (ResidueField B)) →
      g ≫ (D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1)) = gk ≫ ψ ≫ (jκ ≫ D.g) := by
    intro S g gk hg
    have hg' : (g ≫ D₀.A.homOfLE (𝒰.inter_le t 1)) ≫ (𝒰.U (t.1 1)).ι = (gk ≫ jκ) ≫ D₀.g := by
      rw [Category.assoc, Scheme.homOfLE_ι, hg, Category.assoc, hjκ]
    have sq := isPullback_morphismRestrict D₀.g (𝒰.U (t.1 1))
    rw [← Category.assoc, ← sq.lift_fst _ _ hg', Category.assoc, hmpμ, ← Category.assoc (sq.lift _ _ hg'), sq.lift_snd,
      Category.assoc]
    rw [← Category.assoc jκ φ₁ D.g, ← hψ₁, Category.assoc]
  have hCR := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot
    B (RingHom.ker (algebraMap B B₁)) hI hsmall V ι Γ(D₀.A, 𝒰.inter t) ((𝒰.inter t).ι) (D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1))
    haffU.isoSpec.inv (haffU.isoSpec.inv ≫ (τ t).hom) huv
    (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
    ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁ (pullback.fst D₀.f (specMap B (ResidueField B))) (jκ ≫ D.g)
    W τW hWinj hWrange hWadd hWsmul Φ hΦnat hΦpin ψ hψ hψhom θψ hθψ hzψ δt hδAt

  let xθD := (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t)))).symm
      (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t))) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t))))
        (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t))) δt))
  have hpinθ : ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      σ t (xθD.1 a ξ) = (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c)))).1 a ξ t := by
    intro a ξ
    have E1 := AlgebraicGeometry.SmallExtension.pointDerivations_map_symm_map_rTensor_eq _ W Φ hΦnat θψ _ _ σLL δt
    have E2 := AlgebraicGeometry.SmallExtension.pointDerivations_map_symm_map_rTensor_eq _ W Φ hΦnat θψ _ _ gL c
    rw [hδmap, ← E2] at E1

    have E3 := congrArg (fun Dd => (Subtype.val Dd) a ξ) E1
    simp only [Algebra.PointDerivations.map_apply_coe] at E3
    rw [hσLL, hgL] at E3
    exact E3

  have hSr : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hWt).toRingHom) ≫ haffU.isoSpec.inv = hWo.isoSpec.inv ≫ D₀.A.homOfLE hWt :=
    spec_map_comp_isoSpec_inv haffU hWo hWt
  have hC' := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
    Γ(D₀.A, 𝒰.inter t) Γ(D₀.A, Wo) (restrictAlgHom D₀.f hWt) _ _ _ _ _ _ cs' hcs'
  have hX' := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
    Γ(D₀.A, 𝒰.inter t) Γ(D₀.A, Wo) (restrictAlgHom D₀.f hWt) _ _ _ _ _ _ _ hCR
  have eU0 : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hWt).toRingHom) ≫ haffU.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 0) ≫ mp (t.1 0) =
      hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 0)) ≫ mp (t.1 0) := by
    rw [← Category.assoc, hSr, Category.assoc, ← Category.assoc (D₀.A.homOfLE hWt), Scheme.homOfLE_homOfLE]
  have eU1 : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hWt).toRingHom) ≫ haffU.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1) =
      hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 1)) ≫ mp (t.1 1) := by
    rw [← Category.assoc, hSr, Category.assoc, ← Category.assoc (D₀.A.homOfLE hWt), Scheme.homOfLE_homOfLE]
  have eX1 : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hWt).toRingHom) ≫ haffU.isoSpec.inv ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1) =
      hWo.isoSpec.inv ≫ D₀.A.homOfLE hWt ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1) := by
    rw [← Category.assoc, hSr, Category.assoc]
  have eX1' : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hWt).toRingHom) ≫ (haffU.isoSpec.inv ≫ (τ t).hom) ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1) =
      hWo.isoSpec.inv ≫ D₀.A.homOfLE hWt ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1) := by
    rw [Category.assoc, eX1]
  rw [eU0, eX1] at hC'
  have hX'' : IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, Wo)
      (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 1)) ≫ mp (t.1 1))
      (hWo.isoSpec.inv ≫ D₀.A.homOfLE hWt ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1))
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hWt)).toLinearMap ∘ₗ xθD.1 a) := by
    rw [← eU1, ← eX1']
    exact hX'
  clear hX'

  have hux := specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hC'
  have hvx := specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hX''
  have huv' := hux.trans hvx.symm

  have hU0f : (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 0)) ≫ mp (t.1 0)) ≫ D.f =
      Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, Wo))) := by
    rw [Category.assoc, Category.assoc, hmpf, ← Category.assoc (D₀.A.homOfLE _), Scheme.homOfLE_ι]
    exact isoSpec_inv_comp_eq D₀.f hWo
  have hU1f : (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 1)) ≫ mp (t.1 1)) ≫ D.f =
      Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, Wo))) := by
    rw [Category.assoc, Category.assoc, hmpf, ← Category.assoc (D₀.A.homOfLE _), Scheme.homOfLE_ι]
    exact isoSpec_inv_comp_eq D₀.f hWo
  have hX1f : (hWo.isoSpec.inv ≫ D₀.A.homOfLE hWt ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1)) ≫ D.f =
      Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, Wo))) := by
    simp only [Category.assoc]
    rw [hmpf, ← Category.assoc (D₀.A.homOfLE (𝒰.inter_le t 1)) ((𝒰.U (t.1 1)).ι) D₀.f, Scheme.homOfLE_ι, hτB,
      ← Category.assoc (D₀.A.homOfLE hWt) ((𝒰.inter t).ι) D₀.f, Scheme.homOfLE_ι]
    exact isoSpec_inv_comp_eq D₀.f hWo

  have hak : IsPullback (jκ ≫ D.g) (pullback.snd D₀.f (specMap B (ResidueField B))) D.f (Spec.map (CommRingCat.ofHom (residue B))) :=
    isPullback_comp_of_factor hπ hI f₁ D₀.f D₀.g D₀.cart D.f D.g D.cart (pullback.fst D₀.f (specMap B (ResidueField B)))
      (pullback.snd D₀.f (specMap B (ResidueField B))) (IsPullback.of_hasPullback _ _) jκ hjκ

  have hEX := AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
    Γ(D₀.A, Wo) D.f (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 0)) ≫ mp (t.1 0)) hU0f
    (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
    (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁
    (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 1)) ≫ mp (t.1 1)) hU1f huv'
  obtain ⟨y, hy⟩ := hEX
  have hadd := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
    Γ(D₀.A, Wo) D.f
    (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 0)) ≫ mp (t.1 0))
    (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 1)) ≫ mp (t.1 1))
    (hWo.isoSpec.inv ≫ D₀.A.homOfLE hWt ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1))
    hU0f hU1f hX1f huv' hvx (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
    (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁
    y (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hWt)).toLinearMap ∘ₗ xθD.1 a)
    (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hWt)).toLinearMap ∘ₗ cs' a)
    hy hX'' hC'
  refine ⟨y, fun a => xθD.1 a, hy, hpinθ, fun a => ?_⟩
  exact congrFun hadd a

end S_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare (solution)
