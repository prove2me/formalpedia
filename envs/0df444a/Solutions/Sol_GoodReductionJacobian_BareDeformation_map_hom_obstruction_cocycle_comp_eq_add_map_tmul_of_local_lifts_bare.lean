-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/76eb66f2-3818-5f52-a28b-2926d624251d

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
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_local_lifts_factor_bare
import Theorems.Thm_AlgebraicGeometry_SmallExtension_pointDerivations_map_symm_map_rTensor_eq
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_unitPullback_hom_obstruction_cocycle_comp_sub_map_tmul_sub_baseChange_of_local_lifts_factor_bare
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

namespace P5Red

theorem unitPullback_sub {R R' : Type} [CommRing R] [CommRing R'] {X Y : Scheme.{0}}
    {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z z' : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (z - z') =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z
        - OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z' := by
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [Pi.sub_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
      OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
      OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj, Pi.sub_apply]
    erw [RingHom.map_sub, RingHom.map_sub]
    exact smul_sub _ _ _
  · rw [Pi.sub_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
      OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
      OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj]
    exact (sub_zero _).symm

theorem assemble
    {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] (ev : A →+* k)
    (W : Type) [AddCommGroup W] [Module k W]
    (Φ : ∀ (M : Type) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (W ⊗[k] M))
    (hΦnat : ∀ (M M' : Type) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[k] W) g (Φ M δ))
    (θ : W →ₗ[k] W)
    (D C1 : Type) [AddCommGroup D] [Module k D] [AddCommGroup C1] [Module k C1] (K : Submodule k C1)
    (H : Type) [AddCommGroup H] [Module k H] (cls : ↥K →ₗ[k] H) (ρ : H →ₗ[k] H)
    (c c' c'' : ↥(Algebra.PointDerivations k A ev (D →ₗ[k] C1)))
    (ĉ ĉ' ĉ'' : ↥(Algebra.PointDerivations k A ev (D →ₗ[k] ↥K)))
    (hĉ : ∀ (a : A) (ξ : D), ((ĉ.1 a ξ : ↥K) : C1) = c.1 a ξ)
    (hĉ' : ∀ (a : A) (ξ : D), ((ĉ'.1 a ξ : ↥K) : C1) = c'.1 a ξ)
    (hĉ'' : ∀ (a : A) (ξ : D), ((ĉ''.1 a ξ : ↥K) : C1) = c''.1 a ξ)
    (C1' : Type) [AddCommGroup C1'] [Module k C1'] (Rg : Submodule k C1')
    (P Q : C1 → C1') (hP : ∀ x y : C1, P (x - y) = P x - P y)
    (hρ : ∀ z z' : ↥K, Q (z : C1) - P (z' : C1) ∈ Rg → ρ (cls z) = cls z')
    (hfine : ∀ (a : A) (ξ : D),
      P (c''.1 a ξ) - P (((Φ (D →ₗ[k] C1)).symm (TensorProduct.map θ (LinearMap.id : (D →ₗ[k] C1) →ₗ[k] (D →ₗ[k] C1)) (Φ (D →ₗ[k] C1) c'))).1 a ξ)
        - Q (c.1 a ξ) ∈ Rg) :
    Φ (D →ₗ[k] H) (Algebra.PointDerivations.map (M := (D →ₗ[k] ↥K)) (M' := (D →ₗ[k] H)) ev (LinearMap.llcomp k D ↥K H cls) ĉ'') =
      TensorProduct.map θ (LinearMap.id : (D →ₗ[k] H) →ₗ[k] (D →ₗ[k] H))
          (Φ (D →ₗ[k] H) (Algebra.PointDerivations.map (M := (D →ₗ[k] ↥K)) (M' := (D →ₗ[k] H)) ev (LinearMap.llcomp k D ↥K H cls) ĉ')) +
        TensorProduct.map (LinearMap.id : W →ₗ[k] W) (LinearMap.llcomp k D H H ρ)
          (Φ (D →ₗ[k] H) (Algebra.PointDerivations.map (M := (D →ₗ[k] ↥K)) (M' := (D →ₗ[k] H)) ev (LinearMap.llcomp k D ↥K H cls) ĉ)) := by

  obtain ⟨ĉθ, hĉθ⟩ : ∃ ĉθ : ↥(Algebra.PointDerivations k A ev (D →ₗ[k] ↥K)),
      ĉθ = (Φ (D →ₗ[k] ↥K)).symm (TensorProduct.map θ (LinearMap.id : (D →ₗ[k] ↥K) →ₗ[k] (D →ₗ[k] ↥K)) (Φ (D →ₗ[k] ↥K) ĉ')) :=
    ⟨_, rfl⟩

  have hsub : Algebra.PointDerivations.map ev (LinearMap.llcomp k D ↥K C1 K.subtype) ĉ' = c' := by
    apply Subtype.ext
    apply LinearMap.ext; intro a; apply LinearMap.ext; intro ξ
    simp only [Algebra.PointDerivations.map_apply_coe, LinearMap.llcomp_apply, Submodule.subtype_apply, hĉ']

  have hθval : ∀ (a : A) (ξ : D), ((ĉθ.1 a ξ : ↥K) : C1) =
      ((Φ (D →ₗ[k] C1)).symm (TensorProduct.map θ (LinearMap.id : (D →ₗ[k] C1) →ₗ[k] (D →ₗ[k] C1)) (Φ (D →ₗ[k] C1) c'))).1 a ξ := by
    intro a ξ
    have h := AlgebraicGeometry.SmallExtension.pointDerivations_map_symm_map_rTensor_eq ev W Φ hΦnat θ (D →ₗ[k] ↥K) (D →ₗ[k] C1)
      (LinearMap.llcomp k D ↥K C1 K.subtype) ĉ'
    rw [hsub, ← hĉθ] at h
    have h' := congrArg (fun δ : ↥(Algebra.PointDerivations k A ev (D →ₗ[k] C1)) => δ.1 a ξ) h
    simpa only [Algebra.PointDerivations.map_apply_coe, LinearMap.llcomp_apply, Submodule.subtype_apply] using h'

  have hkey : ∀ (a : A) (ξ : D), ρ (cls (ĉ.1 a ξ)) = cls (ĉ''.1 a ξ) - cls (ĉθ.1 a ξ) := by
    intro a ξ
    rw [← map_sub]
    apply hρ
    have e : Q ((ĉ.1 a ξ : ↥K) : C1) - P (((ĉ''.1 a ξ - ĉθ.1 a ξ : ↥K) : C1)) =
        -(P (c''.1 a ξ) - P (((Φ (D →ₗ[k] C1)).symm (TensorProduct.map θ (LinearMap.id : (D →ₗ[k] C1) →ₗ[k] (D →ₗ[k] C1)) (Φ (D →ₗ[k] C1) c'))).1 a ξ)
          - Q (c.1 a ξ)) := by
      rw [Submodule.coe_sub, hP, hĉ, hĉ'', hθval]; abel
    rw [e]
    exact Rg.neg_mem (hfine a ξ)

  have hnatρ := hΦnat (D →ₗ[k] H) (D →ₗ[k] H) (LinearMap.llcomp k D H H ρ)
    (Algebra.PointDerivations.map (M := (D →ₗ[k] ↥K)) (M' := (D →ₗ[k] H)) ev (LinearMap.llcomp k D ↥K H cls) ĉ)
  have hnatθ := AlgebraicGeometry.SmallExtension.pointDerivations_map_symm_map_rTensor_eq ev W Φ hΦnat θ (D →ₗ[k] ↥K) (D →ₗ[k] H)
    (LinearMap.llcomp k D ↥K H cls) ĉ'
  rw [← hĉθ] at hnatθ
  rw [← hnatρ, ← LinearEquiv.apply_symm_apply (Φ (D →ₗ[k] H)) (TensorProduct.map θ LinearMap.id _), ← hnatθ, ← map_add]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext; intro a; apply LinearMap.ext; intro ξ
  simp only [Submodule.coe_add, LinearMap.add_apply, Algebra.PointDerivations.map_apply_coe, LinearMap.llcomp_apply, hkey a ξ]
  abel

end P5Red

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

    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
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
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c₀.1 a ξ s)
    (hc₀Z : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀.1 a ξ) = 0)

    (θψ : W →ₗ[(ResidueField B)] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (φ₁' : A₁ ⟶ A₁) (hφ₁' : φ₁' ≫ f₁ = f₁)
    (ψ' : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ' : ψ' ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁' : ψ' ≫ jκ = jκ ≫ φ₁')
    (hψhom' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField B))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap B (ResidueField B)))),
      pushPt ψ' hψ' ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t (pushPt ψ' hψ' P) (pushPt ψ' hψ' Q))

    (m' : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf' : ∀ i, m' i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ' : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m' i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁' ≫ D₀.g)
    (c₀' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m' (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m' (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c₀'.1 a ξ s)
    (hc₀Z' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀'.1 a ξ) = 0)

    (φ₁'' : A₁ ⟶ A₁) (hcomp : φ₁'' = φ₁' ≫ φ₁)
    (m'' : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf'' : ∀ i, m'' i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ'' : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m'' i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁'' ≫ D₀.g)
    (c₀'' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀'' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m'' (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m'' (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c₀''.1 a ξ s)
    (hc₀Z'' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀''.1 a ξ) = 0)

    (H₁ : Type) [AddCommGroup H₁] [Module (ResidueField B) H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] H₁) (hcls₁ : Function.Surjective cls₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)), cls₁ z = 0 ↔ (z : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0))
    (ρψ' : H₁ →ₗ[(ResidueField B)] H₁)
    (hρψ' : ∀ (𝒱 : (pullback D₀.f (specMap B (ResidueField B))).OrderedAffineCover) (lam lam' : 𝒱.ι → (𝒰.baseChange D₀.f (ResidueField B)).ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ' ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))),
        OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ' 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam' hl' (0 + 1) z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d 𝒱 0) →
        ρψ' (cls₁ z) = cls₁ z')
 :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)

    ∀ (ĉ₀ ĉ₀' ĉ₀'' : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))))),
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀.1 a ξ) →
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀'.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀'.1 a ξ) →
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀''.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀''.1 a ξ) →
      (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀'')) =
        TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁))
            (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀')) +
          TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) H₁ H₁ ρψ')
            (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀)) := by
  letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
  intro ĉ₀ ĉ₀' ĉ₀'' hĉ₀ hĉ₀' hĉ₀''

  have hA := GoodReductionJacobian.BareDeformation.exists_orderedAffineCover_local_lifts_factor_bare B B₁ hπ hker f₁ L₁ D₀ 𝒰 φ₁' jκ hjκ ψ' hψ₁' m' hmμ' D₀
    (fun i => (𝒰.U i).ι) (fun i => inferInstance) (fun i => morphismRestrict_ι D₀.g (𝒰.U i)) m' hmμ'
  obtain ⟨𝒱, lam₀, lam₀', hsub, n, n', hn, hn', hl₀, hl₀'⟩ := hA

  have hF := GoodReductionJacobian.BareDeformation.exists_d_eq_unitPullback_hom_obstruction_cocycle_comp_sub_map_tmul_sub_baseChange_of_local_lifts_factor_bare B B₁ hπ hker hsmall f₁ L₁ hc₁ h₁ hI V ι hι hιI D₀ 𝒰 i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂ hU W τW hWinj hWrange hWadd hWsmul Φ hΦnat hΦpin jκ hjκ φ₁ hφ₁ ψ hψ hψ₁ hψhom m hmf hmμ c₀ hc₀ hc₀Z θψ hθψ φ₁' hφ₁' ψ' hψ' hψ₁' hψhom' m' hmf' hmμ' c₀' hc₀' hc₀Z' φ₁'' hcomp m'' hmf'' hmμ'' c₀'' hc₀'' hc₀Z'' 𝒱 lam₀ lam₀' hsub n' hn' hl₀ hl₀'

  exact P5Red.assemble ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) W Φ hΦnat θψ (Module.Dual (ResidueField B) V) ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)
    (LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁ ρψ' c₀ c₀' c₀'' ĉ₀ ĉ₀' ĉ₀'' hĉ₀ hĉ₀' hĉ₀''
    ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒱.baseChange D₀.f (ResidueField B)) (0 + 1)) (LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒱.baseChange D₀.f (ResidueField B)) 0))
    (OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' (0 + 1))
    (OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ' (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ (0 + 1))
    (P5Red.unitPullback_sub (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' (0 + 1))
    (hρψ' (𝒱.baseChange D₀.f (ResidueField B)) lam₀ lam₀' hl₀ hl₀')
    (fun a ξ => LinearMap.mem_range.mpr (hF a ξ))

end S_GoodReductionJacobian_BareDeformation_map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare (solution)
