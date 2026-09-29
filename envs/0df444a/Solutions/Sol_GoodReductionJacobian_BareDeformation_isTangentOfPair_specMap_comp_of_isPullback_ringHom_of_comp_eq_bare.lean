-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.isTangentOfPair_specMap_comp_of_isPullback_ringHom_of_comp_eq_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bf604d13-7e7b-5a5b-bb88-7e472276dbfb

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_isTangentOfPair_specMap_comp_of_isPullback_ringHom_of_comp_eq_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.SmallExtension"

open scoped Quaternion TensorProduct NumberField

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in
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

    (φ : B →+* B) (hφ₁ : (algebraMap B B₁).comp φ = algebraMap B B₁)
    (φV : V →ₗ[(ResidueField B)] V) (hφV : ∀ v : V, ι (φV v) = φ (ι v))
    (k₀ : D₀.A ⟶ D₀.A) (hk₀c : CategoryTheory.IsPullback k₀ D₀.f D₀.f (Spec.map (CommRingCat.ofHom φ)))
    (hk₀g : D₀.g ≫ k₀ = D₀.g) (hk₀κ : (pullback.fst D₀.f (specMap B (ResidueField B))) ≫ k₀ = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (s : 𝒰.Idx 1) (k₀s : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s)) (hk₀s : k₀s ≫ (𝒰.inter s).ι = (𝒰.inter s).ι ≫ k₀)
    (τs τs' : ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτB : τs.hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f) (hτ'B : τs'.hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hττ' : τs'.hom ≫ k₀s = k₀s ≫ τs.hom)

    (w₀ : letI := algebraOfHom D₀.f (𝒰.inter s)
      Spec (CommRingCat.of (AlgebraicGeometry.SmallExtension.thickening B V Γ(D₀.A, 𝒰.inter s))) ⟶ (pullback D₀.f (specMap B (ResidueField B))))
    (hw : letI := algebraOfHom D₀.f (𝒰.inter s)
      AlgebraicGeometry.SmallExtension.IsTangentOfPair (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ τs.hom ≫ (𝒰.inter s).ι)
        (w₀ ≫ pullback.fst D₀.f (specMap B (ResidueField B)))) :
    letI := algebraOfHom D₀.f (𝒰.inter s)
    AlgebraicGeometry.SmallExtension.IsTangentOfPair (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ τs'.hom ≫ (𝒰.inter s).ι)
      ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))) (TrivSqZeroExt.map (R' := (ResidueField B)) φV)).toRingHom) ≫ w₀) ≫
        pullback.fst D₀.f (specMap B (ResidueField B))) := by
  letI instC : Algebra B Γ(D₀.A, 𝒰.inter s) := algebraOfHom D₀.f (𝒰.inter s)
  have hU : IsAffineOpen (𝒰.inter s) := Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s

  obtain ⟨ϑ, hϑ, φP, hφ1, hφ2, hw⟩ := hw

  have hle : (𝒰.inter s) ≤ k₀ ⁻¹ᵁ (𝒰.inter s) := by
    intro x hx
    show k₀.base x ∈ ((𝒰.inter s) : Set D₀.A)
    have h1 : (k₀s ≫ (𝒰.inter s).ι).base ⟨x, hx⟩ = ((𝒰.inter s).ι ≫ k₀).base ⟨x, hx⟩ := by rw [hk₀s]
    have h2 : ((𝒰.inter s).ι ≫ k₀).base ⟨x, hx⟩ = k₀.base x := rfl
    rw [← h2, ← h1]
    exact (k₀s.base ⟨x, hx⟩).2
  have hk₀s' : k₀s = k₀.resLE (𝒰.inter s) (𝒰.inter s) hle := by
    rw [← cancel_mono (𝒰.inter s).ι, hk₀s, Scheme.Hom.resLE_comp_ι]

  let κC : Γ(D₀.A, 𝒰.inter s) →+* Γ(D₀.A, 𝒰.inter s) := (k₀.appLE (𝒰.inter s) (𝒰.inter s) hle).hom
  have F1 : Spec.map (CommRingCat.ofHom κC) ≫ hU.fromSpec = hU.fromSpec ≫ k₀ := by
    show Spec.map (k₀.appLE (𝒰.inter s) (𝒰.inter s) hle) ≫ hU.fromSpec = hU.fromSpec ≫ k₀
    exact IsAffineOpen.SpecMap_appLE_fromSpec k₀ hU hU hle
  have F1' : Spec.map (CommRingCat.ofHom κC) ≫ hU.isoSpec.inv = hU.isoSpec.inv ≫ k₀s := by
    rw [← cancel_mono (𝒰.inter s).ι, Category.assoc, Category.assoc, hk₀s, IsAffineOpen.isoSpec_inv_ι, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_ι, F1]

  have F0 : hU.fromSpec ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) := by
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec D₀.f (isAffineOpen_top (Spec (CommRingCat.of B))) hU
      (show (𝒰.inter s) ≤ D₀.f ⁻¹ᵁ ⊤ from le_top)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h1
    rw [← h1]
    rfl
  have F2 : ∀ t : B, κC (algebraMap B Γ(D₀.A, 𝒰.inter s) t) = algebraMap B Γ(D₀.A, 𝒰.inter s) (φ t) := by
    have h1 : Spec.map (CommRingCat.ofHom κC) ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) =
        Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [← F0, ← Category.assoc, F1, Category.assoc, hk₀c.w, ← Category.assoc]
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h1
    intro t
    exact congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of Γ(D₀.A, 𝒰.inter s) => f.hom t) h1
  have F3 : ∀ c : Γ(D₀.A, 𝒰.inter s), (1 : (ResidueField B)) ⊗ₜ[B] κC c = (1 : (ResidueField B)) ⊗ₜ[B] c := by
    intro c
    apply (σ s).injective
    rw [hσ₁, hσ₁]

    have h1 : k₀.appLE (𝒰.inter s) (𝒰.inter s) hle ≫ (pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s) =
        (pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s) := by
      have hc : ∀ (f g : (pullback D₀.f (specMap B (ResidueField B))) ⟶ D₀.A) (hfg : f = g)
          (e : (pullback.fst D₀.f (specMap B (ResidueField B))) ⁻¹ᵁ (𝒰.inter s) ≤ f ⁻¹ᵁ (𝒰.inter s))
          (e' : (pullback.fst D₀.f (specMap B (ResidueField B))) ⁻¹ᵁ (𝒰.inter s) ≤ g ⁻¹ᵁ (𝒰.inter s)),
          f.appLE (𝒰.inter s) _ e = g.appLE (𝒰.inter s) _ e' := by
        intros f g hfg e e'; subst hfg; rfl
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      exact hc _ _ hk₀κ _ _
    show (CommRingCat.Hom.hom _) ((CommRingCat.Hom.hom _) ((k₀.appLE (𝒰.inter s) (𝒰.inter s) hle).hom c)) = _
    rw [← CommRingCat.comp_apply _ ((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)), h1]

  have hφI : ∀ t ∈ (RingHom.ker (algebraMap B B₁)), φ t ∈ (RingHom.ker (algebraMap B B₁)) := by
    intro t ht
    rw [RingHom.mem_ker] at ht ⊢
    have := congrArg (fun f : B →+* B₁ => f t) hφ₁
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [this, ht]
  have hκIC : ∀ x ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)), κC x ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      rw [F2]
      exact Ideal.mem_map_of_mem _ (hφI t ht)
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | smul a x _ hx => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx
  have hdiag_mem : ∀ a : Γ(D₀.A, 𝒰.inter s), (a, a) ∈ pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s) := fun a => rfl
  have hιmem : ∀ v : V, ι v ∈ (RingHom.ker (algebraMap B B₁)) := fun v => by
    have : ι v ∈ LinearMap.range ι := ⟨v, rfl⟩
    rw [hιI] at this; exact this
  have hoff_mem : ∀ x : Γ(D₀.A, 𝒰.inter s), x ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)) → ((0 : Γ(D₀.A, 𝒰.inter s)), x) ∈ pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s) := by
    intro x hx
    rw [mem_pairRing, Ideal.Quotient.eq, zero_sub, neg_mem_iff]
    exact hx
  have hmemP : ∀ z : Γ(D₀.A, 𝒰.inter s) × Γ(D₀.A, 𝒰.inter s), z ∈ pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s) → (κC z.1, κC z.2) ∈ pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s) := by
    intro z hz
    rw [mem_pairRing, Ideal.Quotient.eq] at hz ⊢
    show κC z.1 - κC z.2 ∈ _
    rw [← map_sub]
    exact hκIC _ hz
  let κP : pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s) →+* pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s) :=
    ((RingHom.prodMap κC κC).comp (pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)).subtype).codRestrict (pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s))
      (fun z => hmemP z.1 z.2)
  have κP_apply : ∀ (z : Γ(D₀.A, 𝒰.inter s) × Γ(D₀.A, 𝒰.inter s)) (hz : z ∈ pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)),
      κP ⟨z, hz⟩ = ⟨(κC z.1, κC z.2), hmemP z hz⟩ := fun z hz => rfl

  let θE : thickening B V Γ(D₀.A, 𝒰.inter s) →ₐ[(ResidueField B)] thickening B V Γ(D₀.A, 𝒰.inter s) :=
    Algebra.TensorProduct.map (AlgHom.id (ResidueField B) ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))) (TrivSqZeroExt.map (R' := (ResidueField B)) φV)
  let θEr : thickening B V Γ(D₀.A, 𝒰.inter s) →+* thickening B V Γ(D₀.A, 𝒰.inter s) := θE.toRingHom
  have θEr_apply : ∀ x, θEr x = θE x := fun x => rfl
  have hred : ∀ c : Γ(D₀.A, 𝒰.inter s), toReduction B Γ(D₀.A, 𝒰.inter s) (κC c) = toReduction B Γ(D₀.A, 𝒰.inter s) c := fun c => F3 c
  have key : ∀ z : pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s), ϑ (κP z) = θE (ϑ z) := by
    have hdiag : ∀ (a : Γ(D₀.A, 𝒰.inter s)), ϑ (κP ⟨(a, a), hdiag_mem a⟩) = θE (ϑ ⟨(a, a), hdiag_mem a⟩) := by
      intro a
      rw [κP_apply, hϑ.1 a (hdiag_mem a)]
      show ϑ ⟨(κC a, κC a), hdiag_mem (κC a)⟩ = _
      rw [hϑ.1 (κC a) (hdiag_mem (κC a)), hred, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]
    have hoff : ∀ (x : Γ(D₀.A, 𝒰.inter s)) (hx : x ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))),
        ϑ (κP ⟨((0 : Γ(D₀.A, 𝒰.inter s)), x), hoff_mem x hx⟩) = θE (ϑ ⟨((0 : Γ(D₀.A, 𝒰.inter s)), x), hoff_mem x hx⟩) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t, ht, rfl⟩ := hx
        obtain ⟨v, rfl⟩ : t ∈ LinearMap.range ι := by rw [hιI]; exact ht
        have e1 : (⟨((0 : Γ(D₀.A, 𝒰.inter s)), algebraMap B Γ(D₀.A, 𝒰.inter s) (ι v)), hoff_mem _ (Ideal.mem_map_of_mem _ ht)⟩ : pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) =
            ⟨((0 : Γ(D₀.A, 𝒰.inter s)), algebraMap B Γ(D₀.A, 𝒰.inter s) (ι v) * 1), by rw [mul_one]; exact hoff_mem _ (Ideal.mem_map_of_mem _ ht)⟩ := by
          simp only [mul_one]
        have e2 : κP ⟨((0 : Γ(D₀.A, 𝒰.inter s)), algebraMap B Γ(D₀.A, 𝒰.inter s) (ι v)), hoff_mem _ (Ideal.mem_map_of_mem _ ht)⟩ =
            ⟨((0 : Γ(D₀.A, 𝒰.inter s)), algebraMap B Γ(D₀.A, 𝒰.inter s) (ι (φV v)) * 1), by
              rw [mul_one]; exact hoff_mem _ (Ideal.mem_map_of_mem _ (hιmem (φV v)))⟩ := by
          apply Subtype.ext
          rw [κP_apply]
          simp only [Prod.mk.injEq, map_zero, mul_one, true_and]
          rw [F2, hφV]
        rw [e2, hϑ.2 (φV v) 1, e1, hϑ.2 v 1, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
        congr 1
        ext <;> simp
      | zero =>
        have e0 : (⟨((0 : Γ(D₀.A, 𝒰.inter s)), (0 : Γ(D₀.A, 𝒰.inter s))), hoff_mem 0 (Ideal.zero_mem _)⟩ : pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) = 0 := rfl
        rw [e0, map_zero, map_zero, map_zero]
      | add x y hx' hy' hx hy =>
        have eadd : (⟨((0 : Γ(D₀.A, 𝒰.inter s)), x + y), hoff_mem _ (Ideal.add_mem _ hx' hy')⟩ : pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) =
            ⟨((0 : Γ(D₀.A, 𝒰.inter s)), x), hoff_mem x hx'⟩ + ⟨((0 : Γ(D₀.A, 𝒰.inter s)), y), hoff_mem y hy'⟩ := by
          apply Subtype.ext; simp
        rw [eadd, map_add, map_add, map_add, map_add, hx, hy]
      | smul a x hx' hx =>
        have esmul : (⟨((0 : Γ(D₀.A, 𝒰.inter s)), a • x), hoff_mem _ (Ideal.mul_mem_left _ a hx')⟩ : pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) =
            ⟨(a, a), hdiag_mem a⟩ * ⟨((0 : Γ(D₀.A, 𝒰.inter s)), x), hoff_mem x hx'⟩ := by
          apply Subtype.ext; simp [smul_eq_mul]
        rw [esmul, map_mul, map_mul, map_mul, map_mul, hdiag, hx]
    intro z
    have hz2 : z.1.2 - z.1.1 ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)) := by
      have h := (Ideal.Quotient.eq).1 z.2
      rwa [← neg_sub, neg_mem_iff] at h
    have hz : z = ⟨(z.1.1, z.1.1), hdiag_mem z.1.1⟩ + ⟨((0 : Γ(D₀.A, 𝒰.inter s)), z.1.2 - z.1.1), hoff_mem _ hz2⟩ := by
      apply Subtype.ext; ext <;> simp
    rw [hz, map_add, map_add, map_add, map_add, hdiag, hoff _ hz2]

  let algP : B →+* pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s) :=
    ((algebraMap B Γ(D₀.A, 𝒰.inter s)).prod (algebraMap B Γ(D₀.A, 𝒰.inter s))).codRestrict (pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) (fun t => hdiag_mem _)
  have hvB : (hU.isoSpec.inv ≫ τs.hom ≫ (𝒰.inter s).ι) ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) := by
    rw [Category.assoc, Category.assoc, hτB, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, F0]
  have hv'B : (hU.isoSpec.inv ≫ τs'.hom ≫ (𝒰.inter s).ι) ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s))) := by
    rw [Category.assoc, Category.assoc, hτ'B, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, F0]
  have hφPB : φP ≫ D₀.f = Spec.map (CommRingCat.ofHom algP) := by
    obtain ⟨r, hr⟩ : ∃ r : CommRingCat.of B ⟶ CommRingCat.of (pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)), Spec.map r = φP ≫ D₀.f :=
      ⟨(Scheme.Spec.preimage (φP ≫ D₀.f)).unop, Scheme.Spec.map_preimage (φP ≫ D₀.f)⟩
    have h1 : r ≫ CommRingCat.ofHom (pairFst (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) = CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hr, ← Category.assoc, hφ1, F0]
    have h2 : r ≫ CommRingCat.ofHom (pairSnd (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) = CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hr, ← Category.assoc, hφ2, hvB]
    rw [← hr]
    congr 1
    ext t
    · exact congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of Γ(D₀.A, 𝒰.inter s) => f.hom t) h1
    · exact congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of Γ(D₀.A, 𝒰.inter s) => f.hom t) h2
  have hκalg : (CommRingCat.ofHom algP) ≫ CommRingCat.ofHom κP = CommRingCat.ofHom φ ≫ CommRingCat.ofHom algP := by
    ext t
    · exact F2 t
    · exact F2 t
  have hcompat : (Spec.map (CommRingCat.ofHom κP) ≫ φP) ≫ D₀.f =
      Spec.map (CommRingCat.ofHom algP) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, hφPB, ← Spec.map_comp, ← Spec.map_comp, hκalg]
  let φP' : Spec (CommRingCat.of (pairRing (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s))) ⟶ D₀.A :=
    hk₀c.lift (Spec.map (CommRingCat.ofHom κP) ≫ φP) (Spec.map (CommRingCat.ofHom algP)) hcompat
  have hpr1 : CommRingCat.ofHom κP ≫ CommRingCat.ofHom (pairFst (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) =
      CommRingCat.ofHom (pairFst (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) ≫ CommRingCat.ofHom κC := by ext z; rfl
  have hpr2 : CommRingCat.ofHom κP ≫ CommRingCat.ofHom (pairSnd (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) =
      CommRingCat.ofHom (pairSnd (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) ≫ CommRingCat.ofHom κC := by ext z; rfl
  have halg1 : CommRingCat.ofHom algP ≫ CommRingCat.ofHom (pairFst (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) = CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s)) := by
    ext t; rfl
  have halg2 : CommRingCat.ofHom algP ≫ CommRingCat.ofHom (pairSnd (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s)) = CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter s)) := by
    ext t; rfl
  have hφP'1 : Spec.map (CommRingCat.ofHom (pairFst (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s))) ≫ φP' = hU.fromSpec := by
    apply hk₀c.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, ← Spec.map_comp, hpr1, Spec.map_comp, Category.assoc,
        hφ1, F1]
    · rw [Category.assoc, IsPullback.lift_snd, ← Spec.map_comp, halg1, F0]
  have hφP'2 : Spec.map (CommRingCat.ofHom (pairSnd (RingHom.ker (algebraMap B B₁)) Γ(D₀.A, 𝒰.inter s))) ≫ φP' = hU.isoSpec.inv ≫ τs'.hom ≫ (𝒰.inter s).ι := by
    apply hk₀c.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, ← Spec.map_comp, hpr2, Spec.map_comp, Category.assoc,
        hφ2, ← Category.assoc, F1']
      simp only [Category.assoc]
      rw [← hk₀s, ← Category.assoc τs'.hom, hττ', Category.assoc]
    · rw [Category.assoc, IsPullback.lift_snd, ← Spec.map_comp, halg2, hv'B]

  let ΘE : CommRingCat.of (thickening B V Γ(D₀.A, 𝒰.inter s)) ⟶ CommRingCat.of (thickening B V Γ(D₀.A, 𝒰.inter s)) := CommRingCat.ofHom θEr
  have hkeyR : CommRingCat.ofHom κP ≫ CommRingCat.ofHom ϑ = CommRingCat.ofHom ϑ ≫ ΘE := by
    ext z; exact key z
  have hpair' : IsTangentOfPair (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s) hU.fromSpec (hU.isoSpec.inv ≫ τs'.hom ≫ (𝒰.inter s).ι)
      ((Spec.map ΘE ≫ w₀) ≫ pullback.fst D₀.f (specMap B (ResidueField B))) := by
    refine ⟨ϑ, hϑ, φP', hφP'1, hφP'2, ?_⟩
    apply hk₀c.hom_ext
    · rw [Category.assoc, Category.assoc, hk₀κ, hw, Category.assoc, IsPullback.lift_fst, ← Category.assoc,
        ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hkeyR]
    ·
      have hresφ : ∀ t : B, algebraMap B (ResidueField B) (φ t) = algebraMap B (ResidueField B) t := by
        intro t
        rw [IsLocalRing.ResidueField.algebraMap_eq]
        apply (Ideal.Quotient.eq).2
        apply hI
        rw [RingHom.mem_ker, map_sub, sub_eq_zero]
        have := congrArg (fun f : B →+* B₁ => f t) hφ₁
        simpa using this
      have hϑalg : ∀ x : B, ϑ (algP x) = algebraMap B (ResidueField B) x • (1 : thickening B V Γ(D₀.A, 𝒰.inter s)) := by
        intro x
        change ϑ ⟨(algebraMap B Γ(D₀.A, 𝒰.inter s) x, algebraMap B Γ(D₀.A, 𝒰.inter s) x), hdiag_mem _⟩ = _
        rw [hϑ.1 _ (hdiag_mem _)]
        show ((1 : (ResidueField B)) ⊗ₜ[B] algebraMap B Γ(D₀.A, 𝒰.inter s) x) ⊗ₜ[(ResidueField B)] (1 : TrivSqZeroExt (ResidueField B) V) = _
        rw [Algebra.algebraMap_eq_smul_one (A := Γ(D₀.A, 𝒰.inter s)) x, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul (ResidueField B) x,
          ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def]
      simp only [Category.assoc]
      rw [IsPullback.lift_snd, ← Category.assoc w₀, hw, Category.assoc, hφPB, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      rw [Category.assoc, ← hkeyR, ← Category.assoc, hκalg, Category.assoc]
      ext t
      change ϑ (algP (φ t)) = ϑ (algP t)
      rw [hϑalg, hϑalg, hresφ]
  exact hpair'

end S_GoodReductionJacobian_BareDeformation_isTangentOfPair_specMap_comp_of_isPullback_ringHom_of_comp_eq_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_isTangentOfPair_specMap_comp_of_isPullback_ringHom_of_comp_eq_bare (solution)
