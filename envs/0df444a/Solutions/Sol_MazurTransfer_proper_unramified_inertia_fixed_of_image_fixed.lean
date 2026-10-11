-- Prove2me | solution 1 for MazurTransfer.proper_unramified_inertia_fixed_of_image_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-11T00:00:49.305373+00:00
-- url     : https://prove2.me/submissions/df6e96e8-38a0-4ec2-a61a-ab6b4ad5b272

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Retains the complete inertia ring-side helpers from Anthropic FLT, pin
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: proper unramified inertia fixed fibres.
Named downstream consumer: actual order-13 good-prime Kummer restrictions. -/
import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u

noncomputable section
namespace MazurTransfer.PublicProperUnramifiedInertiaHelpers


variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]

theorem exists_of_mem_inertiaSubgroupIn (A : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ ∈ A.inertiaSubgroupIn K) :
    ∃ d : A.decompositionSubgroup K, d ∈ A.inertiaSubgroup K ∧ (d : Ω ≃ₐ[K] Ω) = σ := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  exact ⟨d, hd, rfl⟩

noncomputable def decompRingHom (A : ValuationSubring Ω) (d : A.decompositionSubgroup K) :
    A →+* A :=
  MulSemiringAction.toRingHom (A.decompositionSubgroup K) A d

theorem residue_comp_decompRingHom (A : ValuationSubring Ω) (d : A.decompositionSubgroup K)
    (hd : d ∈ A.inertiaSubgroup K) :
    (IsLocalRing.residue A).comp (decompRingHom A d) = IsLocalRing.residue A := by
  ext a
  simp only [RingHom.comp_apply, decompRingHom, MulSemiringAction.toRingHom_apply]
  rw [IsLocalRing.ResidueField.residue_smul]
  have h := hd
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at h
  have := congrArg (fun e : RingAut (IsLocalRing.ResidueField A) => e (IsLocalRing.residue A a)) h
  simpa using this

theorem algebraMap_comp_decompRingHom (A : ValuationSubring Ω) (d : A.decompositionSubgroup K) :
    (algebraMap A Ω).comp (decompRingHom A d) =
      ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (algebraMap A Ω) := by
  ext a
  rfl

variable {R : Type u} [CommRing R] [Algebra R Ω] [Algebra R K] [IsScalarTower R K Ω]

noncomputable def toValuationSubring (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap R Ω r ∈ A) : R →+* A :=
  (algebraMap R Ω).codRestrict A.toSubring hA

theorem algebraMap_comp_toValuationSubring (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap R Ω r ∈ A) :
    (algebraMap A Ω).comp (toValuationSubring A hA) = algebraMap R Ω := by
  ext r; rfl

theorem decompRingHom_comp_toValuationSubring (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap R Ω r ∈ A) (d : A.decompositionSubgroup K) :
    (decompRingHom A d).comp (toValuationSubring A hA) = toValuationSubring A hA := by
  ext r
  change (d : Ω ≃ₐ[K] Ω) (algebraMap R Ω r) = algebraMap R Ω r
  rw [IsScalarTower.algebraMap_apply R K Ω, AlgEquiv.commutes]


end MazurTransfer.PublicProperUnramifiedInertiaHelpers
open MazurTransfer.PublicProperUnramifiedInertiaHelpers

theorem solution
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (φ : J ⟶ J) (hφ : φ ≫ f = f) [FormallyUnramified φ] [LocallyOfFiniteType φ]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ = x.val ≫ φ) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by
  obtain ⟨d, hd, rfl⟩ := exists_of_mem_inertiaSubgroupIn A σ hσ
  let ρ : R →+* A := toValuationSubring A hA
  let ιA : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A Ω))
  let sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom ρ)
  have hιs : ιA ≫ sA = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    simp only [ιA, sA, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f)).1
  let S : ValuativeCommSq f := ⟨A, Ω, x.val, sA, ⟨by rw [x.property, hιs]⟩⟩
  obtain ⟨ly⟩ := (hE S).exists_lift
  let y : Spec (CommRingCat.of A) ⟶ J := ly.l
  have hy₁ : ιA ≫ y = x.val := ly.fac_left
  have hy₂ : y ≫ f = sA := ly.fac_right
  let σA : A →+* A := decompRingHom A d
  let τ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom σA)
  have hτs : τ ≫ sA = sA := by
    simp only [τ, sA, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [decompRingHom_comp_toValuationSubring]
  have hστ : Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ ιA = ιA ≫ τ := by
    simp only [ιA, τ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [algebraMap_comp_decompRingHom]
  have hU : ValuativeCriterion.Uniqueness f := IsSeparated.valuativeCriterion f
  let S' : ValuativeCommSq f := ⟨A, Ω, x.val ≫ φ, sA,
    ⟨by rw [Category.assoc, hφ, x.property, hιs]⟩⟩
  have hyn : y ≫ φ = (τ ≫ y) ≫ φ := by
    let l₁ : S'.commSq.LiftStruct := ⟨y ≫ φ, by rw [← Category.assoc, hy₁], by
      rw [Category.assoc, hφ, hy₂]⟩
    let l₂ : S'.commSq.LiftStruct := ⟨(τ ≫ y) ≫ φ, by
      calc ιA ≫ ((τ ≫ y) ≫ φ)
          = ((ιA ≫ τ) ≫ y) ≫ φ := by simp only [Category.assoc]
        _ = ((Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ ιA) ≫ y) ≫ φ := by rw [← hστ]
        _ = Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ (ιA ≫ y) ≫ φ := by simp only [Category.assoc]
        _ = Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ x.val ≫ φ := by rw [hy₁]
        _ = S'.i₁ := hx,
      by rw [Category.assoc, Category.assoc, hφ, hy₂, hτs]⟩
    have h : l₁ = l₂ := (hU S').elim l₁ l₂
    exact congrArg CommSq.LiftStruct.l h
  have hyτ : y = τ ≫ y := by
    apply AlgebraicGeometry.eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified φ A y (τ ≫ y) hyn
    rw [← Category.assoc]
    congr 1
    simp only [τ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [residue_comp_decompRingHom A d hd]
  calc Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ x.val
      = (Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ ιA) ≫ y := by
        rw [Category.assoc, hy₁]
    _ = ιA ≫ (τ ≫ y) := by rw [hστ, Category.assoc]
    _ = x.val := by rw [← hyτ, hy₁]

#print axioms solution
