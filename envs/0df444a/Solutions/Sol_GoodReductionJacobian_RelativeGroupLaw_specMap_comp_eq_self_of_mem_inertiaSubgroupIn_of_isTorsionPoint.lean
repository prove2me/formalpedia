-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/81d67287-87c1-5ecd-9c87-1f11520090ee

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint.GoodReductionJacobian"
open scoped Pointwise

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.nsmul_succ RelativeGroupLaw.idPoint schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_succ nsmul_natural IsTorsionPoint idPoint schemeNsmul schemeNsmul_over one_natural mul_assoc one inv one_mul inv_mul_cancel mul baseChangeStr baseChangePointToBase baseChangePointToBase_coe baseChange baseChangePointToBase_mul baseChangePointToBase_one genericFibreStr genericFibre fibre formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing"
namespace InertiaOnTorsion
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section RingSide

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

end RingSide

section SchemeSide

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

theorem coe_comp_schemeNsmul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) (n : ℕ) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  exact congrArg Subtype.val h

theorem coe_one_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

theorem coe_comp_schemeNsmul_of_isTorsionPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {x : SchemeHomOver t f} {n : ℕ} (hx : L.IsTorsionPoint t n x) :
    x.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 _)).1 := by
  rw [coe_comp_schemeNsmul, ← coe_one_eq]
  exact congrArg Subtype.val hx

theorem eq_one_of_mul_self_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {a : SchemeHomOver t f} (h : L.mul t a a = a) : a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t a) a := by rw [h]
    _ = L.one t := L.inv_mul_cancel t a

end SchemeSide

section Main

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (K : Type u) [Field K] [Algebra R K]
  {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

theorem specMap_comp_eq_self [IsProper f] (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hx : L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) n x) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by
  obtain ⟨d, hd, rfl⟩ := exists_of_mem_inertiaSubgroupIn A σ hσ

  let ρ : R →+* A := toValuationSubring A hA
  let ιA : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A Ω))
  let sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom ρ)
  have hιs : ιA ≫ sA = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    simp only [ιA, sA, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let e : Spec (CommRingCat.of R) ⟶ J := (L.one (𝟙 _)).1
  have he : e ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f)).1
  let S : ValuativeCommSq f := ⟨A, Ω, x.1, sA, ⟨by rw [x.2, hιs]⟩⟩
  obtain ⟨ly⟩ := (hE S).exists_lift
  let y : Spec (CommRingCat.of A) ⟶ J := ly.l
  have hy₁ : ιA ≫ y = x.1 := ly.fac_left
  have hy₂ : y ≫ f = sA := ly.fac_right

  have hxn : x.1 ≫ L.schemeNsmul n = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ e :=
    coe_comp_schemeNsmul_of_isTorsionPoint L hx
  have hU : ValuativeCriterion.Uniqueness f := IsSeparated.valuativeCriterion f
  let S' : ValuativeCommSq f := ⟨A, Ω, x.1 ≫ L.schemeNsmul n, sA,
    ⟨by rw [Category.assoc, L.schemeNsmul_over, x.2, hιs]⟩⟩
  have hyn : y ≫ L.schemeNsmul n = sA ≫ e := by
    let l₁ : S'.commSq.LiftStruct := ⟨y ≫ L.schemeNsmul n, by
      rw [← Category.assoc, hy₁], by rw [Category.assoc, L.schemeNsmul_over, hy₂]⟩
    let l₂ : S'.commSq.LiftStruct := ⟨sA ≫ e, by rw [← Category.assoc, hιs, ← hxn], by
      rw [Category.assoc, he, Category.comp_id]⟩
    have : l₁ = l₂ := (hU S').elim l₁ l₂
    exact congrArg CommSq.LiftStruct.l this

  let σA : A →+* A := decompRingHom A d
  let τ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom σA)
  have hτs : τ ≫ sA = sA := by
    simp only [τ, sA, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [decompRingHom_comp_toValuationSubring]
  haveI : FormallyUnramified (L.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      L hcomm n hn
  haveI : LocallyOfFiniteType (L.schemeNsmul n) := by
    haveI : LocallyOfFiniteType (L.schemeNsmul n ≫ f) := by
      rw [L.schemeNsmul_over]; infer_instance
    exact locallyOfFiniteType_of_comp _ f
  have hyτ : y = τ ≫ y := by
    refine AlgebraicGeometry.eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
      (L.schemeNsmul n) A y (τ ≫ y) ?_ ?_
    · rw [Category.assoc, hyn, ← Category.assoc, hτs]
    · rw [← Category.assoc]
      congr 1
      simp only [τ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [residue_comp_decompRingHom A d hd]

  have hστ : Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ ιA = ιA ≫ τ := by
    simp only [ιA, τ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [algebraMap_comp_decompRingHom]
  calc Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ x.1
      = (Spec.map (CommRingCat.ofHom ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) ≫ ιA) ≫ y := by
        rw [Category.assoc, hy₁]
    _ = ιA ≫ (τ ≫ y) := by rw [hστ, Category.assoc]
    _ = x.1 := by rw [← hyτ, hy₁]

theorem specMap_comp_eq_self_of_eq [IsProper f] (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    {t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)}
    (ht : t = Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
    (x : SchemeHomOver t f) (hx : L.IsTorsionPoint t n x) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by
  subst ht
  exact specMap_comp_eq_self K L hcomm n hn A hA σ hσ x hx

end Main

section GenericFibre

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

theorem baseChangePointToBase_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).nsmul t' n x) =
      G.nsmul (t' ≫ ι) n (baseChangePointToBase ι x) := by
  induction n with
  | zero => exact baseChangePointToBase_one ι G t'
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, baseChangePointToBase_mul, ih]

theorem isTorsionPoint_baseChangePointToBase (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) {x : SchemeHomOver t' (baseChangeStr ι f)}
    (hx : (G.baseChange ι).IsTorsionPoint t' n x) :
    G.IsTorsionPoint (t' ≫ ι) n (baseChangePointToBase ι x) := by
  show G.nsmul (t' ≫ ι) n (baseChangePointToBase ι x) = G.one (t' ≫ ι)
  rw [← baseChangePointToBase_nsmul, hx, baseChangePointToBase_one]

end GenericFibre

section GenericFibreMain

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (K : Type u) [Field K] [Algebra R K]
  {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

omit [IsLocalRing R] in

theorem specMap_algebraMap_comp_specGenericFibreInclusion :
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ specGenericFibreInclusion R K =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
  rw [specGenericFibreInclusion, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq R K Ω]

theorem specMap_comp_eq_self_genericFibre [IsProper f] (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (genericFibreStr K f))
    (hz : (L.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n z) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ z.1 = z.1 := by
  have hx := isTorsionPoint_baseChangePointToBase (specGenericFibreInclusion R K) L
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n hz
  have h := specMap_comp_eq_self_of_eq K L hcomm n hn A hA σ hσ
    (specMap_algebraMap_comp_specGenericFibreInclusion (R := R) (Ω := Ω) K)
    (baseChangePointToBase (specGenericFibreInclusion R K) z) hx
  rw [baseChangePointToBase_coe] at h
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h
  · rw [Category.assoc, z.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext k
    exact σ.commutes k

end GenericFibreMain

section SubObject

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (K : Type u) [Field K] [Algebra R K]
  {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

theorem schemeHomOverComp_nsmul {S : Type u} [CommRing S]
    {B X : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of S)} {h : X ⟶ Spec (CommRingCat.of S)}
    (LB : RelativeGroupLaw S g) (LX : RelativeGroupLaw S h) (φ : SchemeHomOver g h)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) φ =
        LX.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t g) :
    NeronModelInfra.schemeHomOverComp (LB.nsmul t n x) φ =
      LX.nsmul t n (NeronModelInfra.schemeHomOverComp x φ) := by
  induction n with
  | zero =>
      show NeronModelInfra.schemeHomOverComp (LB.one t) φ = LX.one t
      apply eq_one_of_mul_self_eq LX t
      rw [← hφ, LB.one_mul]
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hφ, ih]

theorem specMap_comp_eq_self_of_mono [IsProper f] (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} (LBK : RelativeGroupLaw K gK)
    (iK : SchemeHomOver gK (genericFibreStr K f)) [Mono iK.1]
    (hiK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t gK),
      NeronModelInfra.schemeHomOverComp (LBK.mul t x y) iK =
        (L.genericFibre K).mul t (NeronModelInfra.schemeHomOverComp x iK)
          (NeronModelInfra.schemeHomOverComp y iK))
    (w : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) gK)
    (hw : LBK.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n w) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ w.1 = w.1 := by
  have hz : (L.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n
      (NeronModelInfra.schemeHomOverComp w iK) := by
    show (L.genericFibre K).nsmul _ n (NeronModelInfra.schemeHomOverComp w iK) = _
    rw [← schemeHomOverComp_nsmul LBK (L.genericFibre K) iK hiK, hw]
    exact (schemeHomOverComp_nsmul LBK (L.genericFibre K) iK hiK _ 0 w)
  have h := specMap_comp_eq_self_genericFibre K L hcomm n hn A hA σ hσ
    (NeronModelInfra.schemeHomOverComp w iK) hz
  rw [NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc] at h
  exact (cancel_mono iK.1).mp h

end SubObject

end GoodReductionJacobian.RelativeGroupLaw.InertiaOnTorsion

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    (K : Type u) [Field K] [Algebra R K]
    {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsProper f] (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hx : L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) n x) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 :=
  GoodReductionJacobian.RelativeGroupLaw.InertiaOnTorsion.specMap_comp_eq_self K L hcomm n hn A hA
    σ hσ x hx

end S_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint (solution)
