-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/26583df3-9c1f-562f-ae50-0c6ea78115dc

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_smoothOfRelativeDimension
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw

namespace RaynU5

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) (hc : L.IsCommutative) {p h : ℕ} (G : PDivisibleGroup R p h)
variable (T : Type) [CommRing T] [Algebra R T]

structure Glue (e : ∀ v : ℕ,
    G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v)) : Prop where
  mul : ∀ (v : ℕ) (x y : G.Point T v),
    ((e v (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v x).val (e v y).val
  incl : ∀ (v : ℕ) (x : G.Point T v),
    ((e (v + 1) (G.pointIncl T v x)).val : SchemeHomOver _ f) = (e v x).val

variable {e : ∀ v : ℕ,
  G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v)}

def levelFun (_H : Glue L G T e) (v : ℕ) (x : Additive (G.Point T v)) : L.AlgPoints hc T :=
  AlgPoints.ofPoint (e v (Additive.toMul x)).val

theorem toPoint_levelFun (H : Glue L G T e) (v : ℕ) (x : Additive (G.Point T v)) :
    AlgPoints.toPoint (levelFun L hc G T H v x) = (e v (Additive.toMul x)).val := rfl

def levelHom (H : Glue L G T e) (v : ℕ) : Additive (G.Point T v) →+ L.AlgPoints hc T :=
  AddMonoidHom.mk' (levelFun L hc G T H v) fun x y =>
    AlgPoints.toPoint_injective (H.mul v (Additive.toMul x) (Additive.toMul y))

theorem levelHom_apply (H : Glue L G T e) (v : ℕ) (x : Additive (G.Point T v)) :
    levelHom L hc G T H v x = levelFun L hc G T H v x := rfl

theorem levelHom_injective (H : Glue L G T e) (v : ℕ) :
    Function.Injective (levelHom L hc G T H v) := by
  intro x y hxy
  have h1 : (e v (Additive.toMul x)).val = (e v (Additive.toMul y)).val :=
    congrArg AlgPoints.toPoint hxy
  have h2 : e v (Additive.toMul x) = e v (Additive.toMul y) := Subtype.ext h1
  exact congrArg Additive.ofMul ((e v).injective h2)

theorem levelFun_pointInclLE (H : Glue L G T e) {v w : ℕ} (hvw : v ≤ w) (x : G.Point T v) :
    levelFun L hc G T H w (Additive.ofMul (G.pointInclLE T hvw x)) =
      levelFun L hc G T H v (Additive.ofMul x) := by
  induction hvw with
  | refl => rw [G.pointInclLE_self]
  | step hvw ih =>
    rw [G.pointInclLE_succ hvw]
    apply AlgPoints.toPoint_injective
    have h1 := H.incl _ (G.pointInclLE T hvw x)
    have h2 := congrArg AlgPoints.toPoint ih
    exact h1.trans h2

def iota (H : Glue L G T e) : G.Points T →+ L.AlgPoints hc T :=
  AddCommGroup.DirectLimit.lift (fun v => Additive (G.Point T v))
    (fun v w hvw => G.pointsDirectedSystemMap v w hvw) (L.AlgPoints hc T)
    (fun v => levelHom L hc G T H v)
    (fun _ _ hvw x => levelFun_pointInclLE L hc G T H hvw (Additive.toMul x))

theorem iota_pointsMkAdd (H : Glue L G T e) (v : ℕ) (x : G.Point T v) :
    iota L hc G T H (G.pointsMkAdd T v (Additive.ofMul x)) = AlgPoints.ofPoint (e v x).val :=
  AddCommGroup.DirectLimit.lift_of (G := fun v => Additive (G.Point T v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw) (L.AlgPoints hc T)
    (fun v => levelHom L hc G T H v)
    (fun _ _ hvw x => levelFun_pointInclLE L hc G T H hvw (Additive.toMul x)) v (Additive.ofMul x)

theorem iota_injective (H : Glue L G T e) : Function.Injective (iota L hc G T H) :=
  AddCommGroup.DirectLimit.lift_injective (G := fun v => Additive (G.Point T v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw) (L.AlgPoints hc T)
    (fun v => levelHom L hc G T H v)
    (fun _ _ hvw x => levelFun_pointInclLE L hc G T H hvw (Additive.toMul x))
    (fun v => levelHom_injective L hc G T H v)

theorem mem_range_iota (H : Glue L G T e) (y : L.AlgPoints hc T) (n : ℕ)
    (hy : ((p ^ n : ℕ) : ℤ) • y = 0) :
    y ∈ (iota L hc G T H).range := by
  have hy' : AlgPoints.toPoint y ∈ L.torsionSubset _ (p ^ n) := by
    rw [AlgPoints.toPoint_mem_torsionSubset_iff, ← natCast_zsmul]
    exact hy
  refine ⟨G.pointsMkAdd T n (Additive.ofMul ((e n).symm ⟨AlgPoints.toPoint y, hy'⟩)), ?_⟩
  rw [iota_pointsMkAdd, Equiv.apply_symm_apply]
  rfl

theorem iota_smul (H : Glue L G T e)
    (he_nat : ∀ (v : ℕ) (a : T →ₐ[R] T) (x : G.Point T v),
      ((e v (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v x).val.1)
    (σ : T ≃ₐ[R] T) (z : G.Points T) :
    iota L hc G T H (σ • z) = σ • iota L hc G T H z := by
  induction z using PDivisibleGroup.Points.induction_on with
  | ih v x =>
    rw [PDivisibleGroup.Points.smul_pointsMkAdd, iota_pointsMkAdd, iota_pointsMkAdd,
      AlgPoints.smul_ofPoint]
    apply AlgPoints.toPoint_injective
    apply Subtype.ext
    rw [AlgPoints.toPoint_ofPoint, AlgPoints.toPoint_ofPoint, AlgPoints.mapPoint_coe]
    exact he_nat v (σ : T →ₐ[R] T) x

end RaynU5

namespace PDIVSCH13

section Bridge

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

theorem schemeHomOverComp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := by
  apply Subtype.ext
  simp [GoodReductionJacobian.schemeHomOverComp_coe]

theorem nsmul_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [schemeHomOverComp_idPoint] at h
  rw [← h]
  rfl

theorem one_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem isTorsionPoint_iff_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    L.IsTorsionPoint t n x ↔
      x.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [RelativeGroupLaw.isTorsionPoint_def, ← nsmul_val, ← one_val]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem mem_torsionSubset_iff_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    x ∈ L.torsionSubset t n ↔
      x.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  isTorsionPoint_iff_comp L t n x

theorem isClosedImmersion_one [IsSeparated f] :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h2 := (L.one (𝟙 (Spec (CommRingCat.of R)))).2
  have : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) := by
    rw [h2]; infer_instance
  exact IsClosedImmersion.of_comp _ f

end Bridge

section Levels

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) {p h : ℕ} (G : PDivisibleGroup R p h)
  (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
    G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))
  (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (x : G.Point T v),
    ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J)
  (hι : ∀ v : ℕ, ι v =
    (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))).val.1)

include hι in

theorem ι_comp (v : ℕ) :
    ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))) := by
  rw [hι]
  exact (e v (G.level v) _).val.2

include he_nat hι in

theorem val_eq (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v) :
    (e v T x).val.1 =
      Spec.map (CommRingCat.ofHom (PDivisibleGroup.Point.toAlgHom x).toRingHom) ≫ ι v := by
  have hx : G.pointMap (PDivisibleGroup.Point.toAlgHom x) v
      (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v))) = x :=
    PDivisibleGroup.Point.ext fun _ => rfl
  have := he_nat v (G.level v) T (PDivisibleGroup.Point.toAlgHom x)
    (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))
  rw [hx] at this
  rw [hι]
  exact this

include hι in

theorem ι_comp_schemeNsmul (v : ℕ) :
    ι v ≫ L.schemeNsmul (p ^ v) =
      (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have hmem := (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))).2
  rw [mem_torsionSubset_iff_comp] at hmem
  rw [ι_comp L G e ι hι v, hι]
  exact hmem

theorem kernel_fst_comp (n : ℕ) :
    pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f =
      pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h1 : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f =
      pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
        (L.schemeNsmul n ≫ f) := by
    rw [L.schemeNsmul_over]
  have h2 := (L.one (𝟙 (Spec (CommRingCat.of R)))).2
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc, h2, Category.comp_id]

include he_nat hι in

theorem isIso_lift (hfin : ∀ v : ℕ, IsFinite (L.schemeNsmul (p ^ v))) (v : ℕ)
    (h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) :
    IsIso (pullback.lift (f := L.schemeNsmul (p ^ v))
      (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1) (ι v) (ι v ≫ f) h3) := by
  classical
  haveI := hfin v

  set N := L.schemeNsmul (p ^ v) with hN
  set o := (L.one (𝟙 (Spec (CommRingCat.of R)))).1 with ho
  set k₁ := pullback.fst N o with hk₁
  set k₂ := pullback.snd N o with hk₂
  have hk : k₁ ≫ f = k₂ := kernel_fst_comp L (p ^ v)

  haveI : IsAffine (pullback N o) := inferInstance
  set B : CommRingCat := Γ(pullback N o, ⊤) with hB
  let eK : pullback N o ≅ Spec B := (pullback N o).isoSpec

  let φ : CommRingCat.of R ⟶ B := Spec.preimage (eK.inv ≫ k₂)
  letI : Algebra R B := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R B)) = eK.inv ≫ k₂ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

  let PB : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) f :=
    ⟨eK.inv ≫ k₁, by rw [Category.assoc, hk, hφ]⟩
  have hPB : PB ∈ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R B))) (p ^ v) := by
    rw [mem_torsionSubset_iff_comp]
    change (eK.inv ≫ k₁) ≫ N = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ o
    rw [hφ, Category.assoc, Category.assoc, pullback.condition]
  let xB : G.Point B v := (e v B).symm ⟨PB, hPB⟩
  have hxB : (e v B xB).val.1 = eK.inv ≫ k₁ := by
    simp only [xB, Equiv.apply_symm_apply]
    rfl
  let ψ : G.level v →ₐ[R] B := PDivisibleGroup.Point.toAlgHom xB
  let inv : pullback N o ⟶ Spec (CommRingCat.of (G.level v)) :=
    eK.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)

  have hinvι : inv ≫ ι v = k₁ := by
    have := val_eq L G e he_nat ι hι v B xB
    rw [hxB] at this
    change (eK.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) ≫ ι v = k₁
    rw [Category.assoc, ← this, Iso.hom_inv_id_assoc]
  set lift := pullback.lift (f := N) (g := o) (ι v) (ι v ≫ f) h3 with hlift

  have h₁ : inv ≫ lift = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact hinvι
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, ← Category.assoc, hinvι]
      exact hk

  have h₂ : lift ≫ inv = 𝟙 _ := by
    set c := lift ≫ inv with hc
    let χ : CommRingCat.of (G.level v) ⟶ CommRingCat.of (G.level v) := Spec.preimage c
    have hχc : Spec.map χ = c := Spec.map_preimage c

    have hcover : c ≫ Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))) := by
      rw [← ι_comp L G e ι hι v, hc, Category.assoc, ← Category.assoc inv, hinvι,
        ← Category.assoc, pullback.lift_fst]
    have hχalg : (CommRingCat.ofHom (algebraMap R (G.level v))) ≫ χ =
        CommRingCat.ofHom (algebraMap R (G.level v)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hχc]
      exact hcover
    let χₐ : G.level v →ₐ[R] G.level v :=
      { χ.hom with
        commutes' := fun r => by
          have := congrArg (fun g => (CommRingCat.Hom.hom g) r) hχalg
          simpa using this }
    have hχₐ : CommRingCat.ofHom χₐ.toRingHom = χ := by
      ext a; rfl

    have hval : (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom χₐ)).val.1 =
        (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))).val.1 := by
      rw [val_eq L G e he_nat ι hι, ← hι, PDivisibleGroup.Point.toAlgHom_ofAlgHom, hχₐ, hχc, hc,
        Category.assoc, hinvι, pullback.lift_fst]
    have heq : PDivisibleGroup.Point.ofAlgHom χₐ =
        (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)) : G.Point (G.level v) v) :=
      (e v (G.level v)).injective (Subtype.ext (Subtype.ext hval))
    have hχid : χₐ = AlgHom.id R (G.level v) := by
      have := congrArg PDivisibleGroup.Point.toAlgHom heq
      simpa using this
    have : χ = 𝟙 _ := by
      rw [← hχₐ, hχid]
      rfl
    rw [← hχc, this, Spec.map_id]
  exact ⟨inv, h₂, h₁⟩

include he_nat hι in

theorem isClosedImmersion_ι [IsSeparated f] (hfin : ∀ v : ℕ, IsFinite (L.schemeNsmul (p ^ v)))
    (v : ℕ) : IsClosedImmersion (ι v) := by
  have h3 := ι_comp_schemeNsmul L G e ι hι v
  haveI := isIso_lift L G e he_nat ι hι hfin v h3
  haveI : IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := isClosedImmersion_one L
  haveI : IsClosedImmersion
      (pullback.fst (L.schemeNsmul (p ^ v)) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  rw [← pullback.lift_fst (f := L.schemeNsmul (p ^ v))
    (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1) (ι v) (ι v ≫ f) h3]
  infer_instance

end Levels

end PDIVSCH13

namespace PDIVSCH13

section Hom

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

theorem eq_one_of_mul_self {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a : SchemeHomOver t f} (h : L.mul t a a = a) : a = L.one t := by
  have h' := congrArg (L.mul t (L.inv t a)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at h'
  exact h'

variable (E : SchemeHomOver f f)
  (hE : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
    NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
      L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E))

include hE in
theorem comp_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (L.one t) E = L.one t := by
  apply eq_one_of_mul_self L
  have := hE t (L.one t) (L.one t)
  rw [L.one_mul] at this
  exact this.symm

include hE in
theorem comp_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.nsmul t n x) E =
      L.nsmul t n (NeronModelInfra.schemeHomOverComp x E) := by
  induction n with
  | zero => exact comp_one L E hE t
  | succ n ih => rw [L.nsmul_succ, hE, ih, L.nsmul_succ]

include hE in
theorem isTorsionPoint_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    {x : SchemeHomOver t f} (hx : L.IsTorsionPoint t n x) :
    L.IsTorsionPoint t n (NeronModelInfra.schemeHomOverComp x E) := by
  rw [RelativeGroupLaw.isTorsionPoint_def] at hx ⊢
  rw [← comp_nsmul L E hE, hx, comp_one L E hE]

end Hom

section Endo

open PDivisibleGroup Bialgebra
p2m_open_scoped "TensorProduct Bialgebra.TensorProduct"

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) {p h : ℕ} (G : PDivisibleGroup R p h)
  (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
    G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))
  (he_mul : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x y : G.Point T v),
    ((e v T (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v T x).val (e v T y).val)
  (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (x : G.Point T v),
    ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1)
  (he_incl : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v),
    ((e (v + 1) T (G.pointIncl T v x)).val : SchemeHomOver _ f) = (e v T x).val)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J)
  (hι : ∀ v : ℕ, ι v =
    (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))).val.1)
  (E : SchemeHomOver f f)
  (hE : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
    NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
      L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E))

noncomputable def act (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v) :
    G.Point T v :=
  (e v T).symm ⟨NeronModelInfra.schemeHomOverComp (e v T x).val E,
    isTorsionPoint_comp L E hE _ _ (e v T x).2⟩

theorem e_act_val (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v) :
    ((e v T (act L G e E hE v T x)).val : SchemeHomOver _ f) =
      NeronModelInfra.schemeHomOverComp (e v T x).val E := by
  unfold act
  rw [Equiv.apply_symm_apply]

theorem e_act_val_coe (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v) :
    (e v T (act L G e E hE v T x)).val.1 = (e v T x).val.1 ≫ E.1 := by
  rw [e_act_val]
  rfl

noncomputable def φ₀ (v : ℕ) : G.level v →ₐ[R] G.level v :=
  Point.toAlgHom (act L G e E hE v (G.level v) (Point.ofAlgHom (AlgHom.id R (G.level v))))

include he_nat hι in
theorem specMap_φ₀_comp_ι (v : ℕ) :
    Spec.map (CommRingCat.ofHom (φ₀ L G e E hE v).toRingHom) ≫ ι v = ι v ≫ E.1 := by
  have h1 := val_eq L G e he_nat ι hι v (G.level v)
    (act L G e E hE v (G.level v) (Point.ofAlgHom (AlgHom.id R (G.level v))))
  rw [e_act_val_coe, ← hι] at h1
  exact h1.symm

include he_nat hι in

theorem act_eq (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v) :
    act L G e E hE v T x = Point.ofAlgHom ((Point.toAlgHom x).comp (φ₀ L G e E hE v)) := by
  apply (e v T).injective
  apply Subtype.ext
  apply Subtype.ext
  rw [e_act_val_coe, val_eq L G e he_nat ι hι v T x,
    val_eq L G e he_nat ι hι v T (Point.ofAlgHom _), Point.toAlgHom_ofAlgHom]
  change _ = Spec.map (CommRingCat.ofHom (φ₀ L G e E hE v).toRingHom ≫
    CommRingCat.ofHom (Point.toAlgHom x).toRingHom) ≫ ι v
  rw [Spec.map_comp]
  simp only [Category.assoc]
  rw [specMap_φ₀_comp_ι L G e he_nat ι hι E hE v]

include he_mul in
theorem act_mul (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x y : G.Point T v) :
    act L G e E hE v T (x * y) = act L G e E hE v T x * act L G e E hE v T y := by
  apply (e v T).injective
  apply Subtype.ext
  rw [e_act_val, he_mul, hE, he_mul, e_act_val, e_act_val]

include he_mul in
theorem act_one (v : ℕ) (T : Type) [CommRing T] [Algebra R T] :
    act L G e E hE v T (1 : G.Point T v) = 1 := by
  have h1 := act_mul L G e he_mul E hE v T (1 : G.Point T v) 1
  rw [_root_.mul_one] at h1
  have h2 : act L G e E hE v T 1 * act L G e E hE v T 1 = act L G e E hE v T 1 * 1 := by
    rw [_root_.mul_one]; exact h1.symm
  exact mul_left_cancel h2

include he_mul he_nat hι in

theorem counit_comp_φ₀ (v : ℕ) :
    (counitAlgHom R (G.level v)).comp (φ₀ L G e E hE v) = counitAlgHom R (G.level v) := by
  have h1 := act_one L G e he_mul E hE v R
  rw [act_eq L G e he_nat ι hι E hE] at h1
  have h2 := congrArg Point.toAlgHom h1
  rw [Point.toAlgHom_ofAlgHom] at h2
  have h3 : Point.toAlgHom (1 : G.Point R v) = counitAlgHom R (G.level v) := by
    apply AlgHom.ext
    intro a
    rw [Point.one_apply, counitAlgHom_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h3] at h2
  exact h2

include he_mul he_nat hι in

theorem map_comp_comul_φ₀ (v : ℕ) :
    (Algebra.TensorProduct.map (φ₀ L G e E hE v) (φ₀ L G e E hE v)).comp
        (comulAlgHom R (G.level v)) =
      (comulAlgHom R (G.level v)).comp (φ₀ L G e E hE v) := by
  have h1 := act_mul L G e he_mul E hE v (G.level v ⊗[R] G.level v)
    (Point.ofAlgHom
      (Algebra.TensorProduct.includeLeft : G.level v →ₐ[R] G.level v ⊗[R] G.level v))
    (Point.ofAlgHom
      (Algebra.TensorProduct.includeRight : G.level v →ₐ[R] G.level v ⊗[R] G.level v))
  rw [act_eq L G e he_nat ι hι E hE, act_eq L G e he_nat ι hι E hE,
    act_eq L G e he_nat ι hι E hE] at h1
  have h2 := congrArg Point.toAlgHom h1
  rw [Point.toAlgHom_ofAlgHom] at h2
  apply AlgHom.ext
  intro a
  have h3 := congrArg (fun F : G.level v →ₐ[R] G.level v ⊗[R] G.level v => F a) h2
  simp only [AlgHom.comp_apply, Point.mul_apply, Point.toAlgHom_ofAlgHom] at h3

  have hl : ∀ hc, Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft : G.level v →ₐ[R] G.level v ⊗[R] G.level v)
      (Algebra.TensorProduct.includeRight : G.level v →ₐ[R] G.level v ⊗[R] G.level v) hc =
        AlgHom.id R (G.level v ⊗[R] G.level v) :=
    fun hc => Algebra.TensorProduct.ext' fun a b => by simp
  have hr : ∀ hc, Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : G.level v →ₐ[R] G.level v ⊗[R] G.level v).comp
        (φ₀ L G e E hE v))
      ((Algebra.TensorProduct.includeRight : G.level v →ₐ[R] G.level v ⊗[R] G.level v).comp
        (φ₀ L G e E hE v)) hc =
        Algebra.TensorProduct.map (φ₀ L G e E hE v) (φ₀ L G e E hE v) :=
    fun hc => Algebra.TensorProduct.ext' fun a b => by simp [Algebra.TensorProduct.map_tmul]
  rw [hl, hr] at h3
  rw [AlgHom.comp_apply, AlgHom.comp_apply, comulAlgHom_apply, comulAlgHom_apply]
  exact h3.symm

noncomputable def φ (v : ℕ) : G.level v →ₐc[R] G.level v :=
  BialgHom.ofAlgHom (φ₀ L G e E hE v) (counit_comp_φ₀ L G e he_mul he_nat ι hι E hE v)
    (map_comp_comul_φ₀ L G e he_mul he_nat ι hι E hE v)

theorem φ_toAlgHom (v : ℕ) :
    (φ L G e he_mul he_nat ι hι E hE v : G.level v →ₐ[R] G.level v) = φ₀ L G e E hE v := by
  apply AlgHom.ext
  intro a
  rfl

theorem φ_toRingHom (v : ℕ) :
    (φ L G e he_mul he_nat ι hι E hE v : G.level v →+* G.level v) = (φ₀ L G e E hE v).toRingHom := by
  apply RingHom.ext
  intro a
  rfl

include he_incl in

theorem act_pointIncl (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v) :
    act L G e E hE (v + 1) T (G.pointIncl T v x) = G.pointIncl T v (act L G e E hE v T x) := by
  apply (e (v + 1) T).injective
  apply Subtype.ext
  rw [e_act_val, he_incl, he_incl, e_act_val]

include he_incl in

theorem transition_comp_φ (v : ℕ) :
    (G.transition v).comp (φ L G e he_mul he_nat ι hι E hE (v + 1)) =
      (φ L G e he_mul he_nat ι hι E hE v).comp (G.transition v) := by
  apply BialgHom.coe_algHom_injective
  rw [BialgHom.comp_toAlgHom, BialgHom.comp_toAlgHom, φ_toAlgHom, φ_toAlgHom]
  have h1 := act_pointIncl L G e he_incl E hE v (G.level v)
    (Point.ofAlgHom (AlgHom.id R (G.level v)))
  rw [act_eq L G e he_nat ι hι E hE, act_eq L G e he_nat ι hι E hE] at h1
  have h2 := congrArg Point.toAlgHom h1
  rw [Point.toAlgHom_ofAlgHom, toAlgHom_pointIncl, toAlgHom_pointIncl,
    Point.toAlgHom_ofAlgHom, Point.toAlgHom_ofAlgHom, AlgHom.id_comp] at h2
  exact h2

include L e he_mul he_nat he_incl hι hE in

theorem exists_bialgHom_restrict :
    ∃ φ : ∀ v : ℕ, G.level v →ₐc[R] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (G.transition v)) ∧
      ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : G.level v →+* G.level v)) ≫ ι v = ι v ≫ E.1 :=
  ⟨φ L G e he_mul he_nat ι hι E hE, transition_comp_φ L G e he_mul he_nat he_incl ι hι E hE,
    fun v => by
      rw [φ_toRingHom]
      exact specMap_φ₀_comp_ι L G e he_nat ι hι E hE v⟩

end Endo

end PDIVSCH13

namespace PDIVSCH3

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) {p h : ℕ} (G : PDivisibleGroup R p h)
variable (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
    G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))

def u (v : ℕ) : G.Point (G.level v) v := PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v))

def ι (v : ℕ) : Spec (CommRingCat.of (G.level v)) ⟶ J := (e v (G.level v) (u G v)).val.1

theorem ι_def (v : ℕ) : ι L G e v = (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))).val.1 := rfl

theorem val_eq_specMap_comp_ι
    (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (x : G.Point T v),
      ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1)
    (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v) :
    ((e v T x).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] T) : G.level v →+* T)) ≫ ι L G e v := by
  have hx : G.pointMap (PDivisibleGroup.Point.toAlgHom x) v (u G v) = x := by
    show PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (AlgHom.id R (G.level v))) = x
    rw [AlgHom.comp_id]; rfl
  have h := he_nat v (G.level v) T (PDivisibleGroup.Point.toAlgHom x) (u G v)
  rw [hx] at h
  exact h

end PDIVSCH3

open RaynU5 PDIVSCH3 in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f]
    (p h : ℕ)
    (hfin : ∀ v : ℕ, IsFinite (L.schemeNsmul (p ^ v)))
    (hflat : ∀ v : ℕ, Flat (L.schemeNsmul (p ^ v)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra R Ω]
    (hcard : ∀ v : ℕ,
      Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) ((p ^ v : ℕ) : ℤ)) = p ^ (v * h)) :
    ∃ G : PDivisibleGroup R p h, G.HasDimension d ∧
      ∃ (ιG : G.Points Ω →+ L.AlgPoints hc Ω)
        (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J),

        Function.Injective ιG ∧
        (∀ (σ : Ω ≃ₐ[R] Ω) (x : G.Points Ω), ιG (σ • x) = σ • ιG x) ∧
        (∀ (e : L.AlgPoints hc Ω) (n : ℕ), ((p ^ n : ℕ) : ℤ) • e = 0 → e ∈ ιG.range) ∧

        (∀ v : ℕ, ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v)))) ∧

        (∀ v : ℕ, IsClosedImmersion (ι v)) ∧

        (∀ v : ℕ, ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧

        (∀ (v : ℕ) (x : G.Point Ω v),
          (GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint (ιG (G.pointsMkAdd Ω v (Additive.ofMul x)))).1 =
            Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] Ω) : G.level v →+* Ω)) ≫ ι v) ∧

        (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B v)
          (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
            Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
            Spec.map (CommRingCat.ofHom (algebraMap R B))),
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v =
            (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

        (∀ v : ℕ, Spec.map (CommRingCat.ofHom (G.transition v : G.level (v + 1) →+* G.level v)) ≫ ι (v + 1) = ι v) ∧

        (∀ (E : SchemeHomOver f f),
          (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
            NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
              L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
          ∃ φ : ∀ v : ℕ, G.level v →ₐc[R] G.level v,
            (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (G.transition v)) ∧
            ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : G.level v →+* G.level v)) ≫ ι v = ι v ≫ E.1) ∧

        (∀ (v : ℕ)
          (h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1),
          IsIso (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3)) := by
  classical

  have hcard' : ∀ v : ℕ,
      Nat.card (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (p ^ v)) = p ^ (v * h) := fun v => by
    rw [← AlgPoints.natCard_torsionBy (hc := hc)]
    exact hcard v
  obtain ⟨G, e, he_mul, he_nat, he_incl⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat
      L hc p h hfin hflat Ω hcard'
  have hdim : G.HasDimension d :=
    GoodReductionJacobian.RelativeGroupLaw.hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension
      L d G e he_mul he_nat
  have H : Glue L G Ω (fun v => e v Ω) := ⟨fun v => he_mul v Ω, fun v => he_incl v Ω⟩
  have hpt := val_eq_specMap_comp_ι L G e he_nat
  refine ⟨G, hdim, iota L hc G Ω H, ι L G e, iota_injective L hc G Ω H, ?_, ?_, ?S1, ?S2, ?S3, ?S4, ?S5, ?S6, ?S7, ?S8⟩
  · exact iota_smul L hc G Ω H (fun v a x => he_nat v Ω Ω a x)
  · exact fun y n hy => mem_range_iota L hc G Ω H y n hy
  case S1 =>
    intro v
    exact (e v (G.level v) (u G v)).val.2
  case S2 => exact fun v => PDIVSCH13.isClosedImmersion_ι L G e he_nat (ι L G e) (fun _ => rfl) hfin v
  case S3 =>
    intro v

    have hX : L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R (G.level v)))) (p ^ v) (e v (G.level v) (u G v)).val =
        L.one (Spec.map (CommRingCat.ofHom (algebraMap R (G.level v)))) := (e v (G.level v) (u G v)).2
    have hid : schemeHomOverComp (e v (G.level v) (u G v)).val.1 (e v (G.level v) (u G v)).val.2 (idPoint (f := f)) =
        (e v (G.level v) (u G v)).val := Subtype.ext (Category.comp_id _)
    have hn := L.nsmul_natural f (Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))))
      (e v (G.level v) (u G v)).val.1 (e v (G.level v) (u G v)).val.2 (p ^ v) idPoint
    rw [hid, hX] at hn
    have h1 : ι L G e v ≫ L.schemeNsmul (p ^ v) =
        (schemeHomOverComp (e v (G.level v) (u G v)).val.1 (e v (G.level v) (u G v)).val.2
          (L.nsmul f (p ^ v) idPoint)).1 := rfl
    rw [h1, hn]
    have h2 := L.one_natural (𝟙 (Spec (CommRingCat.of R))) (Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (G.level v)))) (Category.comp_id _)
    rw [← h2]
    show Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))) ≫ _ = _
    rw [← (e v (G.level v) (u G v)).val.2]
    rfl
  case S4 =>
    intro v x
    rw [iota_pointsMkAdd, AlgPoints.toPoint_ofPoint]
    exact hpt v Ω x
  case S5 =>
    intro v B _ _ x y hx hy
    have hm := he_mul v B x y
    have h1 : ((e v B (x * y)).val : SchemeHomOver _ f).1 = (L.mul _ (e v B x).val (e v B y).val).1 := congrArg Subtype.val hm
    rw [hpt v B (x * y)] at h1
    rw [h1]
    have ex : (e v B x).val = ⟨_, hx⟩ := Subtype.ext (hpt v B x)
    have ey : (e v B y).val = ⟨_, hy⟩ := Subtype.ext (hpt v B y)
    rw [ex, ey]
  case S6 =>
    intro v
    have h1 := congrArg Subtype.val (he_incl v (G.level v) (u G v))
    rw [hpt (v + 1) (G.level v) (G.pointIncl (G.level v) v (u G v))] at h1

    exact h1
  case S7 => exact fun E hE => PDIVSCH13.exists_bialgHom_restrict L G e he_mul he_nat he_incl (ι L G e) (fun _ => rfl) E hE
  case S8 => exact fun v h3 => PDIVSCH13.isIso_lift L G e he_nat (ι L G e) (fun _ => rfl) hfin v h3

end
end S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_smoothOfRelativeDimension (solution)
