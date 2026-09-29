-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_pullback_unit_equiv_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7cb23a30-a708-5970-bc01-a28d0347e8da

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_pullback_unit_equiv_ker

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace S17Glue

theorem mono_iff_forall_injective_schemeHomOverComp
    {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B} (u : SchemeHomOver g f) :
    Mono u.1 ↔ ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ B),
      Function.Injective (fun x : SchemeHomOver t g => NeronModelInfra.schemeHomOverComp x u) := by
  constructor
  · intro hm T t x y hxy
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h
    exact (cancel_mono u.1).mp h
  · intro h
    refine ⟨fun {T} a b hab => ?_⟩
    have hb : b ≫ g = a ≫ g := by
      rw [← u.2, ← Category.assoc, ← hab, Category.assoc]
    have key := @h T (a ≫ g) ⟨a, rfl⟩ ⟨b, hb⟩ (Subtype.ext (by simpa using hab))
    exact congrArg Subtype.val key

section Hom
variable {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u : SchemeHomOver g f)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))

include hu in
theorem hom_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (LB.one t) u = L.one t := by

  set a := NeronModelInfra.schemeHomOverComp (LB.one t) u with ha
  have haa : L.mul t a a = a := by
    rw [ha, ← hu, LB.one_mul]
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t a) a := by rw [haa]
    _ = L.one t := L.inv_mul_cancel t a

include hu in
theorem hom_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t g) :
    NeronModelInfra.schemeHomOverComp (LB.nsmul t n x) u =
      L.nsmul t n (NeronModelInfra.schemeHomOverComp x u) := by
  induction n with
  | zero => simpa using hom_one LB L u hu t
  | succ n ih => rw [LB.nsmul_succ, L.nsmul_succ, hu, ih]

omit hu in
theorem nsmul_coe_eq_comp_schemeNsmul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (n : ℕ) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (L.nsmul f n RelativeGroupLaw.idPoint)
      = L.nsmul t n (GoodReductionJacobian.schemeHomOverComp x.1 x.2 RelativeGroupLaw.idPoint) :=
    L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hid : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id x.1)
  rw [hid] at h
  exact (congrArg Subtype.val h).symm

include hu in
theorem schemeNsmul_comp (n : ℕ) : LB.schemeNsmul n ≫ u.1 = u.1 ≫ L.schemeNsmul n := by
  have h := hom_nsmul LB L u hu g n RelativeGroupLaw.idPoint
  have hid : NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.idPoint (f := g)) u = ⟨u.1, u.2⟩ :=
    Subtype.ext (Category.id_comp u.1)
  rw [hid] at h
  have h1 := congrArg Subtype.val h
  rw [NeronModelInfra.schemeHomOverComp_coe, nsmul_coe_eq_comp_schemeNsmul L n ⟨u.1, u.2⟩] at h1
  exact h1

include hu in
theorem schemeNsmul_comp_eq_comp_schemeNsmul_of_hom :
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        NeronModelInfra.schemeHomOverComp (LB.one t) u = L.one t) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (LB.nsmul t n x) u =
          L.nsmul t n (NeronModelInfra.schemeHomOverComp x u)) ∧
    (∀ n : ℕ, LB.schemeNsmul n ≫ u.1 = u.1 ≫ L.schemeNsmul n) :=
  ⟨fun t => hom_one LB L u hu t, fun t n x => hom_nsmul LB L u hu t n x,
    fun n => schemeNsmul_comp LB L u hu n⟩

include hu in
theorem isFinite_schemeNsmul_of_isFinite_hom (hufin : IsFinite u.1) (n : ℕ)
    (hfin : IsFinite (L.schemeNsmul n)) : IsFinite (LB.schemeNsmul n) := by
  haveI := hufin; haveI := hfin
  haveI : IsFinite (LB.schemeNsmul n ≫ u.1) := by
    rw [schemeNsmul_comp LB L u hu n]; infer_instance
  haveI : IsSeparated u.1 := inferInstance
  exact IsFinite.of_comp (LB.schemeNsmul n) u.1

omit hu in
theorem one_coe_eq_comp_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h : GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) (L.one (𝟙 _)) = L.one t :=
    L.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

omit hu LB in
theorem exists_schemeHomOver_pullback_unit_equiv_ker :
    ∃ e : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        SchemeHomOver t (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≃
          {x : SchemeHomOver t g // NeronModelInfra.schemeHomOverComp x u = L.one t},
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (y : SchemeHomOver t (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)),
        ((e t y : {x : SchemeHomOver t g // _}) : SchemeHomOver t g).1 =
          y.1 ≫ pullback.fst u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  refine ⟨fun {T} t =>
    { toFun := fun y => ⟨⟨y.1 ≫ pullback.fst u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1, by
          have h1 : pullback.fst u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ g =
              pullback.fst u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u.1 ≫ f := by rw [u.2]
          rw [Category.assoc, h1, ← Category.assoc (pullback.fst _ _), pullback.condition,
            Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id, y.2]⟩, by
          apply Subtype.ext
          rw [NeronModelInfra.schemeHomOverComp_coe, one_coe_eq_comp_one L t, Category.assoc,
            pullback.condition, ← Category.assoc, y.2]⟩
      invFun := fun x => ⟨pullback.lift x.1.1 t (by
          have hx := congrArg Subtype.val x.2
          rw [NeronModelInfra.schemeHomOverComp_coe, one_coe_eq_comp_one L t] at hx
          exact hx), pullback.lift_snd _ _ _⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm
      right_inv := fun x => by
        apply Subtype.ext; apply Subtype.ext
        exact pullback.lift_fst _ _ _ }, fun {T} t y => rfl⟩

end Hom

theorem injective_schemeHomOverComp_of_mono_genericFibreRestrict
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (u : SchemeHomOver g f) [Mono (genericFibreRestrict R K f g u).1]
    {T : Scheme.{u}} (tK : T ⟶ Spec (CommRingCat.of K)) :
    Function.Injective (fun x : SchemeHomOver (tK ≫ specGenericFibreInclusion R K) g =>
      NeronModelInfra.schemeHomOverComp x u) := by
  intro x y hxy
  have h := congrArg Subtype.val hxy
  simp only [NeronModelInfra.schemeHomOverComp_coe] at h
  let lx : T ⟶ pullback g (specGenericFibreInclusion R K) := pullback.lift x.1 tK x.2
  let ly : T ⟶ pullback g (specGenericFibreInclusion R K) := pullback.lift y.1 tK y.2
  have key : lx ≫ (genericFibreRestrict R K f g u).1 = ly ≫ (genericFibreRestrict R K f g u).1 := by
    apply pullback.hom_ext
    · simp only [genericFibreRestrict, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, ← Category.assoc, pullback.lift_fst, pullback.lift_fst, h]
    · simp only [genericFibreRestrict, Category.assoc, pullback.lift_snd]
      rw [pullback.lift_snd, pullback.lift_snd]
  have hl : lx = ly := (cancel_mono _).mp key
  apply Subtype.ext
  have := congrArg (fun m => m ≫ pullback.fst g (specGenericFibreInclusion R K)) hl
  simp only [lx, ly, pullback.lift_fst] at this
  exact this

end S17Glue

theorem solution
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u : SchemeHomOver g f) :
    ∃ e : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        SchemeHomOver t (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≃
          {x : SchemeHomOver t g // NeronModelInfra.schemeHomOverComp x u = L.one t},
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (y : SchemeHomOver t (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)),
        ((e t y : {x : SchemeHomOver t g // _}) : SchemeHomOver t g).1 =
          y.1 ≫ pullback.fst u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  S17Glue.exists_schemeHomOver_pullback_unit_equiv_ker L u

end S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_pullback_unit_equiv_ker
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_pullback_unit_equiv_ker (solution)
