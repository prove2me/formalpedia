-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f442ef56-4875-5d1a-bc8c-727669af9892

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open NeronModelInfra (SchemeHomOver)

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
p2m_open "GoodReductionJacobian"

namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_inv_cancel one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul"
p2m_open "GoodReductionJacobian.RelativeGroupLaw"

namespace ClosedSubmonoidC2

section Maps

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)

def const {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : SchemeHomOver t f :=
  GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) s

@[scoped simp]
theorem const_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : (const t s).1 = t ≫ s.1 := rfl

theorem const_pt (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    const (𝟙 (Spec (CommRingCat.of k))) s = s :=
  Subtype.ext (Category.id_comp _)

theorem const_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (const t s) = const t' s :=
  Subtype.ext (by simp [← hψ])

include L in
theorem const_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (s s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    const t (L.mul (𝟙 _) s s') = L.mul t (const t s) (const t s') :=
  L.mul_natural (𝟙 _) t t (Category.comp_id t) s s'

include L in
theorem const_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    const t (L.one (𝟙 _)) = L.one t :=
  L.one_natural (𝟙 _) t t (Category.comp_id t)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) *
      GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show L.mul t' _ _ = L.one t'
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left h

def idPt (f : G ⟶ Spec (CommRingCat.of k)) : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩

theorem comp_idPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp x.1 x.2 (idPt f) = x :=
  Subtype.ext (Category.comp_id _)

def transl (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f (const f s) (idPt f)).1

theorem transl_over (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    transl L s ≫ f = f :=
  (L.mul f (const f s) (idPt f)).2

theorem comp_transl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x.1 ≫ transl L s = (L.mul t (const t s) x).1 := by
  have h := L.mul_natural f t x.1 x.2 (const f s) (idPt f)
  rw [const_transition, comp_idPt] at h
  exact congrArg Subtype.val h

theorem transl_one : transl L (L.one (𝟙 _)) = 𝟙 G := by
  have h := comp_transl L (idPt f) (L.one (𝟙 _))
  rw [const_one, L.one_mul] at h
  simpa [idPt] using h

theorem transl_comp (s s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    transl L s ≫ transl L s' = transl L (L.mul (𝟙 _) s' s) := by
  have h := comp_transl L (L.mul f (const f s) (idPt f)) s'
  rw [← L.mul_assoc, ← const_mul] at h
  exact h

scoped instance isIso_transl (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : IsIso (transl L s) := by
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  refine ⟨⟨transl L (L.inv (𝟙 _) s), ?_, ?_⟩⟩
  · rw [transl_comp, show L.mul (𝟙 _) (L.inv (𝟙 _) s) s = L.one (𝟙 _) from
      L.inv_mul_cancel (𝟙 _) s, transl_one]
  · rw [transl_comp, show L.mul (𝟙 _) s (L.inv (𝟙 _) s) = L.one (𝟙 _) from
      L.mul_inv_cancel (𝟙 _) s, transl_one]

abbrev clpt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G :=
  x.1 (IsLocalRing.closedPoint k)

theorem transl_clpt (x s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    transl L s (clpt x) = clpt (L.mul (𝟙 _) s x) := by
  have h := comp_transl L x s
  rw [const_pt] at h
  show (x.1 ≫ transl L s) (IsLocalRing.closedPoint k) = _
  rw [h]

def invG : G ⟶ G := (L.inv f (idPt f)).1

theorem invG_over : invG L ≫ f = f := (L.inv f (idPt f)).2

theorem comp_invG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) :
    x.1 ≫ invG L = (L.inv t x).1 := by
  have h := inv_natural L f t x.1 x.2 (idPt f)
  rw [comp_idPt] at h
  exact congrArg Subtype.val h

theorem invG_clpt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    invG L (clpt x) = clpt (L.inv (𝟙 _) x) := by
  show (x.1 ≫ invG L) (IsLocalRing.closedPoint k) = _
  rw [comp_invG]

theorem range_kPoint {X : Scheme.{u}} (x : Spec (CommRingCat.of k) ⟶ X) :
    Set.range x = {x (IsLocalRing.closedPoint k)} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rfl
  · rintro rfl; exact ⟨_, rfl⟩

variable [IsAlgClosed k]

theorem exists_clpt_eq {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] {s : X} (hs : IsClosed ({s} : Set X)) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX, x.1 (IsLocalRing.closedPoint k) = s :=
  ⟨⟨pointOfClosedPoint tX s hs, pointOfClosedPoint_comp _ _ _⟩, pointOfClosedPoint_apply _ _ _ _⟩

theorem isClosed_clpt {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX) :
    IsClosed ({x.1 (IsLocalRing.closedPoint k)} : Set X) :=
  (pointEquivClosedPoint tX ⟨x.1, x.2⟩).2

theorem eq_univ_of_forall_clpt_mem {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] {C : Set X} (hC : IsClosed C)
    (h : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX, x.1 (IsLocalRing.closedPoint k) ∈ C) :
    C = Set.univ := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace tX
  have hsub : closedPoints X ⊆ C := by
    intro s hs
    obtain ⟨x, rfl⟩ := exists_clpt_eq tX hs
    exact h x
  apply Set.eq_univ_of_univ_subset
  rw [← closure_closedPoints (X := X)]
  exact closure_minimal hsub hC

theorem range_subset_of_forall_clpt {X Y : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] (φ : X ⟶ Y) {C : Set Y} (hC : IsClosed C)
    (h : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX,
      (x.1 ≫ φ) (IsLocalRing.closedPoint k) ∈ C) :
    Set.range φ ⊆ C := by
  have hpre : φ ⁻¹' C = Set.univ :=
    eq_univ_of_forall_clpt_mem tX (hC.preimage φ.continuous) (fun x => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact h x)
  rintro _ ⟨z, rfl⟩
  have : z ∈ φ ⁻¹' C := hpre ▸ Set.mem_univ z
  exact this

end Maps

section Submonoid

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}}
  {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
  (Z : Set G) (hZ : IsClosed Z)
  (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
    x.1 (IsLocalRing.closedPoint k) ∈ Z → y.1 (IsLocalRing.closedPoint k) ∈ Z →
      (L.mul (𝟙 (Spec (CommRingCat.of k))) x y).1 (IsLocalRing.closedPoint k) ∈ Z)

include hZ hmul in

theorem transl_image_subset (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hs : clpt s ∈ Z) : transl L s '' Z ⊆ Z := by
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  have hZeq : Z = closure (Z ∩ closedPoints G) := by
    rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hZ.isLocallyClosed, hZ.closure_eq]
  conv_lhs => rw [hZeq]
  refine (image_closure_subset_closure_image (transl L s).continuous).trans
    (closure_minimal ?_ hZ)
  rintro _ ⟨z, ⟨hzZ, hzc⟩, rfl⟩
  obtain ⟨x, rfl⟩ := exists_clpt_eq f hzc
  show transl L s (clpt x) ∈ Z
  rw [transl_clpt]
  exact hmul s x hs hzZ

include hZ hmul in

theorem transl_image_eq [QuasiCompact f] (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hs : clpt s ∈ Z) : transl L s '' Z = Z := by

  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian G := {}
  haveI : NoetherianSpace G := IsNoetherian.noetherianSpace
  let φ : G → G := transl L s
  have hφinj : Function.Injective φ := (transl L s).homeomorph.injective
  have hφcl : IsClosedMap φ := (transl L s).homeomorph.isClosedMap
  have hsub : φ '' Z ⊆ Z := transl_image_subset L Z hZ hmul s hs

  have hclosed : ∀ n : ℕ, IsClosed (φ^[n] '' Z) := by
    intro n
    induction n with
    | zero => simpa using hZ
    | succ n ih =>
      rw [Function.iterate_succ', Set.image_comp]
      exact hφcl _ ih
  let F : ℕ → Closeds G := fun n => ⟨φ^[n] '' Z, hclosed n⟩
  have hanti : ∀ n : ℕ, F (n + 1) ≤ F n := by
    intro n
    show φ^[n + 1] '' Z ⊆ φ^[n] '' Z
    rw [Function.iterate_succ, Set.image_comp]
    exact Set.image_mono hsub

  obtain ⟨_, ⟨n, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Closeds G)).has_min (Set.range F) ⟨F 0, 0, rfl⟩
  have heq : F (n + 1) = F n := by
    by_contra hne
    exact hmin (F (n + 1)) ⟨n + 1, rfl⟩ (lt_of_le_of_ne (hanti n) hne)
  have heq' : φ^[n] '' (φ '' Z) = φ^[n] '' Z := by
    have := congrArg (fun C : Closeds G => (C : Set G)) heq
    simp only [F, Function.iterate_succ, Set.image_comp] at this
    exact this
  exact (hφinj.iterate n).image_injective heq'

include hZ hmul in

theorem inv_clpt_mem [QuasiCompact f]
    (hone : clpt (L.one (𝟙 (Spec (CommRingCat.of k)))) ∈ Z)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hs : clpt s ∈ Z) :
    clpt (L.inv (𝟙 _) s) ∈ Z := by
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  have heZ : clpt (L.one (𝟙 _)) ∈ transl L s '' Z := by
    rw [transl_image_eq L Z hZ hmul s hs]; exact hone
  obtain ⟨z, hz, hze⟩ := heZ

  have h2 : transl L s (clpt (L.inv (𝟙 _) s)) = clpt (L.one (𝟙 _)) := by
    rw [transl_clpt, L.mul_inv_cancel (𝟙 _) s]
  have : z = clpt (L.inv (𝟙 _) s) :=
    (transl L s).homeomorph.injective (hze.trans h2.symm)
  rw [← this]; exact hz

end Submonoid

section Subscheme

open AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

abbrev redSub (Z : Closeds G) : Scheme.{u} := (vanishingIdeal Z).subscheme

abbrev redι (Z : Closeds G) : redSub Z ⟶ G := (vanishingIdeal Z).subschemeι

scoped instance isReduced_redSub (Z : Closeds G) : IsReduced (redSub Z) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker Z).1

theorem range_redι (Z : Closeds G) : Set.range (redι Z) = (Z : Set G) := by
  rw [range_subschemeι]
  rfl

theorem redι_apply_mem (Z : Closeds G) (a : redSub Z) : redι Z a ∈ (Z : Set G) := by
  rw [← range_redι Z]
  exact ⟨a, rfl⟩

def redLift (Z : Closeds G) {T : Scheme.{u}} [IsReduced T] (φ : T ⟶ G)
    (hφ : Set.range φ ⊆ Z) : T ⟶ redSub Z :=
  IsClosedImmersion.lift (redι Z) φ (by
    rw [ker_subschemeι]
    exact (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      Z).2 φ hφ)

@[reassoc (attr := simp)]
theorem redLift_ι (Z : Closeds G) {T : Scheme.{u}} [IsReduced T] (φ : T ⟶ G)
    (hφ : Set.range φ ⊆ Z) : redLift Z φ hφ ≫ redι Z = φ :=
  IsClosedImmersion.lift_fac _ _ _

variable (L : RelativeGroupLaw k f) (Z : Closeds G)

def mulMap : pullback (redι Z ≫ f) (redι Z ≫ f) ⟶ G :=
  (L.mul (pullback.fst (redι Z ≫ f) (redι Z ≫ f) ≫ redι Z ≫ f)
    ⟨pullback.fst _ _ ≫ redι Z, by simp only [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ redι Z, by simpa using pullback.condition.symm⟩).1

theorem lift_mulMap {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a b : T ⟶ redSub Z) (ha : a ≫ redι Z ≫ f = t) (hb : b ≫ redι Z ≫ f = t) :
    pullback.lift a b (ha.trans hb.symm) ≫ mulMap L Z =
      (L.mul t ⟨a ≫ redι Z, by simpa using ha⟩ ⟨b ≫ redι Z, by simpa using hb⟩).1 := by
  have hψ : pullback.lift a b (ha.trans hb.symm) ≫
      (pullback.fst (redι Z ≫ f) (redι Z ≫ f) ≫ redι Z ≫ f) = t := by
    rw [pullback.lift_fst_assoc, ha]
  have hnat := L.mul_natural _ t (pullback.lift a b (ha.trans hb.symm)) hψ
    ⟨pullback.fst _ _ ≫ redι Z, by simp only [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ redι Z, by simpa using pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.fst _ _ ≫ redι Z, by simp only [Category.assoc]⟩ : SchemeHomOver _ f) =
      ⟨a ≫ redι Z, by simpa using ha⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_fst])
  have h2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.snd _ _ ≫ redι Z, by simpa using pullback.condition.symm⟩ :
        SchemeHomOver _ f) =
      ⟨b ≫ redι Z, by simpa using hb⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_snd])
  rw [h1, h2] at hnat
  exact congrArg Subtype.val hnat

def ratLift (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hs : clpt s ∈ (Z : Set G)) :
    Spec (CommRingCat.of k) ⟶ redSub Z :=
  redLift Z s.1 (by rw [range_kPoint, Set.singleton_subset_iff]; exact hs)

@[reassoc (attr := simp)]
theorem ratLift_ι (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hs : clpt s ∈ (Z : Set G)) : ratLift Z s hs ≫ redι Z = s.1 :=
  redLift_ι _ _ _

theorem clpt_comp_mem (a : Spec (CommRingCat.of k) ⟶ redSub Z) (ha : (a ≫ redι Z) ≫ f = 𝟙 _) :
    clpt (⟨a ≫ redι Z, ha⟩ : SchemeHomOver (𝟙 _) f) ∈ (Z : Set G) := by
  show (a ≫ redι Z) (IsLocalRing.closedPoint k) ∈ (Z : Set G)
  rw [Scheme.Hom.comp_apply]
  exact redι_apply_mem Z _

def oneH (hone : clpt (L.one (𝟙 (Spec (CommRingCat.of k)))) ∈ (Z : Set G)) :
    Spec (CommRingCat.of k) ⟶ redSub Z :=
  ratLift Z (L.one (𝟙 _)) hone

@[reassoc (attr := simp)]
theorem oneH_ι (hone : clpt (L.one (𝟙 (Spec (CommRingCat.of k)))) ∈ (Z : Set G)) :
    oneH L Z hone ≫ redι Z = (L.one (𝟙 _)).1 :=
  ratLift_ι _ _ _

variable [IsAlgClosed k] [LocallyOfFiniteType f]

theorem isReduced_pullback : IsReduced (pullback (redι Z ≫ f) (redι Z ≫ f)) := by
  haveI : IsLocallyNoetherian (redSub Z) := LocallyOfFiniteType.isLocallyNoetherian (redι Z ≫ f)
  haveI : PerfectField k := IsAlgClosed.perfectField k
  haveI : GeometricallyReduced (redι Z ≫ f) :=
    AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField _
  infer_instance

variable (hone : clpt (L.one (𝟙 (Spec (CommRingCat.of k)))) ∈ (Z : Set G))
  (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
    x.1 (IsLocalRing.closedPoint k) ∈ (Z : Set G) → y.1 (IsLocalRing.closedPoint k) ∈ (Z : Set G) →
      (L.mul (𝟙 (Spec (CommRingCat.of k))) x y).1 (IsLocalRing.closedPoint k) ∈ (Z : Set G))

include hmul in

theorem range_mulMap_subset : Set.range (mulMap L Z) ⊆ (Z : Set G) := by
  refine range_subset_of_forall_clpt (pullback.fst (redι Z ≫ f) (redι Z ≫ f) ≫ redι Z ≫ f)
    (mulMap L Z) Z.2 ?_
  intro ζ
  have ha : (ζ.1 ≫ pullback.fst (redι Z ≫ f) (redι Z ≫ f)) ≫ redι Z ≫ f = 𝟙 _ := by
    simpa only [Category.assoc] using ζ.2
  have hb : (ζ.1 ≫ pullback.snd (redι Z ≫ f) (redι Z ≫ f)) ≫ redι Z ≫ f = 𝟙 _ := by
    rw [Category.assoc, ← pullback.condition]
    exact ζ.2
  have hζ : ζ.1 ≫ mulMap L Z =
      (L.mul (𝟙 _) ⟨(ζ.1 ≫ pullback.fst _ _) ≫ redι Z, by simpa using ha⟩
        ⟨(ζ.1 ≫ pullback.snd _ _) ≫ redι Z, by simpa using hb⟩).1 := by
    have hlift : pullback.lift (ζ.1 ≫ pullback.fst _ _) (ζ.1 ≫ pullback.snd _ _)
        (ha.trans hb.symm) = ζ.1 :=
      pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [← lift_mulMap L Z (𝟙 _) _ _ ha hb, hlift]
  rw [hζ]
  exact hmul _ _ (clpt_comp_mem Z _ (by simpa using ha)) (clpt_comp_mem Z _ (by simpa using hb))

def mulH : pullback (redι Z ≫ f) (redι Z ≫ f) ⟶ redSub Z :=
  haveI := isReduced_pullback Z (f := f)
  redLift Z (mulMap L Z) (range_mulMap_subset L Z hmul)

@[reassoc (attr := simp)]
theorem mulH_ι : mulH L Z hmul ≫ redι Z = mulMap L Z := by
  haveI := isReduced_pullback Z (f := f)
  exact redLift_ι _ _ _

variable [QuasiCompact f]

include hone hmul in

theorem range_ι_invG_subset : Set.range (redι Z ≫ invG L) ⊆ (Z : Set G) := by
  refine range_subset_of_forall_clpt (redι Z ≫ f) (redι Z ≫ invG L) Z.2 ?_
  intro a
  have ha : (a.1 ≫ redι Z) ≫ f = 𝟙 _ := by simpa only [Category.assoc] using a.2
  have h : a.1 ≫ redι Z ≫ invG L = (L.inv (𝟙 _) ⟨a.1 ≫ redι Z, ha⟩).1 := by
    rw [← Category.assoc]
    exact comp_invG L ⟨a.1 ≫ redι Z, ha⟩
  rw [h]
  exact inv_clpt_mem L (Z : Set G) Z.2 hmul hone _ (clpt_comp_mem Z _ ha)

def invH : redSub Z ⟶ redSub Z :=
  redLift Z (redι Z ≫ invG L) (range_ι_invG_subset L Z hone hmul)

@[reassoc (attr := simp)]
theorem invH_ι : invH L Z hone hmul ≫ redι Z = redι Z ≫ invG L := redLift_ι _ _ _

end Subscheme

section Points

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (Z : Closeds G)

def toG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (redι Z ≫ f)) :
    SchemeHomOver t f :=
  ⟨x.1 ≫ redι Z, by rw [Category.assoc]; exact x.2⟩

@[scoped simp]
theorem toG_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (x : SchemeHomOver t (redι Z ≫ f)) : (toG Z x).1 = x.1 ≫ redι Z := rfl

theorem toG_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (toG Z (f := f) (T := T) (t := t)) := by
  intro x y h
  exact Subtype.ext ((cancel_mono (redι Z)).mp (congrArg Subtype.val h))

theorem toG_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (redι Z ≫ f)) :
    toG Z (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (toG Z x) :=
  Subtype.ext (Category.assoc _ _ _)

end Points

section Law

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) (Z : Closeds G)
  (hone : clpt (L.one (𝟙 (Spec (CommRingCat.of k)))) ∈ (Z : Set G))
  (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
    x.1 (IsLocalRing.closedPoint k) ∈ (Z : Set G) → y.1 (IsLocalRing.closedPoint k) ∈ (Z : Set G) →
      (L.mul (𝟙 (Spec (CommRingCat.of k))) x y).1 (IsLocalRing.closedPoint k) ∈ (Z : Set G))

def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (redι Z ≫ f)) :
    SchemeHomOver t (redι Z ≫ f) :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ mulH L Z hmul, by
    rw [Category.assoc, mulH_ι_assoc, ← Category.assoc, lift_mulMap L Z t x.1 y.1 x.2 y.2]
    exact (L.mul t _ _).2⟩

omit [QuasiCompact f] in
theorem toG_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (redι Z ≫ f)) :
    toG Z (mulPt L Z hmul t x y) = L.mul t (toG Z x) (toG Z y) := by
  apply Subtype.ext
  rw [toG_coe]
  show (pullback.lift x.1 y.1 _ ≫ mulH L Z hmul) ≫ redι Z = _
  rw [Category.assoc, mulH_ι, lift_mulMap L Z t x.1 y.1 x.2 y.2]
  rfl

def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (redι Z ≫ f) :=
  ⟨t ≫ oneH L Z hone, by
    rw [Category.assoc, oneH_ι_assoc, (L.one (𝟙 _)).2, Category.comp_id]⟩

omit [IsAlgClosed k] [LocallyOfFiniteType f] [QuasiCompact f] in
theorem toG_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toG Z (onePt L Z hone t) = L.one t := by
  apply Subtype.ext
  rw [toG_coe, ← const_one L t, const_coe]
  show (t ≫ oneH L Z hone) ≫ redι Z = _
  rw [Category.assoc, oneH_ι]

def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (redι Z ≫ f)) :
    SchemeHomOver t (redι Z ≫ f) :=
  ⟨x.1 ≫ invH L Z hone hmul, by
    rw [Category.assoc, invH_ι_assoc, invG_over]
    exact x.2⟩

theorem toG_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t (redι Z ≫ f)) :
    toG Z (invPt L Z hone hmul t x) = L.inv t (toG Z x) := by
  apply Subtype.ext
  rw [toG_coe]
  show (x.1 ≫ invH L Z hone hmul) ≫ redι Z = _
  rw [Category.assoc, invH_ι, ← Category.assoc]
  exact comp_invG L (toG Z x)

def lawH : RelativeGroupLaw k (redι Z ≫ f) where
  mul t x y := mulPt L Z hmul t x y
  one t := onePt L Z hone t
  inv t x := invPt L Z hone hmul t x
  mul_assoc t x y z := by
    apply toG_injective Z
    simp only [toG_mulPt]
    exact L.mul_assoc t _ _ _
  one_mul t x := by
    apply toG_injective Z
    simp only [toG_mulPt, toG_onePt]
    exact L.one_mul t _
  mul_one t x := by
    apply toG_injective Z
    simp only [toG_mulPt, toG_onePt]
    exact L.mul_one t _
  inv_mul_cancel t x := by
    apply toG_injective Z
    simp only [toG_mulPt, toG_invPt, toG_onePt]
    exact L.inv_mul_cancel t _
  mul_natural t t' ψ hψ x y := by
    apply toG_injective Z
    rw [toG_transition]
    simp only [toG_mulPt]
    rw [L.mul_natural t t' ψ hψ, toG_transition, toG_transition]

theorem hom_clause {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (redι Z ≫ f)) :
    NeronModelInfra.schemeHomOverComp ((lawH L Z hone hmul).mul t x y)
        (⟨redι Z, rfl⟩ : SchemeHomOver (redι Z ≫ f) f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (⟨redι Z, rfl⟩ : SchemeHomOver (redι Z ≫ f) f))
        (NeronModelInfra.schemeHomOverComp y (⟨redι Z, rfl⟩ : SchemeHomOver (redι Z ≫ f) f)) :=
  toG_mulPt L Z hmul t x y

end Law

theorem main (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (Z : Set ↥G) (hZ : IsClosed Z)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) ∈ Z)
    (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      x.1 (IsLocalRing.closedPoint k) ∈ Z → y.1 (IsLocalRing.closedPoint k) ∈ Z →
        (L.mul (𝟙 (Spec (CommRingCat.of k))) x y).1 (IsLocalRing.closedPoint k) ∈ Z) :
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧ IsReduced H ∧ Set.range i = Z ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) := by
  let Zc : Closeds G := ⟨Z, hZ⟩
  have hone' : clpt (L.one (𝟙 (Spec (CommRingCat.of k)))) ∈ (Zc : Set G) := hone
  have hmul' : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      x.1 (IsLocalRing.closedPoint k) ∈ (Zc : Set G) → y.1 (IsLocalRing.closedPoint k) ∈ (Zc : Set G) →
        (L.mul (𝟙 (Spec (CommRingCat.of k))) x y).1 (IsLocalRing.closedPoint k) ∈ (Zc : Set G) :=
    hmul
  refine ⟨redSub Zc, redι Zc, lawH L Zc hone' hmul', inferInstance, inferInstance, range_redι Zc,
    ?_⟩
  intro T t x y
  exact hom_clause L Zc hone' hmul' t x y

end ClosedSubmonoidC2
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoidC2"

end RelativeGroupLaw
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoidC2 P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw"

end GoodReductionJacobian
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoidC2 P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoidC2 P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.GoodReductionJacobian"

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (Z : Set ↥G) (hZ : IsClosed Z)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) ∈ Z)
    (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      x.1 (IsLocalRing.closedPoint k) ∈ Z → y.1 (IsLocalRing.closedPoint k) ∈ Z →
        (L.mul (𝟙 (Spec (CommRingCat.of k))) x y).1 (IsLocalRing.closedPoint k) ∈ Z) :
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧ IsReduced H ∧ Set.range i = Z ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :=
  GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoidC2.main k f L Z hZ hone hmul

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem (solution)
