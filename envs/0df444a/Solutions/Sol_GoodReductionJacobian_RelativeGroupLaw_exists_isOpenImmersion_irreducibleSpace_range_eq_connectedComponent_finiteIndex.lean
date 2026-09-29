-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b525a0d9-f5dc-5a4d-8561-e12e731225f4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace

noncomputable section

universe u

namespace P2mIdentityComponent

section Maps

variable {k : Type u} [Field k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  (LN : RelativeGroupLaw k gN)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def const {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s : SchemeHomOver pt gN) :
    SchemeHomOver t gN :=
  GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) s

@[scoped simp]
theorem const_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s : SchemeHomOver pt gN) :
    (const t s).1 = t ≫ s.1 := rfl

theorem const_pt (s : SchemeHomOver pt gN) : const pt s = s :=
  Subtype.ext (Category.id_comp _)

theorem const_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (s : SchemeHomOver pt gN) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (const t s) = const t' s :=
  Subtype.ext (by simp [← hψ])

theorem const_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s s' : SchemeHomOver pt gN) :
    const t (LN.mul pt s s') = LN.mul t (const t s) (const t s') :=
  LN.mul_natural pt t t (Category.comp_id t) s s'

theorem const_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    const t (LN.one pt) = LN.one t :=
  LN.one_natural pt t t (Category.comp_id t)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t gN) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x) =
      LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := LN.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x) *
      GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show LN.mul t' _ _ = LN.one t'
    rw [← LN.mul_natural t t' ψ hψ, LN.inv_mul_cancel, LN.one_natural]
  exact eq_inv_of_mul_eq_one_left h

def transl (s : SchemeHomOver pt gN) : N ⟶ N :=
  (LN.mul gN (const gN s) RelativeGroupLaw.idPoint).1

theorem comp_transl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t gN)
    (s : SchemeHomOver pt gN) : x.1 ≫ transl LN s = (LN.mul t (const t s) x).1 := by
  have h := LN.mul_natural gN t x.1 x.2 (const gN s) RelativeGroupLaw.idPoint
  have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (const gN s) = const t s :=
    const_transition gN t x.1 x.2 s
  have h2 : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (RelativeGroupLaw.idPoint : SchemeHomOver gN gN) = x :=
    Subtype.ext (Category.comp_id _)
  rw [h1, h2] at h
  exact congrArg Subtype.val h

theorem transl_one : transl LN (LN.one pt) = 𝟙 N := by
  have h := comp_transl LN (RelativeGroupLaw.idPoint : SchemeHomOver gN gN) (LN.one pt)
  rw [const_one, LN.one_mul] at h
  simpa using h

theorem transl_comp (s s' : SchemeHomOver pt gN) :
    transl LN s ≫ transl LN s' = transl LN (LN.mul pt s' s) := by
  have h := comp_transl LN (LN.mul gN (const gN s) RelativeGroupLaw.idPoint) s'
  rw [← LN.mul_assoc, ← const_mul] at h
  exact h

scoped instance isIso_transl (s : SchemeHomOver pt gN) : IsIso (transl LN s) := by
  letI := LN.pointGroup pt
  refine ⟨⟨transl LN (LN.inv pt s), ?_, ?_⟩⟩
  · rw [transl_comp, show LN.mul pt (LN.inv pt s) s = LN.one pt from LN.inv_mul_cancel pt s,
      transl_one]
  · rw [transl_comp, show LN.mul pt s (LN.inv pt s) = LN.one pt from LN.mul_inv_cancel pt s,
      transl_one]

abbrev clpt (x : SchemeHomOver pt gN) : N := x.1 (IsLocalRing.closedPoint k)

theorem transl_clpt (x s : SchemeHomOver pt gN) :
    transl LN s (clpt x) = clpt (LN.mul pt s x) := by
  have h := comp_transl LN x s
  rw [const_pt] at h
  show (x.1 ≫ transl LN s) (IsLocalRing.closedPoint k) = _
  rw [h]

theorem range_coe_eq (x : SchemeHomOver pt gN) : Set.range x.1 = {clpt x} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [this]; rfl
  · rintro rfl; exact ⟨_, rfl⟩

def invN : N ⟶ N := (LN.inv gN RelativeGroupLaw.idPoint).1

theorem comp_invN {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t gN) :
    x.1 ≫ invN LN = (LN.inv t x).1 := by
  have h := inv_natural LN gN t x.1 x.2 RelativeGroupLaw.idPoint
  have h2 : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (RelativeGroupLaw.idPoint : SchemeHomOver gN gN) = x :=
    Subtype.ext (Category.comp_id _)
  rw [h2] at h
  exact congrArg Subtype.val h

theorem invN_invN : invN LN ≫ invN LN = 𝟙 N := by
  letI := LN.pointGroup gN
  have h := comp_invN LN (LN.inv gN RelativeGroupLaw.idPoint)
  rw [show LN.inv gN (LN.inv gN RelativeGroupLaw.idPoint) = RelativeGroupLaw.idPoint from
    inv_inv (RelativeGroupLaw.idPoint : SchemeHomOver gN gN)] at h
  exact h

scoped instance isIso_invN : IsIso (invN LN) := ⟨⟨invN LN, invN_invN LN, invN_invN LN⟩⟩

theorem invN_clpt (x : SchemeHomOver pt gN) : invN LN (clpt x) = clpt (LN.inv pt x) := by
  show (x.1 ≫ invN LN) (IsLocalRing.closedPoint k) = _
  rw [comp_invN]

end Maps

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

theorem image_mem_irreducibleComponents (h : α ≃ₜ β) {Z : Set α}
    (hZ : Z ∈ irreducibleComponents α) : h '' Z ∈ irreducibleComponents β := by
  refine ⟨hZ.1.image h h.continuous.continuousOn, fun W hW hZW => ?_⟩
  have h1 : IsIrreducible (h.symm '' W) := hW.image h.symm h.symm.continuous.continuousOn
  have h2 : Z ⊆ h.symm '' W := by
    intro z hz
    exact ⟨h z, hZW ⟨z, hz, rfl⟩, h.symm_apply_apply z⟩
  have h3 : h.symm '' W ⊆ Z := hZ.2 h1 h2
  intro w hw
  exact ⟨h.symm w, h3 ⟨w, hw, rfl⟩, h.apply_symm_apply w⟩

end Topology

section Component

variable {k : Type u} [Field k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}

open AlgebraicGeometry.Scheme.IdealSheafData

abbrev redSub (Z : Closeds N) : Scheme.{u} := (vanishingIdeal Z).subscheme

abbrev redι (Z : Closeds N) : redSub Z ⟶ N := (vanishingIdeal Z).subschemeι

scoped instance isReduced_redSub (Z : Closeds N) : IsReduced (redSub Z) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker Z).1

theorem range_redι (Z : Closeds N) : Set.range (redι Z) = (Z : Set N) := by
  rw [range_subschemeι]
  rfl

def redLift (Z : Closeds N) {T : Scheme.{u}} [IsReduced T] (f : T ⟶ N)
    (hf : Set.range f ⊆ Z) : T ⟶ redSub Z :=
  IsClosedImmersion.lift (redι Z) f (by
    rw [ker_subschemeι]
    exact (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      Z).2 f hf)

@[reassoc (attr := simp)]
theorem redLift_ι (Z : Closeds N) {T : Scheme.{u}} [IsReduced T] (f : T ⟶ N)
    (hf : Set.range f ⊆ Z) : redLift Z f hf ≫ redι Z = f :=
  IsClosedImmersion.lift_fac _ _ _

theorem irreducibleSpace_redSub {Z : Closeds N} (hZ : IsIrreducible (Z : Set N)) :
    IrreducibleSpace (redSub Z) := by
  have h : IsIrreducible (Set.range (redι Z)) := by rwa [range_redι]
  have e : Set.range (redι Z) ≃ₜ redSub Z :=
    ((redι Z).isEmbedding.toHomeomorph).symm
  haveI := Subtype.irreducibleSpace h
  exact e.irreducibleSpace_iff.mp inferInstance

theorem isIntegral_redSub {Z : Closeds N} (hZ : IsIrreducible (Z : Set N)) :
    IsIntegral (redSub Z) := by
  haveI := irreducibleSpace_redSub hZ
  exact isIntegral_of_irreducibleSpace_of_isReduced (redSub Z)

def ratLift (Z : Closeds N) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN)
    (hs : clpt s ∈ (Z : Set N)) :
    Spec (CommRingCat.of k) ⟶ redSub Z :=
  redLift Z s.1 (by rw [range_coe_eq]; exact Set.singleton_subset_iff.mpr hs)

@[reassoc (attr := simp)]
theorem ratLift_ι (Z : Closeds N) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN)
    (hs : clpt s ∈ (Z : Set N)) : ratLift Z s hs ≫ redι Z = s.1 :=
  redLift_ι _ _ _

theorem ratLift_over (Z : Closeds N) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN)
    (hs : clpt s ∈ (Z : Set N)) : ratLift Z s hs ≫ redι Z ≫ gN = 𝟙 _ := by
  rw [ratLift_ι_assoc, s.2]

end Component

section Mul

variable {k : Type u} [Field k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  (LN : RelativeGroupLaw k gN)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def mulMap (C₁ C₂ : Closeds N) : pullback (redι C₁ ≫ gN) (redι C₂ ≫ gN) ⟶ N :=
  (LN.mul (pullback.fst (redι C₁ ≫ gN) (redι C₂ ≫ gN) ≫ redι C₁ ≫ gN)
    ⟨pullback.fst _ _ ≫ redι C₁, by simp⟩
    ⟨pullback.snd _ _ ≫ redι C₂, by simpa using pullback.condition.symm⟩).1

theorem lift_mulMap (C₁ C₂ : Closeds N) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : T ⟶ redSub C₁) (b : T ⟶ redSub C₂) (ha : a ≫ redι C₁ ≫ gN = t)
    (hb : b ≫ redι C₂ ≫ gN = t) :
    pullback.lift a b (ha.trans hb.symm) ≫ mulMap LN C₁ C₂ =
      (LN.mul t ⟨a ≫ redι C₁, by simpa using ha⟩ ⟨b ≫ redι C₂, by simpa using hb⟩).1 := by
  have hψ : pullback.lift a b (ha.trans hb.symm) ≫
      (pullback.fst (redι C₁ ≫ gN) (redι C₂ ≫ gN) ≫ redι C₁ ≫ gN) = t := by
    rw [pullback.lift_fst_assoc, ha]
  have hnat := LN.mul_natural _ t (pullback.lift a b (ha.trans hb.symm)) hψ
    ⟨pullback.fst _ _ ≫ redι C₁, by simp⟩
    ⟨pullback.snd _ _ ≫ redι C₂, by simpa using pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.fst _ _ ≫ redι C₁, by simp⟩ : SchemeHomOver _ gN) =
      ⟨a ≫ redι C₁, by simpa using ha⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_fst])
  have h2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.snd _ _ ≫ redι C₂, by simpa using pullback.condition.symm⟩ :
        SchemeHomOver _ gN) =
      ⟨b ≫ redι C₂, by simpa using hb⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_snd])
  rw [h1, h2] at hnat
  exact congrArg Subtype.val hnat

theorem one_mem_range_mulMap (C₁ C₂ : Closeds N) (e₁ : clpt (LN.one pt) ∈ (C₁ : Set N))
    (e₂ : clpt (LN.one pt) ∈ (C₂ : Set N)) :
    clpt (LN.one pt) ∈ Set.range (mulMap LN C₁ C₂) := by
  let a : Spec (CommRingCat.of k) ⟶ redSub C₁ := ratLift C₁ (LN.one pt) e₁
  let b : Spec (CommRingCat.of k) ⟶ redSub C₂ := ratLift C₂ (LN.one pt) e₂
  have ha : a ≫ redι C₁ ≫ gN = pt := ratLift_over _ _ _
  have hb : b ≫ redι C₂ ≫ gN = pt := ratLift_over _ _ _
  have hj := lift_mulMap LN C₁ C₂ pt a b ha hb
  have h1 : (⟨a ≫ redι C₁, by simpa using ha⟩ : SchemeHomOver pt gN) = LN.one pt :=
    Subtype.ext (ratLift_ι _ _ _)
  have h2 : (⟨b ≫ redι C₂, by simpa using hb⟩ : SchemeHomOver pt gN) = LN.one pt :=
    Subtype.ext (ratLift_ι _ _ _)
  rw [h1, h2, LN.mul_one] at hj
  exact ⟨pullback.lift a b (ha.trans hb.symm) (IsLocalRing.closedPoint k),
    by rw [← Scheme.Hom.comp_apply, hj]⟩

variable [IsAlgClosed k] [LocallyOfFiniteType gN]

scoped instance isIntegral_pullback_redι (C₁ C₂ : Closeds N) [Fact (IsIrreducible (C₁ : Set N))]
    [Fact (IsIrreducible (C₂ : Set N))] : IsIntegral (pullback (redι C₁ ≫ gN) (redι C₂ ≫ gN)) := by
  haveI : IsIntegral (redSub C₁) := isIntegral_redSub (Fact.out : IsIrreducible (C₁ : Set N))
  haveI : IsIntegral (redSub C₂) := isIntegral_redSub (Fact.out : IsIrreducible (C₂ : Set N))
  haveI : GeometricallyIntegral (redι C₁ ≫ gN) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI : IsLocallyNoetherian (redSub C₂) := LocallyOfFiniteType.isLocallyNoetherian (redι C₂ ≫ gN)
  infer_instance

theorem isIrreducible_range_mulMap (C₁ C₂ : Closeds N) (h₁ : IsIrreducible (C₁ : Set N))
    (h₂ : IsIrreducible (C₂ : Set N)) : IsIrreducible (Set.range (mulMap LN C₁ C₂)) := by
  haveI : Fact (IsIrreducible (C₁ : Set N)) := ⟨h₁⟩
  haveI : Fact (IsIrreducible (C₂ : Set N)) := ⟨h₂⟩
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (mulMap LN C₁ C₂).continuous.continuousOn

end Mul

section IdComp

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def idComp : Closeds G :=
  ⟨irreducibleComponent (clpt (L.one pt)), isClosed_irreducibleComponent⟩

theorem idComp_mem : (idComp L : Set G) ∈ irreducibleComponents G :=
  irreducibleComponent_mem_irreducibleComponents _

theorem one_mem_idComp : clpt (L.one pt) ∈ (idComp L : Set G) :=
  mem_irreducibleComponent

theorem isIrreducible_idComp : IsIrreducible (idComp L : Set G) :=
  isIrreducible_irreducibleComponent

theorem eq_idComp_of_one_mem {Z : Set G} (hZ : Z ∈ irreducibleComponents G)
    (he : clpt (L.one pt) ∈ Z) : Z = idComp L :=
  GoodReductionJacobian.RelativeGroupLaw.eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
    k L (L.one pt) hZ (idComp_mem L) he (one_mem_idComp L)

theorem subset_idComp_of_isIrreducible {W : Set G} (hW : IsIrreducible W)
    (he : clpt (L.one pt) ∈ W) : W ⊆ idComp L := by
  obtain ⟨Z, hZ, hWZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hW
  rw [← eq_idComp_of_one_mem L hZ (hWZ he)]
  exact hWZ

theorem exists_clpt_mem_of_isClosed {Z : Set G} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ s : SchemeHomOver pt f, clpt s ∈ Z := by
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints hne hZ.isLocallyClosed
  refine ⟨(pointEquivClosedPoint f).symm ⟨z, hz⟩, ?_⟩
  have h := congrArg Subtype.val ((pointEquivClosedPoint f).apply_symm_apply ⟨z, hz⟩)
  simp only [pointEquivClosedPoint_apply_coe] at h
  show ((pointEquivClosedPoint f).symm ⟨z, hz⟩).1 (IsLocalRing.closedPoint k) ∈ Z
  rw [h]; exact hzZ

theorem disjoint_idComp_of_ne {Z : Set G} (hZ : Z ∈ irreducibleComponents G) (hne : Z ≠ idComp L) :
    Disjoint Z (idComp L : Set G) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra h
  have hcl : IsClosed (Z ∩ (idComp L : Set G)) :=
    (isClosed_of_mem_irreducibleComponents _ hZ).inter (idComp L).2
  obtain ⟨s, hs⟩ := exists_clpt_mem_of_isClosed (f := f) hcl (Set.nonempty_iff_ne_empty.mpr h)
  exact hne (GoodReductionJacobian.RelativeGroupLaw.eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
    k L s hZ (idComp_mem L) hs.1 hs.2)

variable [QuasiCompact f]

include L in

private theorem _root_.P2mIdentityComponent.finite_irreducibleComponents : (irreducibleComponents G).Finite := by
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsNoetherian G := ⟨⟩
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

p2m_export "P2mIdentityComponent" "finite_irreducibleComponents"

theorem compl_idComp_eq :
    (idComp L : Set G)ᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents G | Z ≠ idComp L}, Z := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
      mem_irreducibleComponent⟩
    intro h
    exact hx (h ▸ mem_irreducibleComponent)
  · rintro ⟨Z, ⟨hZ, hne⟩, hxZ⟩ hx
    exact Set.disjoint_left.mp (disjoint_idComp_of_ne L hZ hne) hxZ hx

theorem isOpen_idComp : IsOpen (idComp L : Set G) := by
  rw [← isClosed_compl_iff, compl_idComp_eq L]
  refine Set.Finite.isClosed_biUnion ((finite_irreducibleComponents L).subset fun Z hZ => hZ.1)
    fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1

theorem isClopen_idComp : IsClopen (idComp L : Set G) := ⟨(idComp L).2, isOpen_idComp L⟩

def U₀ : G.Opens := ⟨idComp L, isOpen_idComp L⟩

abbrev G₀ : Scheme.{u} := (U₀ L : Scheme.{u})

abbrev ι₀ : G₀ L ⟶ G := (U₀ L).ι

abbrev f₀ : G₀ L ⟶ Spec (CommRingCat.of k) := ι₀ L ≫ f

theorem range_ι₀ : Set.range (ι₀ L) = (idComp L : Set G) := (U₀ L).range_ι

theorem ι₀_apply_mem (a : G₀ L) : ι₀ L a ∈ (idComp L : Set G) := by
  rw [← range_ι₀ L]; exact ⟨a, rfl⟩

scoped instance irreducibleSpace_G₀ : IrreducibleSpace (G₀ L) := by
  have h : IsIrreducible (Set.range (ι₀ L)) := by rw [range_ι₀]; exact isIrreducible_idComp L
  have e : Set.range (ι₀ L) ≃ₜ G₀ L := ((ι₀ L).isEmbedding.toHomeomorph).symm
  haveI := Subtype.irreducibleSpace h
  exact e.irreducibleSpace_iff.mp inferInstance

scoped instance isClosedImmersion_ι₀ : IsClosedImmersion (ι₀ L) :=
  .of_isPreimmersion _ (by rw [range_ι₀]; exact (idComp L).2)

theorem range_ι₀_eq_connectedComponent :
    Set.range (ι₀ L) = connectedComponent (clpt (L.one pt)) := by
  rw [range_ι₀]
  refine Set.Subset.antisymm ?_ ?_
  · exact (isIrreducible_idComp L).isConnected.isPreconnected.subset_connectedComponent
      (one_mem_idComp L)
  · exact (isClopen_idComp L).connectedComponent_subset (one_mem_idComp L)

end IdComp

section Law

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def toG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (f₀ L)) :
    SchemeHomOver t f :=
  ⟨x.1 ≫ ι₀ L, by rw [Category.assoc]; exact x.2⟩

@[scoped simp]
theorem toG_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (f₀ L)) :
    (toG L x).1 = x.1 ≫ ι₀ L := rfl

theorem toG_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (toG L (T := T) (t := t)) := by
  intro x y h
  exact Subtype.ext ((cancel_mono (ι₀ L)).mp (congrArg Subtype.val h))

theorem toG_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (f₀ L)) :
    toG L (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (toG L x) :=
  Subtype.ext (Category.assoc _ _ _)

def liftPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (y : SchemeHomOver t f)
    (hy : Set.range y.1 ⊆ (idComp L : Set G)) : SchemeHomOver t (f₀ L) :=
  ⟨IsOpenImmersion.lift (ι₀ L) y.1 (by rw [range_ι₀]; exact hy), by
    rw [IsOpenImmersion.lift_fac_assoc]; exact y.2⟩

@[scoped simp]
theorem toG_liftPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (y : SchemeHomOver t f)
    (hy : Set.range y.1 ⊆ (idComp L : Set G)) : toG L (liftPt L y hy) = y :=
  Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

def M : pullback (f₀ L) (f₀ L) ⟶ G :=
  (L.mul (pullback.fst (f₀ L) (f₀ L) ≫ f₀ L)
    ⟨pullback.fst _ _ ≫ ι₀ L, by simp⟩
    ⟨pullback.snd _ _ ≫ ι₀ L, by simpa using pullback.condition.symm⟩).1

theorem lift_M {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a b : T ⟶ G₀ L) (ha : a ≫ f₀ L = t) (hb : b ≫ f₀ L = t) :
    pullback.lift a b (ha.trans hb.symm) ≫ M L =
      (L.mul t ⟨a ≫ ι₀ L, by simpa using ha⟩ ⟨b ≫ ι₀ L, by simpa using hb⟩).1 := by
  have hψ : pullback.lift a b (ha.trans hb.symm) ≫ (pullback.fst (f₀ L) (f₀ L) ≫ f₀ L) = t := by
    rw [pullback.lift_fst_assoc, ha]
  have hnat := L.mul_natural _ t (pullback.lift a b (ha.trans hb.symm)) hψ
    ⟨pullback.fst _ _ ≫ ι₀ L, by simp⟩
    ⟨pullback.snd _ _ ≫ ι₀ L, by simpa using pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.fst _ _ ≫ ι₀ L, by simp⟩ : SchemeHomOver _ f) =
      ⟨a ≫ ι₀ L, by simpa using ha⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_fst])
  have h2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.snd _ _ ≫ ι₀ L, by simpa using pullback.condition.symm⟩ : SchemeHomOver _ f) =
      ⟨b ≫ ι₀ L, by simpa using hb⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_snd])
  rw [h1, h2] at hnat
  exact congrArg Subtype.val hnat

abbrev A : Scheme.{u} := redSub (idComp L)

abbrev ιA : A L ⟶ G := redι (idComp L)

def j : A L ⟶ G₀ L :=
  IsOpenImmersion.lift (ι₀ L) (ιA L) (by rw [range_ι₀, range_redι])

@[reassoc (attr := simp)]
theorem j_ι₀ : j L ≫ ι₀ L = ιA L := IsOpenImmersion.lift_fac _ _ _

theorem range_j : Set.range (j L) = Set.univ := by
  refine Set.eq_univ_of_forall fun u => ?_
  have hu : ι₀ L u ∈ Set.range (ιA L) := by rw [range_redι]; exact ι₀_apply_mem L u
  obtain ⟨a, ha⟩ := hu
  refine ⟨a, (ι₀ L).isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, j_ι₀, ha]

def φ : pullback (ιA L ≫ f) (ιA L ≫ f) ⟶ pullback (f₀ L) (f₀ L) :=
  pullback.map _ _ _ _ (j L) (j L) (𝟙 _) (by simp) (by simp)

theorem range_φ : Set.range (φ L) = Set.univ := by
  rw [φ, Scheme.Pullback.range_map, range_j]
  simp

theorem φ_M : φ L ≫ M L = mulMap L (idComp L) (idComp L) := by
  have hφ : φ L = pullback.lift (pullback.fst _ _ ≫ j L) (pullback.snd _ _ ≫ j L)
      (by simp only [Category.assoc, j_ι₀_assoc]; exact pullback.condition) := by
    apply pullback.hom_ext <;> simp [φ]
  have ha : (pullback.fst (ιA L ≫ f) (ιA L ≫ f) ≫ j L) ≫ f₀ L =
      pullback.fst (ιA L ≫ f) (ιA L ≫ f) ≫ ιA L ≫ f := by
    rw [Category.assoc, ← Category.assoc (j L), j_ι₀]
  have hb : (pullback.snd (ιA L ≫ f) (ιA L ≫ f) ≫ j L) ≫ f₀ L =
      pullback.fst (ιA L ≫ f) (ιA L ≫ f) ≫ ιA L ≫ f := by
    rw [Category.assoc, ← Category.assoc (j L), j_ι₀]; exact pullback.condition.symm
  rw [hφ, lift_M L _ _ _ ha hb]
  show _ = (L.mul _ _ _).1
  congr 2
  · apply Subtype.ext
    show (pullback.fst (ιA L ≫ f) (ιA L ≫ f) ≫ j L) ≫ ι₀ L = pullback.fst _ _ ≫ redι (idComp L)
    rw [Category.assoc, j_ι₀]
  · apply Subtype.ext
    show (pullback.snd (ιA L ≫ f) (ιA L ≫ f) ≫ j L) ≫ ι₀ L = pullback.snd _ _ ≫ redι (idComp L)
    rw [Category.assoc, j_ι₀]

theorem range_M_subset : Set.range (M L) ⊆ (idComp L : Set G) := by
  have h1 : Set.range (M L) = Set.range (φ L ≫ M L) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_φ, Set.image_univ]
  rw [h1, φ_M]
  exact subset_idComp_of_isIrreducible L
    (isIrreducible_range_mulMap L _ _ (isIrreducible_idComp L) (isIrreducible_idComp L))
    (one_mem_range_mulMap L _ _ (one_mem_idComp L) (one_mem_idComp L))

theorem range_mul_toG_subset {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (f₀ L)) :
    Set.range (L.mul t (toG L x) (toG L y)).1 ⊆ (idComp L : Set G) := by
  have h : (L.mul t (toG L x) (toG L y)).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ M L := by
    rw [lift_M L t x.1 y.1 x.2 y.2]; rfl
  rw [h, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans (range_M_subset L)

theorem range_one_subset {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    Set.range (L.one t).1 ⊆ (idComp L : Set G) := by
  rw [← const_one L t, const_coe, Scheme.Hom.comp_base, TopCat.coe_comp]
  refine (Set.range_comp_subset_range _ _).trans ?_
  rw [range_coe_eq]
  exact Set.singleton_subset_iff.mpr (one_mem_idComp L)

theorem range_ι₀_invN_subset : Set.range (ι₀ L ≫ invN L) ⊆ (idComp L : Set G) := by
  let h : G ≃ₜ G := (invN L).homeomorph
  have h1 : h '' (idComp L : Set G) ∈ irreducibleComponents G :=
    image_mem_irreducibleComponents h (idComp_mem L)
  have h2 : clpt (L.one pt) ∈ h '' (idComp L : Set G) := by
    refine ⟨clpt (L.one pt), one_mem_idComp L, ?_⟩
    letI := L.pointGroup pt
    show invN L (clpt (L.one pt)) = _
    rw [invN_clpt, show L.inv pt (L.one pt) = L.one pt from inv_one]
  have h3 := eq_idComp_of_one_mem L h1 h2
  rintro _ ⟨a, rfl⟩
  rw [← h3]
  exact ⟨ι₀ L a, ι₀_apply_mem L a, rfl⟩

theorem range_inv_toG_subset {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t (f₀ L)) :
    Set.range (L.inv t (toG L x)).1 ⊆ (idComp L : Set G) := by
  rw [← comp_invN L (toG L x), toG_coe, Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans (range_ι₀_invN_subset L)

def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (f₀ L)) :
    SchemeHomOver t (f₀ L) :=
  liftPt L (L.mul t (toG L x) (toG L y)) (range_mul_toG_subset L t x y)

theorem toG_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (f₀ L)) :
    toG L (mulPt L t x y) = L.mul t (toG L x) (toG L y) :=
  toG_liftPt _ _ _

def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (f₀ L) :=
  liftPt L (L.one t) (range_one_subset L t)

theorem toG_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toG L (onePt L t) = L.one t :=
  toG_liftPt _ _ _

def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (f₀ L)) :
    SchemeHomOver t (f₀ L) :=
  liftPt L (L.inv t (toG L x)) (range_inv_toG_subset L t x)

theorem toG_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t (f₀ L)) : toG L (invPt L t x) = L.inv t (toG L x) :=
  toG_liftPt _ _ _

def law₀ : RelativeGroupLaw k (f₀ L) where
  mul t x y := mulPt L t x y
  one t := onePt L t
  inv t x := invPt L t x
  mul_assoc t x y z := by
    apply toG_injective L
    simp only [toG_mulPt]
    exact L.mul_assoc t _ _ _
  one_mul t x := by
    apply toG_injective L
    simp only [toG_mulPt, toG_onePt]
    exact L.one_mul t _
  mul_one t x := by
    apply toG_injective L
    simp only [toG_mulPt, toG_onePt]
    exact L.mul_one t _
  inv_mul_cancel t x := by
    apply toG_injective L
    simp only [toG_mulPt, toG_invPt, toG_onePt]
    exact L.inv_mul_cancel t _
  mul_natural t t' ψ hψ x y := by
    apply toG_injective L
    rw [toG_transition]
    simp only [toG_mulPt]
    rw [L.mul_natural t t' ψ hψ, toG_transition, toG_transition]

theorem toG_law₀_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (f₀ L)) :
    toG L ((law₀ L).mul t x y) = L.mul t (toG L x) (toG L y) :=
  toG_mulPt L t x y

theorem hom_ι₀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (f₀ L)) :
    NeronModelInfra.schemeHomOverComp ((law₀ L).mul t x y) (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f))
        (NeronModelInfra.schemeHomOverComp y (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f)) :=
  toG_law₀_mul L t x y

theorem isCommutative_law₀ (hc : L.IsCommutative) : (law₀ L).IsCommutative := by
  intro T t x y
  apply toG_injective L
  rw [toG_law₀_mul, toG_law₀_mul]
  exact hc t _ _

end Law

section FiniteIndex

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

theorem clpt_mul_inv_mem_idComp (x s : SchemeHomOver pt f) {Z : Set G}
    (hZ : Z ∈ irreducibleComponents G) (hx : clpt x ∈ Z) (hs : clpt s ∈ Z) :
    clpt (L.mul pt (L.inv pt s) x) ∈ (idComp L : Set G) := by
  letI := L.pointGroup pt
  let h : G ≃ₜ G := (transl L (L.inv pt s)).homeomorph
  have h1 : h '' Z ∈ irreducibleComponents G := image_mem_irreducibleComponents h hZ
  have h2 : clpt (L.one pt) ∈ h '' Z := by
    refine ⟨clpt s, hs, ?_⟩
    show transl L (L.inv pt s) (clpt s) = _
    rw [transl_clpt, show L.mul pt (L.inv pt s) s = L.one pt from inv_mul_cancel s]
  have h3 : h '' Z = idComp L := eq_idComp_of_one_mem L h1 h2
  have h4 : clpt (L.mul pt (L.inv pt s) x) = h (clpt x) := by
    show _ = transl L (L.inv pt s) (clpt x)
    rw [transl_clpt]
  rw [h4, ← h3]
  exact ⟨clpt x, hx, rfl⟩

theorem exists_finite_cosets :
    ∃ S : Set (SchemeHomOver pt f), S.Finite ∧
      ∀ x : SchemeHomOver pt f, ∃ s ∈ S, ∃ a : SchemeHomOver pt (f₀ L),
        x = L.mul pt s (NeronModelInfra.schemeHomOverComp a (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f)) := by
  classical
  letI := L.pointGroup pt
  haveI : Finite (irreducibleComponents G) := (finite_irreducibleComponents L).to_subtype

  choose rep hrep using fun Z : irreducibleComponents G =>
    exists_clpt_mem_of_isClosed (f := f) (isClosed_of_mem_irreducibleComponents _ Z.2) Z.2.1.nonempty
  refine ⟨Set.range rep, Set.finite_range rep, fun x => ?_⟩
  let Z : irreducibleComponents G :=
    ⟨irreducibleComponent (clpt x), irreducibleComponent_mem_irreducibleComponents _⟩
  let s := rep Z
  have hy : clpt (L.mul pt (L.inv pt s) x) ∈ (idComp L : Set G) :=
    clpt_mul_inv_mem_idComp L x s Z.2 mem_irreducibleComponent (hrep Z)
  let a : SchemeHomOver pt (f₀ L) :=
    liftPt L (L.mul pt (L.inv pt s) x) (by
      rw [range_coe_eq]; exact Set.singleton_subset_iff.mpr hy)
  refine ⟨s, ⟨Z, rfl⟩, a, ?_⟩
  have ha : NeronModelInfra.schemeHomOverComp a (⟨ι₀ L, rfl⟩ : SchemeHomOver (f₀ L) f) =
      L.mul pt (L.inv pt s) x :=
    toG_liftPt L _ _
  rw [ha]
  show x = s * (s⁻¹ * x)
  rw [mul_inv_cancel_left]

end FiniteIndex

end P2mIdentityComponent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex.P2mIdentityComponent"

open P2mIdentityComponent in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) (L₀ : RelativeGroupLaw k (i ≫ f)),
      IsOpenImmersion i ∧ IsClosedImmersion i ∧ IrreducibleSpace G₀ ∧
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      (L.IsCommutative → L₀.IsCommutative) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f),
            x = L.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by
  obtain ⟨S, hS, hcos⟩ := exists_finite_cosets L
  exact ⟨G₀ L, ι₀ L, law₀ L, inferInstance, inferInstance, inferInstance,
    range_ι₀_eq_connectedComponent L, fun t x y => hom_ι₀ L t x y, isCommutative_law₀ L,
    S, hS, hcos⟩

end
end S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex (solution)
