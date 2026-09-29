-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/63c04c0f-fc2d-5d41-9ff3-f762f96811c5

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace

noncomputable section

universe u

namespace P2mReducedIdentityComponent

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

theorem const_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s : SchemeHomOver pt gN) :
    const t (LN.inv pt s) = LN.inv t (const t s) :=
  inv_natural LN pt t t (Category.comp_id t) s

def transl (s : SchemeHomOver pt gN) : N ⟶ N :=
  (LN.mul gN (const gN s) RelativeGroupLaw.idPoint).1

theorem transl_over (s : SchemeHomOver pt gN) : transl LN s ≫ gN = gN :=
  (LN.mul gN (const gN s) RelativeGroupLaw.idPoint).2

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

theorem transl_point {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t gN)
    (s : SchemeHomOver pt gN) :
    (⟨x.1 ≫ transl LN s, by rw [Category.assoc, transl_over, x.2]⟩ : SchemeHomOver t gN) =
      LN.mul t (const t s) x :=
  Subtype.ext (comp_transl LN x s)

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

theorem transl_clpt_one (s : SchemeHomOver pt gN) :
    transl LN s (clpt (LN.one pt)) = clpt s := by
  rw [transl_clpt, LN.mul_one]

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
  refine ⟨h.symm w, h3 ⟨w, hw, rfl⟩, h.apply_symm_apply w⟩

theorem eq_of_mem_irreducibleComponents_of_subset {Z W : Set α} (hZ : Z ∈ irreducibleComponents α)
    (hW : IsIrreducible W) (hZW : Z ⊆ W) : W = Z :=
  Set.Subset.antisymm (hZ.2 hW hZW) hZW

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

theorem redι_apply_mem (Z : Closeds N) (a : redSub Z) : redι Z a ∈ (Z : Set N) := by
  rw [← range_redι Z]
  exact ⟨a, rfl⟩

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

end Component

section Identity

variable {k : Type u} [Field k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  (LN : RelativeGroupLaw k gN)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def ratLift (Z : Closeds N) (s : SchemeHomOver pt gN) (hs : clpt s ∈ (Z : Set N)) :
    Spec (CommRingCat.of k) ⟶ redSub Z :=
  redLift Z s.1 (by
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [this]; exact hs)

@[reassoc (attr := simp)]
theorem ratLift_ι (Z : Closeds N) (s : SchemeHomOver pt gN) (hs : clpt s ∈ (Z : Set N)) :
    ratLift Z s hs ≫ redι Z = s.1 :=
  redLift_ι _ _ _

theorem ratLift_over (Z : Closeds N) (s : SchemeHomOver pt gN) (hs : clpt s ∈ (Z : Set N)) :
    ratLift Z s hs ≫ redι Z ≫ gN = 𝟙 _ := by
  rw [ratLift_ι_assoc, s.2]

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

theorem subset_range_mulMap_left (C₁ C₂ : Closeds N) (e₂ : clpt (LN.one pt) ∈ (C₂ : Set N)) :
    (C₁ : Set N) ⊆ Set.range (mulMap LN C₁ C₂) := by
  let e₂' : Spec (CommRingCat.of k) ⟶ redSub C₂ := ratLift C₂ (LN.one pt) e₂
  have hb : ((redι C₁ ≫ gN) ≫ e₂') ≫ redι C₂ ≫ gN = redι C₁ ≫ gN := by
    simp only [Category.assoc, e₂']
    rw [ratLift_over, Category.comp_id]
  have hj := lift_mulMap LN C₁ C₂ (redι C₁ ≫ gN) (𝟙 _) ((redι C₁ ≫ gN) ≫ e₂')
    (Category.id_comp _) hb
  have hone : (⟨((redι C₁ ≫ gN) ≫ e₂') ≫ redι C₂, by simpa using hb⟩ :
      SchemeHomOver (redι C₁ ≫ gN) gN) = LN.one (redι C₁ ≫ gN) := by
    apply Subtype.ext
    rw [← const_one LN, const_coe]
    simp [e₂']
  rw [hone, LN.mul_one] at hj
  have hj' : pullback.lift (𝟙 _) ((redι C₁ ≫ gN) ≫ e₂') ((Category.id_comp _).trans hb.symm) ≫
      mulMap LN C₁ C₂ = redι C₁ := hj.trans (Category.id_comp _)
  intro z hz
  have hz' : z ∈ Set.range (redι C₁) := by rw [range_redι]; exact hz
  obtain ⟨a, rfl⟩ := hz'
  exact ⟨pullback.lift (𝟙 _) ((redι C₁ ≫ gN) ≫ e₂') ((Category.id_comp _).trans hb.symm) a,
    by rw [← Scheme.Hom.comp_apply, hj']⟩

theorem subset_range_mulMap_right (C₁ C₂ : Closeds N) (e₁ : clpt (LN.one pt) ∈ (C₁ : Set N)) :
    (C₂ : Set N) ⊆ Set.range (mulMap LN C₁ C₂) := by
  let e₁' : Spec (CommRingCat.of k) ⟶ redSub C₁ := ratLift C₁ (LN.one pt) e₁
  have ha : ((redι C₂ ≫ gN) ≫ e₁') ≫ redι C₁ ≫ gN = redι C₂ ≫ gN := by
    simp only [Category.assoc, e₁']
    rw [ratLift_over, Category.comp_id]
  have hj := lift_mulMap LN C₁ C₂ (redι C₂ ≫ gN) ((redι C₂ ≫ gN) ≫ e₁') (𝟙 _)
    ha (Category.id_comp _)
  have hone : (⟨((redι C₂ ≫ gN) ≫ e₁') ≫ redι C₁, by simpa using ha⟩ :
      SchemeHomOver (redι C₂ ≫ gN) gN) = LN.one (redι C₂ ≫ gN) := by
    apply Subtype.ext
    rw [← const_one LN, const_coe]
    simp [e₁']
  rw [hone, LN.one_mul] at hj
  have hj' : pullback.lift ((redι C₂ ≫ gN) ≫ e₁') (𝟙 _) (ha.trans (Category.id_comp _).symm) ≫
      mulMap LN C₁ C₂ = redι C₂ := hj.trans (Category.id_comp _)
  intro z hz
  have hz' : z ∈ Set.range (redι C₂) := by rw [range_redι]; exact hz
  obtain ⟨b, rfl⟩ := hz'
  exact ⟨pullback.lift ((redι C₂ ≫ gN) ≫ e₁') (𝟙 _) (ha.trans (Category.id_comp _).symm) b,
    by rw [← Scheme.Hom.comp_apply, hj']⟩

variable [IsAlgClosed k] [LocallyOfFiniteType gN]

theorem isIrreducible_range_mulMap (C₁ C₂ : Closeds N) (h₁ : IsIrreducible (C₁ : Set N))
    (h₂ : IsIrreducible (C₂ : Set N)) : IsIrreducible (Set.range (mulMap LN C₁ C₂)) := by
  haveI : IsIntegral (redSub C₁) := isIntegral_redSub h₁
  haveI : IsIntegral (redSub C₂) := isIntegral_redSub h₂
  haveI : GeometricallyIntegral (redι C₁ ≫ gN) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI : IsLocallyNoetherian (redSub C₂) := LocallyOfFiniteType.isLocallyNoetherian (redι C₂ ≫ gN)
  haveI : IsIntegral (pullback (redι C₁ ≫ gN) (redι C₂ ≫ gN)) := inferInstance
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (mulMap LN C₁ C₂).continuous.continuousOn

end Identity

section IdComp

variable {k : Type u} [Field k] [IsAlgClosed k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType gN] (LN : RelativeGroupLaw k gN)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def idComp : Closeds N :=
  ⟨irreducibleComponent (clpt (LN.one pt)), isClosed_irreducibleComponent⟩

theorem idComp_mem : (idComp LN : Set N) ∈ irreducibleComponents N :=
  irreducibleComponent_mem_irreducibleComponents _

theorem one_mem_idComp : clpt (LN.one pt) ∈ (idComp LN : Set N) :=
  mem_irreducibleComponent

theorem isIrreducible_idComp : IsIrreducible (idComp LN : Set N) :=
  isIrreducible_irreducibleComponent

theorem eq_idComp_of_one_mem {Z : Set N} (hZ : Z ∈ irreducibleComponents N)
    (he : clpt (LN.one pt) ∈ Z) : Z = idComp LN :=
  GoodReductionJacobian.RelativeGroupLaw.eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
    k LN (LN.one pt) hZ (idComp_mem LN) he (one_mem_idComp LN)

abbrev A : Scheme.{u} := redSub (idComp LN)

abbrev ιA : A LN ⟶ N := redι (idComp LN)

abbrev fA : A LN ⟶ Spec (CommRingCat.of k) := ιA LN ≫ gN

scoped instance isIntegral_A : IsIntegral (A LN) := isIntegral_redSub (isIrreducible_idComp LN)

scoped instance geometricallyIntegral_fA : GeometricallyIntegral (fA LN) :=
  AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _

scoped instance isLocallyNoetherian_A : IsLocallyNoetherian (A LN) :=
  LocallyOfFiniteType.isLocallyNoetherian (fA LN)

theorem subset_idComp_of_isIrreducible {W : Set N} (hW : IsIrreducible W)
    (h : (idComp LN : Set N) ⊆ W) : W ⊆ idComp LN := by
  obtain ⟨W', hW', hWW'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hW
  have : W' = idComp LN :=
    eq_of_mem_irreducibleComponents_of_subset (idComp_mem LN) hW'.1 (h.trans hWW')
  rw [← this]; exact hWW'

theorem range_mulMap_subset :
    Set.range (mulMap LN (idComp LN) (idComp LN)) ⊆ (idComp LN : Set N) :=
  subset_idComp_of_isIrreducible LN
    (isIrreducible_range_mulMap LN _ _ (isIrreducible_idComp LN) (isIrreducible_idComp LN))
    (subset_range_mulMap_left LN _ _ (one_mem_idComp LN))

def mulA : pullback (fA LN) (fA LN) ⟶ A LN :=
  redLift (idComp LN) (mulMap LN (idComp LN) (idComp LN)) (range_mulMap_subset LN)

@[reassoc (attr := simp)]
theorem mulA_ι : mulA LN ≫ ιA LN = mulMap LN (idComp LN) (idComp LN) := redLift_ι _ _ _

def oneA : Spec (CommRingCat.of k) ⟶ A LN := ratLift (idComp LN) (LN.one pt) (one_mem_idComp LN)

@[reassoc (attr := simp)]
theorem oneA_ι : oneA LN ≫ ιA LN = (LN.one pt).1 := ratLift_ι _ _ _

def invN : N ⟶ N := (LN.inv gN RelativeGroupLaw.idPoint).1

theorem invN_over : invN LN ≫ gN = gN := (LN.inv gN RelativeGroupLaw.idPoint).2

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

theorem range_ι_invN_subset : Set.range (ιA LN ≫ invN LN) ⊆ (idComp LN : Set N) := by
  let h : N ≃ₜ N := (invN LN).homeomorph
  have h1 : h '' (idComp LN : Set N) ∈ irreducibleComponents N :=
    image_mem_irreducibleComponents h (idComp_mem LN)
  have h2 : clpt (LN.one pt) ∈ h '' (idComp LN : Set N) := by
    refine ⟨clpt (LN.one pt), one_mem_idComp LN, ?_⟩
    letI := LN.pointGroup pt
    show invN LN (clpt (LN.one pt)) = _
    rw [invN_clpt, show LN.inv pt (LN.one pt) = LN.one pt from inv_one]
  have h3 := eq_idComp_of_one_mem LN h1 h2
  rintro _ ⟨a, rfl⟩
  rw [← h3]
  exact ⟨ιA LN a, redι_apply_mem _ a, rfl⟩

def invA : A LN ⟶ A LN := redLift (idComp LN) (ιA LN ≫ invN LN) (range_ι_invN_subset LN)

@[reassoc (attr := simp)]
theorem invA_ι : invA LN ≫ ιA LN = ιA LN ≫ invN LN := redLift_ι _ _ _

def toN {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (fA LN)) :
    SchemeHomOver t gN :=
  ⟨x.1 ≫ ιA LN, by rw [Category.assoc]; exact x.2⟩

@[scoped simp]
theorem toN_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (fA LN)) :
    (toN LN x).1 = x.1 ≫ ιA LN := rfl

theorem toN_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (toN LN (T := T) (t := t)) := by
  intro x y h
  exact Subtype.ext ((cancel_mono (ιA LN)).mp (congrArg Subtype.val h))

theorem toN_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (fA LN)) :
    toN LN (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (toN LN x) :=
  Subtype.ext (Category.assoc _ _ _)

def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (fA LN)) :
    SchemeHomOver t (fA LN) :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ mulA LN, by
    show pullback.lift x.1 y.1 _ ≫ mulA LN ≫ ιA LN ≫ gN = t
    rw [mulA_ι_assoc, ← Category.assoc, lift_mulMap LN _ _ t x.1 y.1 x.2 y.2]
    exact (LN.mul t _ _).2⟩

theorem toN_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (fA LN)) :
    toN LN (mulPt LN t x y) = LN.mul t (toN LN x) (toN LN y) := by
  apply Subtype.ext
  rw [toN_coe]
  show (pullback.lift x.1 y.1 _ ≫ mulA LN) ≫ ιA LN = _
  rw [Category.assoc, mulA_ι, lift_mulMap LN _ _ t x.1 y.1 x.2 y.2]
  rfl

def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (fA LN) :=
  ⟨t ≫ oneA LN, by
    show t ≫ oneA LN ≫ ιA LN ≫ gN = t
    rw [oneA_ι_assoc, (LN.one pt).2, Category.comp_id]⟩

theorem toN_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toN LN (onePt LN t) = LN.one t := by
  apply Subtype.ext
  rw [toN_coe, ← const_one LN t, const_coe]
  show (t ≫ oneA LN) ≫ ιA LN = _
  rw [Category.assoc, oneA_ι]

def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (fA LN)) :
    SchemeHomOver t (fA LN) :=
  ⟨x.1 ≫ invA LN, by
    show x.1 ≫ invA LN ≫ ιA LN ≫ gN = t
    rw [invA_ι_assoc, invN_over]
    exact x.2⟩

theorem toN_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t (fA LN)) : toN LN (invPt LN t x) = LN.inv t (toN LN x) := by
  apply Subtype.ext
  rw [toN_coe]
  show (x.1 ≫ invA LN) ≫ ιA LN = _
  rw [Category.assoc, invA_ι, ← Category.assoc]
  exact comp_invN LN (toN LN x)

def lawA : RelativeGroupLaw k (fA LN) where
  mul t x y := mulPt LN t x y
  one t := onePt LN t
  inv t x := invPt LN t x
  mul_assoc t x y z := by
    apply toN_injective LN
    simp only [toN_mulPt]
    exact LN.mul_assoc t _ _ _
  one_mul t x := by
    apply toN_injective LN
    simp only [toN_mulPt, toN_onePt]
    exact LN.one_mul t _
  mul_one t x := by
    apply toN_injective LN
    simp only [toN_mulPt, toN_onePt]
    exact LN.mul_one t _
  inv_mul_cancel t x := by
    apply toN_injective LN
    simp only [toN_mulPt, toN_invPt, toN_onePt]
    exact LN.inv_mul_cancel t _
  mul_natural t t' ψ hψ x y := by
    apply toN_injective LN
    rw [toN_transition]
    simp only [toN_mulPt]
    rw [LN.mul_natural t t' ψ hψ, toN_transition, toN_transition]

theorem toN_lawA_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (fA LN)) :
    toN LN ((lawA LN).mul t x y) = LN.mul t (toN LN x) (toN LN y) :=
  toN_mulPt LN t x y

def ιA' : SchemeHomOver (fA LN) gN := ⟨ιA LN, rfl⟩

theorem hom_ιA' {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (fA LN)) :
    NeronModelInfra.schemeHomOverComp ((lawA LN).mul t x y) (ιA' LN) =
      LN.mul t (NeronModelInfra.schemeHomOverComp x (ιA' LN))
        (NeronModelInfra.schemeHomOverComp y (ιA' LN)) :=
  toN_lawA_mul LN t x y

end IdComp

section Structure

variable {k : Type u} [Field k] [IsAlgClosed k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType gN] (LN : RelativeGroupLaw k gN)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

scoped instance smooth_fA : Smooth (fA LN) := by
  obtain ⟨g, -⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_eq (lawA LN)
  letI : GrpObj (Over.mk (fA LN)) := g
  exact smooth_of_grpObj (fA LN)

theorem exists_isStandardSmoothOfRelativeDimension {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsStandardSmooth) :
    ∃ d : ℕ, f.IsStandardSmoothOfRelativeDimension d := by
  algebraize [f]
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hf.out
  exact ⟨P.dimension, ι, σ, hσ, hι, P, rfl⟩

theorem exists_smoothOfRelativeDimension : ∃ d : ℕ, SmoothOfRelativeDimension d (fA LN) := by
  obtain ⟨a₀⟩ : Nonempty (A LN) := inferInstance
  obtain ⟨U, hU, V, hV, ha, e, hstd⟩ := Smooth.exists_isStandardSmooth (fA LN) a₀
  obtain ⟨d, hd⟩ := exists_isStandardSmoothOfRelativeDimension _ hstd
  refine ⟨d, ?_⟩

  have key : SmoothOfRelativeDimension d ((fA LN).resLE U V e) := by
    haveI : IsAffine U := hU
    haveI : IsAffine V := hV
    have hf : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)
        ((fA LN).appLE U V e).hom :=
      RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hd
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
    haveI : (RingHom.toMorphismProperty
        (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d))).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp <|
        (HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension d)).respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff
      (RingHom.toMorphismProperty (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)))
      (arrowResLEAppIso (fA LN) U V e)).mpr hf

  have hcomp : SmoothOfRelativeDimension (d + 0) ((fA LN).resLE U V e ≫ U.ι) := inferInstance
  rw [Scheme.Hom.resLE_comp_ι, Nat.add_zero] at hcomp
  exact AlgebraicGeometry.smoothOfRelativeDimension_of_irreducibleSpace d (fA LN) V ⟨a₀, ha⟩

variable [IsProper gN]

scoped instance isProper_fA : IsProper (fA LN) := inferInstance

theorem abelianSchemePropertyBundle_A : AbelianSchemePropertyBundle k (fA LN) where
  smooth := inferInstance
  proper := inferInstance
  connectedFibres s := by
    have : (fA LN).base ⁻¹' {s} = Set.univ := by
      ext a; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [this]
    exact IrreducibleSpace.isIrreducible_univ (A LN) |>.isConnected
  hasGroupLaw := ⟨lawA LN⟩

theorem isCommutative_lawA : (lawA LN).IsCommutative :=
  GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral (lawA LN)

end Structure

section FiniteIndex

variable {k : Type u} [Field k] [IsAlgClosed k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  [IsProper gN] (LN : RelativeGroupLaw k gN)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

theorem exists_clpt_mem {Z : Set N} (hZ : Z ∈ irreducibleComponents N) :
    ∃ s : SchemeHomOver pt gN, clpt s ∈ Z := by
  haveI : JacobsonSpace N := LocallyOfFiniteType.jacobsonSpace gN
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints hZ.1.nonempty
    (isClosed_of_mem_irreducibleComponents _ hZ).isLocallyClosed
  refine ⟨(pointEquivClosedPoint gN).symm ⟨z, hz⟩, ?_⟩
  have h := congrArg Subtype.val ((pointEquivClosedPoint gN).apply_symm_apply ⟨z, hz⟩)
  simp only [pointEquivClosedPoint_apply_coe] at h
  show ((pointEquivClosedPoint gN).symm ⟨z, hz⟩).1 (IsLocalRing.closedPoint k) ∈ Z
  rw [h]; exact hzZ

include LN in

private theorem _root_.P2mReducedIdentityComponent.finite_irreducibleComponents : (irreducibleComponents N).Finite := by
  haveI : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace gN
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian gN
  haveI : IsNoetherian N := ⟨⟩
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

p2m_export "P2mReducedIdentityComponent" "finite_irreducibleComponents"

theorem clpt_mul_inv_mem_idComp (x s : SchemeHomOver pt gN) {Z : Set N}
    (hZ : Z ∈ irreducibleComponents N) (hx : clpt x ∈ Z) (hs : clpt s ∈ Z) :
    clpt (LN.mul pt (LN.inv pt s) x) ∈ (idComp LN : Set N) := by
  letI := LN.pointGroup pt
  let h : N ≃ₜ N := (transl LN (LN.inv pt s)).homeomorph
  have h1 : h '' Z ∈ irreducibleComponents N := image_mem_irreducibleComponents h hZ
  have h2 : clpt (LN.one pt) ∈ h '' Z := by
    refine ⟨clpt s, hs, ?_⟩
    show transl LN (LN.inv pt s) (clpt s) = _
    rw [transl_clpt, show LN.mul pt (LN.inv pt s) s = LN.one pt from inv_mul_cancel s]
  have h3 : h '' Z = idComp LN := eq_idComp_of_one_mem LN h1 h2
  have h4 : clpt (LN.mul pt (LN.inv pt s) x) = h (clpt x) := by
    show _ = transl LN (LN.inv pt s) (clpt x)
    rw [transl_clpt]
  rw [h4, ← h3]
  exact ⟨clpt x, hx, rfl⟩

theorem exists_finite_cosets :
    ∃ S : Set (SchemeHomOver pt gN), S.Finite ∧
      ∀ x : SchemeHomOver pt gN, ∃ s ∈ S, ∃ a : SchemeHomOver pt (fA LN),
        x = LN.mul pt s (NeronModelInfra.schemeHomOverComp a (ιA' LN)) := by
  classical
  letI := LN.pointGroup pt
  haveI : Finite (irreducibleComponents N) := (finite_irreducibleComponents LN).to_subtype

  choose rep hrep using fun Z : irreducibleComponents N => exists_clpt_mem (gN := gN) Z.2
  refine ⟨Set.range rep, Set.finite_range rep, fun x => ?_⟩
  let Z : irreducibleComponents N :=
    ⟨irreducibleComponent (clpt x), irreducibleComponent_mem_irreducibleComponents _⟩
  let s := rep Z
  have hy : clpt (LN.mul pt (LN.inv pt s) x) ∈ (idComp LN : Set N) :=
    clpt_mul_inv_mem_idComp LN x s Z.2 mem_irreducibleComponent (hrep Z)
  let a : SchemeHomOver pt (fA LN) :=
    ⟨ratLift (idComp LN) _ hy, ratLift_over _ _ _⟩
  refine ⟨s, ⟨Z, rfl⟩, a, ?_⟩
  have ha : NeronModelInfra.schemeHomOverComp a (ιA' LN) = LN.mul pt (LN.inv pt s) x :=
    Subtype.ext (ratLift_ι _ _ hy)
  rw [ha]
  show x = s * (s⁻¹ * x)
  rw [mul_inv_cancel_left]

end FiniteIndex

end P2mReducedIdentityComponent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper.P2mReducedIdentityComponent"

open P2mReducedIdentityComponent in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {N : Scheme.{u}}
    {gN : N ⟶ Spec (CommRingCat.of k)} [IsProper gN] (LN : RelativeGroupLaw k gN) :
    ∃ (A : Scheme.{u}) (fA : A ⟶ Spec (CommRingCat.of k)) (LA : RelativeGroupLaw k fA) (d : ℕ)
      (ι : SchemeHomOver fA gN),
      LA.IsCommutative ∧ AbelianSchemePropertyBundle k fA ∧ SmoothOfRelativeDimension d fA ∧
      IsClosedImmersion ι.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t fA),
        NeronModelInfra.schemeHomOverComp (LA.mul t x y) ι =
          LN.mul t (NeronModelInfra.schemeHomOverComp x ι)
            (NeronModelInfra.schemeHomOverComp y ι)) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA,
            x = LN.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a ι) := by
  obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension LN
  obtain ⟨S, hS, hcos⟩ := exists_finite_cosets LN
  exact ⟨A LN, fA LN, lawA LN, d, ιA' LN, isCommutative_lawA LN, abelianSchemePropertyBundle_A LN,
    hd, inferInstanceAs (IsClosedImmersion (ιA LN)), fun t x y => hom_ιA' LN t x y, S, hS, hcos⟩

end
end S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper (solution)
