-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_fppf_quotient_of_sliceQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8b2475bb-9abd-52e4-85ff-0d666c3ef968

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact
import Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace G2eAsm

section Points

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

abbrev amap : pullback (i ≫ f) (j ≫ f) ⟶ G :=
  pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i

theorem mul_coe_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (h : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst h
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

def ipt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f)) : SchemeHomOver t f :=
  ⟨n.1 ≫ i, by rw [Category.assoc]; exact n.2⟩

@[scoped simp] theorem ipt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f)) :
    (ipt i n).1 = n.1 ≫ i := rfl

theorem ipt_eq_comp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f)) :
    ipt i n = NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) := rfl

def pairNS {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f)) (s : T ⟶ S)
    (hs : s ≫ j ≫ f = t) : T ⟶ pullback (i ≫ f) (j ≫ f) :=
  pullback.lift n.1 s (by rw [n.2, hs])

@[scoped simp] theorem pairNS_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) : pairNS i j n s hs ≫ pullback.fst _ _ = n.1 := pullback.lift_fst _ _ _

@[scoped simp] theorem pairNS_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) : pairNS i j n s hs ≫ pullback.snd _ _ = s := pullback.lift_snd _ _ _

theorem comp_amap {T : Scheme.{u}} (z : T ⟶ pullback (i ≫ f) (j ≫ f)) (t : T ⟶ Spec (CommRingCat.of k))
    (ht : z ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    z ≫ amap L i j =
      (L.mul t (ipt i ⟨z ≫ pullback.fst _ _, ht⟩)
        ⟨z ≫ pullback.snd _ _ ≫ j, by
          rw [Category.assoc, Category.assoc, ← pullback.condition]; exact ht⟩).1 := by

  set m := pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) with hm
  have hm_snd : m ≫ pullback.snd (i ≫ f) f = pullback.snd _ _ ≫ j := by
    rw [hm]; exact pullback.lift_snd _ _ _
  have hm_fst : m ≫ pullback.fst (i ≫ f) f = pullback.fst _ _ ≫ 𝟙 N := by
    rw [hm]; exact pullback.lift_fst _ _ _
  have hz : (z ≫ m) ≫ RelativeGroupLaw.actionSource f i = t := by
    show (z ≫ m) ≫ pullback.snd (i ≫ f) f ≫ f = t
    rw [Category.assoc, ← Category.assoc m, hm_snd]
    simp only [Category.assoc]
    rw [← pullback.condition]
    exact ht
  show z ≫ m ≫ L.action i = _
  rw [RelativeGroupLaw.action_def, ← Category.assoc]
  have h1 := congrArg Subtype.val
    (L.mul_natural (RelativeGroupLaw.actionSource f i) t (z ≫ m) hz (L.actionFstPoint i) (L.actionSndPoint i))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  rw [h1]
  apply mul_coe_congr L rfl
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionFstPoint_coe, ipt_coe,
      Category.assoc]
    rw [← Category.assoc m, hm_fst, Category.comp_id]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionSndPoint_coe, Category.assoc]
    rw [hm_snd]

theorem pairNS_amap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) :
    pairNS i j n s hs ≫ amap L i j = (L.mul t (ipt i n) ⟨s ≫ j, hs⟩).1 := by
  rw [comp_amap L i j (pairNS i j n s hs) t (by rw [← Category.assoc, pairNS_fst, n.2])]
  apply mul_coe_congr L rfl
  · simp only [ipt_coe]; rw [pairNS_fst]
  · show (pairNS i j n s hs ≫ pullback.snd _ _) ≫ j = s ≫ j
    rw [pairNS_snd]

theorem ipt_mul
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)) :
    ipt i (LN.mul t x y) = L.mul t (ipt i x) (ipt i y) := by
  simp only [ipt_eq_comp]; exact hi t x y

theorem ipt_injective [IsClosedImmersion i] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (x y : SchemeHomOver t (i ≫ f)) (h : ipt i x = ipt i y) : x = y := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [ipt_coe] at this
  exact (cancel_mono i).1 this

end Points

section Action

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

theorem comp_action {T : Scheme.{u}} (α : T ⟶ pullback (i ≫ f) f) (t : T ⟶ Spec (CommRingCat.of k))
    (ht : α ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    α ≫ L.action i =
      (L.mul t (ipt i ⟨α ≫ pullback.fst _ _, ht⟩)
        ⟨α ≫ pullback.snd _ _, by rw [Category.assoc, ← pullback.condition]; exact ht⟩).1 := by
  have hz : α ≫ RelativeGroupLaw.actionSource f i = t := by
    show α ≫ pullback.snd (i ≫ f) f ≫ f = t
    rw [← pullback.condition]; exact ht
  rw [RelativeGroupLaw.action_def]
  have h1 := congrArg Subtype.val
    (L.mul_natural (RelativeGroupLaw.actionSource f i) t α hz (L.actionFstPoint i) (L.actionSndPoint i))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  rw [h1]
  apply mul_coe_congr L rfl
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionFstPoint_coe, ipt_coe,
      Category.assoc]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionSndPoint_coe]

variable (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))

include hi in
theorem ipt_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : ipt i (LN.one t) = L.one t := by
  letI := L.pointGroup t
  have h := ipt_mul L i LN hi t (LN.one t) (LN.one t)
  rw [LN.one_mul] at h

  have h' : ipt i (LN.one t) * ipt i (LN.one t) = ipt i (LN.one t) * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h'

include hi in
theorem ipt_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (m : SchemeHomOver t (i ≫ f)) :
    ipt i (LN.inv t m) = L.inv t (ipt i m) := by
  letI := L.pointGroup t
  have h := ipt_mul L i LN hi t (LN.inv t m) m
  rw [LN.inv_mul_cancel, ipt_one L i LN hi] at h

  exact eq_inv_of_mul_eq_one_left h.symm

include hi in

theorem pairNS_mul_amap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (m n : SchemeHomOver t (i ≫ f))
    (s : T ⟶ S) (hs : s ≫ j ≫ f = t) :
    pairNS i j (LN.mul t m n) s hs ≫ amap L i j =
      (L.mul t (ipt i m) ⟨pairNS i j n s hs ≫ amap L i j, by
        rw [pairNS_amap]; exact (L.mul t _ _).2⟩).1 := by
  rw [pairNS_amap, ipt_mul L i LN hi, L.mul_assoc]
  apply mul_coe_congr L rfl _ _ _ _ rfl
  exact (pairNS_amap L i j n s hs).symm

omit hi in
theorem amap_over : amap L i j ≫ f = pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f := by
  show (pullback.map _ _ _ _ _ _ _ _ _ ≫ L.action i) ≫ f = _
  rw [Category.assoc, RelativeGroupLaw.action_over, RelativeGroupLaw.actionSource, ← Category.assoc,
    pullback.lift_snd, Category.assoc]

omit hi in

theorem eq_pairNS {T : Scheme.{u}} (z : T ⟶ pullback (i ≫ f) (j ≫ f)) (t : T ⟶ Spec (CommRingCat.of k))
    (ht : z ≫ pullback.fst _ _ ≫ i ≫ f = t) :
    z = pairNS i j ⟨z ≫ pullback.fst _ _, ht⟩ (z ≫ pullback.snd _ _)
      (by rw [Category.assoc, ← pullback.condition]; exact ht) := by
  apply pullback.hom_ext
  · rw [pairNS_fst]
  · rw [pairNS_snd]

include LN hi in

theorem action_mem_image_of_snd_mem_image (V : Set ↥S) (x : ↥(pullback (i ≫ f) f))
    (hx : (pullback.snd (i ≫ f) f).base x ∈
      (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' V)) :
    (L.action i).base x ∈ (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' V) := by
  obtain ⟨y, hyV, hxy⟩ := hx
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd (i ≫ f) f)
    (g := amap L i j) x y hxy.symm

  let Q := pullback (pullback.snd (i ≫ f) f) (amap L i j)
  let t : Q ⟶ Spec (CommRingCat.of k) := pullback.snd _ _ ≫ pullback.fst _ _ ≫ i ≫ f
  have hm : (pullback.fst _ _ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = t := by
    show (pullback.fst _ _ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f =
      pullback.snd (pullback.snd (i ≫ f) f) (amap L i j) ≫ pullback.fst _ _ ≫ i ≫ f
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, amap_over,
      ← pullback.condition]
  let m : SchemeHomOver t (i ≫ f) := ⟨pullback.fst _ _ ≫ pullback.fst (i ≫ f) f, hm⟩
  let n : SchemeHomOver t (i ≫ f) := ⟨pullback.snd _ _ ≫ pullback.fst (i ≫ f) (j ≫ f), Category.assoc _ _ _⟩
  have hs : (pullback.snd (pullback.snd (i ≫ f) f) (amap L i j) ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = t := by
    show _ = pullback.snd (pullback.snd (i ≫ f) f) (amap L i j) ≫ pullback.fst _ _ ≫ i ≫ f
    rw [Category.assoc, ← pullback.condition]
  let μ : Q ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j (LN.mul t m n) _ hs
  have hμ : μ ≫ amap L i j = pullback.fst _ _ ≫ L.action i := by
    rw [pairNS_mul_amap L i LN j hi,
      comp_action L i (pullback.fst (pullback.snd (i ≫ f) f) (amap L i j)) t (by rw [Category.assoc] at hm; exact hm)]
    apply mul_coe_congr L rfl _ _ _ _ rfl
    show pairNS i j n _ hs ≫ amap L i j = pullback.fst _ _ ≫ pullback.snd (i ≫ f) f
    rw [← eq_pairNS i j (pullback.snd _ _) t rfl, pullback.condition]
  refine ⟨μ.base z, ?_, ?_⟩
  · show (μ ≫ pullback.snd (i ≫ f) (j ≫ f)).base z ∈ V
    rw [pairNS_snd]
    show (pullback.snd (i ≫ f) (j ≫ f)).base ((pullback.snd (pullback.snd (i ≫ f) f) (amap L i j)).base z) ∈ V
    rw [hz2]; exact hyV
  · show (μ ≫ amap L i j).base z = _
    rw [hμ, ← hz1]; rfl

include LN hi in

theorem snd_mem_image_of_action_mem_image (V : Set ↥S) (x : ↥(pullback (i ≫ f) f))
    (hx : (L.action i).base x ∈ (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' V)) :
    (pullback.snd (i ≫ f) f).base x ∈ (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' V) := by
  obtain ⟨y, hyV, hxy⟩ := hx
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := L.action i)
    (g := amap L i j) x y hxy.symm
  let Q := pullback (L.action i) (amap L i j)
  let t : Q ⟶ Spec (CommRingCat.of k) := pullback.snd _ _ ≫ pullback.fst _ _ ≫ i ≫ f
  have hm : (pullback.fst _ _ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = t := by
    show (pullback.fst _ _ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f =
      pullback.snd (L.action i) (amap L i j) ≫ pullback.fst _ _ ≫ i ≫ f
    rw [Category.assoc, pullback.condition,
      show pullback.snd (i ≫ f) f ≫ f = L.action i ≫ f from (RelativeGroupLaw.action_over L i).symm,
      ← Category.assoc, pullback.condition, Category.assoc, amap_over, ← pullback.condition]
  let m : SchemeHomOver t (i ≫ f) := ⟨pullback.fst _ _ ≫ pullback.fst (i ≫ f) f, hm⟩
  let n : SchemeHomOver t (i ≫ f) := ⟨pullback.snd _ _ ≫ pullback.fst (i ≫ f) (j ≫ f), Category.assoc _ _ _⟩
  have hs : (pullback.snd (L.action i) (amap L i j) ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = t := by
    show _ = pullback.snd (L.action i) (amap L i j) ≫ pullback.fst _ _ ≫ i ≫ f
    rw [Category.assoc, ← pullback.condition]
  let μ : Q ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j (LN.mul t (LN.inv t m) n) _ hs
  have hμ : μ ≫ amap L i j = pullback.fst _ _ ≫ pullback.snd (i ≫ f) f := by
    rw [pairNS_mul_amap L i LN j hi, ipt_inv L i LN hi]
    have hn : pairNS i j n _ hs ≫ amap L i j = pullback.fst _ _ ≫ L.action i := by
      rw [← eq_pairNS i j (pullback.snd _ _) t rfl, pullback.condition]
    have hact := comp_action L i (pullback.fst (L.action i) (amap L i j)) t (by rw [Category.assoc] at hm; exact hm)
    letI := L.pointGroup t

    have key : L.mul t (L.inv t (ipt i m)) ⟨pairNS i j n _ hs ≫ amap L i j, by
        rw [pairNS_amap]; exact (L.mul t _ _).2⟩ =
        ⟨pullback.fst _ _ ≫ pullback.snd (i ≫ f) f, by
          rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact hm⟩ := by
      have e1 : (⟨pairNS i j n _ hs ≫ amap L i j, by rw [pairNS_amap]; exact (L.mul t _ _).2⟩ : SchemeHomOver t f) =
          L.mul t (ipt i m) ⟨pullback.fst _ _ ≫ pullback.snd (i ≫ f) f, by
            rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact hm⟩ := by
        apply Subtype.ext; exact hn.trans hact
      rw [e1]
      show (ipt i m)⁻¹ * (ipt i m * _) = _
      rw [inv_mul_cancel_left]
    exact congrArg Subtype.val key
  refine ⟨μ.base z, ?_, ?_⟩
  · show (μ ≫ pullback.snd (i ≫ f) (j ≫ f)).base z ∈ V
    rw [pairNS_snd]
    show (pullback.snd (i ≫ f) (j ≫ f)).base ((pullback.snd (L.action i) (amap L i j)).base z) ∈ V
    rw [hz2]; exact hyV
  · show (μ ≫ amap L i j).base z = _
    rw [hμ, ← hz1]; rfl

end Action

section Descent

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)

abbrev NV : (pullback (i ≫ f) (j ≫ f)).Opens := pullback.snd (i ≫ f) (j ≫ f) ⁻¹ᵁ V

def Uimg [UniversallyOpen (amap L i j)] : G.Opens :=
  (amap L i j).isOpenMap.functor.obj (NV (f := f) i j V)

theorem coe_Uimg [UniversallyOpen (amap L i j)] :
    (Uimg L i j V : Set ↥G) = (amap L i j).base '' ((pullback.snd (i ≫ f) (j ≫ f)).base ⁻¹' (V : Set ↥S)) := rfl

theorem le_preimage_Uimg [UniversallyOpen (amap L i j)] : NV (f := f) i j V ≤ amap L i j ⁻¹ᵁ Uimg L i j V :=
  fun x hx => Set.mem_image_of_mem _ hx

def cover [UniversallyOpen (amap L i j)] : (NV (f := f) i j V).toScheme ⟶ (Uimg L i j V).toScheme :=
  (amap L i j).resLE (Uimg L i j V) (NV (f := f) i j V) (le_preimage_Uimg L i j V)

theorem cover_ι [UniversallyOpen (amap L i j)] :
    cover L i j V ≫ (Uimg L i j V).ι = (NV (f := f) i j V).ι ≫ amap L i j := Scheme.Hom.resLE_comp_ι _ _

scoped instance cover_surjective [UniversallyOpen (amap L i j)] : Surjective (cover L i j V) := by
  refine ⟨fun u => ?_⟩
  obtain ⟨y0, hy0, hu⟩ := u.2
  have : y0 ∈ Set.range (NV (f := f) i j V).ι.base := by rw [Scheme.Opens.range_ι]; exact hy0
  obtain ⟨y, rfl⟩ := this
  refine ⟨y, ?_⟩
  apply (Uimg L i j V).ι.isOpenEmbedding.injective
  show ((cover L i j V) ≫ (Uimg L i j V).ι).base y = _
  rw [cover_ι]
  exact hu

scoped instance cover_flat [UniversallyOpen (amap L i j)] [Flat (amap L i j)] : Flat (cover L i j V) := by
  unfold cover; infer_instance

scoped instance cover_lfp [UniversallyOpen (amap L i j)] [LocallyOfFinitePresentation (amap L i j)] :
    LocallyOfFinitePresentation (cover L i j V) := by
  unfold cover; infer_instance

include LN hi in

theorem Uimg_saturated [IsClosedImmersion i] [UniversallyOpen (amap L i j)] :
    pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V := by
  apply le_antisymm
  · intro x hx
    exact action_mem_image_of_snd_mem_image L i LN j hi (V : Set ↥S) x hx
  · intro x hx
    exact snd_mem_image_of_action_mem_image L i LN j hi (V : Set ↥S) x hx

include LN in
theorem surjective_if : Surjective (i ≫ f) := by
  refine ⟨fun s => ⟨(LN.one (𝟙 _)).1.base s, ?_⟩⟩
  show ((LN.one (𝟙 _)).1 ≫ i ≫ f).base s = s
  rw [(LN.one (𝟙 _)).2]; rfl

include LN in
theorem nonempty_Uimg [UniversallyOpen (amap L i j)] [Nonempty V.toScheme] : Nonempty (Uimg L i j V).toScheme := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V.toScheme)
  haveI := surjective_if i LN
  obtain ⟨y, hy⟩ := (pullback.snd (i ≫ f) (j ≫ f)).surjective (V.ι.base v)
  have hyV : y ∈ NV (f := f) i j V := by
    show (pullback.snd (i ≫ f) (j ≫ f)).base y ∈ (V : Set ↥S)
    rw [hy, ← Scheme.Opens.range_ι V]; exact ⟨v, rfl⟩
  exact ⟨⟨(amap L i j).base y, Set.mem_image_of_mem _ hyV⟩⟩

end Descent

section KernelPair

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)

abbrev q₁ : pullback (amap L i j) j ⟶ S := pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)
abbrev q₂ : pullback (amap L i j) j ⟶ S := pullback.snd (amap L i j) j

omit hi in
theorem amap_over' : amap L i j ≫ f = pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f := by
  rw [amap_over, pullback.condition]

include LN hi in

theorem kernel_pair [IsClosedImmersion i] [UniversallyOpen (amap L i j)]
    (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
    (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)
    {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (NV (f := f) i j V).toScheme)
    (h : g₁ ≫ cover L i j V = g₂ ≫ cover L i j V) :
    g₁ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π = g₂ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π := by

  have hz : (g₁ ≫ (NV (f := f) i j V).ι) ≫ amap L i j = (g₂ ≫ (NV (f := f) i j V).ι) ≫ amap L i j := by
    rw [Category.assoc, Category.assoc, ← cover_ι, ← Category.assoc, h, Category.assoc]

  have ht₁ : (g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f =
      (g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f := by
    rw [← amap_over', ← Category.assoc, hz, Category.assoc]
  obtain ⟨t, hzt₂⟩ : ∃ t : Z ⟶ Spec (CommRingCat.of k),
      (g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := ⟨_, rfl⟩
  have hzt₁ : (g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := ht₁.trans hzt₂

  let n₁ : SchemeHomOver t (i ≫ f) := ⟨(g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by rw [Category.assoc]; exact hzt₁⟩
  let n₂ : SchemeHomOver t (i ≫ f) := ⟨(g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by rw [Category.assoc]; exact hzt₂⟩
  have hs₁ : ((g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j ≫ f = t := by
    rw [Category.assoc, ← pullback.condition]; exact hzt₁
  have hs₂ : ((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j ≫ f = t := by
    rw [Category.assoc, ← pullback.condition]; exact hzt₂

  have key : L.mul t (ipt i n₁) ⟨((g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j, by rw [Category.assoc]; exact hs₁⟩ =
      L.mul t (ipt i n₂) ⟨((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j, by rw [Category.assoc]; exact hs₂⟩ := by
    apply Subtype.ext
    have e₁ := comp_amap L i j (g₁ ≫ (NV (f := f) i j V).ι) t hzt₁
    have e₂ := comp_amap L i j (g₂ ≫ (NV (f := f) i j V).ι) t hzt₂
    rw [hz] at e₁
    rw [e₁] at e₂

    refine (mul_coe_congr L rfl _ _ _ _ ?_ ?_).trans (e₂.trans (mul_coe_congr L rfl _ _ _ _ ?_ ?_))
    · show ((g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _) ≫ i = _
      simp only [ipt_coe, Category.assoc]
    · show (((g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j) = _
      simp only [Category.assoc]
    · show _ = ((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _) ≫ i
      simp only [ipt_coe, Category.assoc]
    · show _ = (((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j)
      simp only [Category.assoc]

  let r : Z ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j (LN.mul t (LN.inv t n₂) n₁) _ hs₁
  have hr : r ≫ amap L i j = ((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j := by
    show pairNS i j (LN.mul t (LN.inv t n₂) n₁) _ hs₁ ≫ amap L i j = _
    rw [pairNS_mul_amap L i LN j hi, ipt_inv L i LN hi]
    letI := L.pointGroup t
    have e1 : (⟨pairNS i j n₁ _ hs₁ ≫ amap L i j, by rw [pairNS_amap]; exact (L.mul t _ _).2⟩ : SchemeHomOver t f) =
        L.mul t (ipt i n₂) ⟨((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j, by rw [Category.assoc]; exact hs₂⟩ := by
      rw [← key]; apply Subtype.ext; exact pairNS_amap L i j n₁ _ hs₁
    have e2 : L.mul t (L.inv t (ipt i n₂)) ⟨pairNS i j n₁ _ hs₁ ≫ amap L i j, by rw [pairNS_amap]; exact (L.mul t _ _).2⟩ =
        ⟨((g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _) ≫ j, by rw [Category.assoc]; exact hs₂⟩ := by
      rw [e1]
      show (ipt i n₂)⁻¹ * (ipt i n₂ * _) = _
      rw [inv_mul_cancel_left]
    exact congrArg Subtype.val e2
  let ρ : Z ⟶ pullback (amap L i j) j := pullback.lift r _ hr
  have hρ₁ : ρ ≫ q₁ L i j = (g₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _ := by
    show ρ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [← Category.assoc, pullback.lift_fst]
    exact pairNS_snd i j _ _ hs₁
  have hρ₂ : ρ ≫ q₂ L i j = (g₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _ := pullback.lift_snd _ _ _

  have hρV : Set.range ρ.base ⊆ Set.range (q₁ L i j ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    show (ρ ≫ q₁ L i j).base z ∈ (V : Set ↥S)
    rw [hρ₁]
    show (pullback.snd (i ≫ f) (j ≫ f)).base ((NV (f := f) i j V).ι.base (g₁.base z)) ∈ (V : Set ↥S)
    have : (NV (f := f) i j V).ι.base (g₁.base z) ∈ NV (f := f) i j V := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    exact this
  let ρ' : Z ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift (q₁ L i j ⁻¹ᵁ V).ι ρ hρV
  have hρ' : ρ' ≫ (q₁ L i j ⁻¹ᵁ V).ι = ρ := IsOpenImmersion.lift_fac _ _ _

  have A : ρ' ≫ (q₁ L i j ∣_ V) = g₁ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hρ', hρ₁, Category.assoc,
      Category.assoc, morphismRestrict_ι]
  have B : ρ' ≫ ((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V) =
      g₂ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc (Iso.hom _),
      Scheme.isoOfEq_hom_ι, ← Category.assoc, hρ', hρ₂, Category.assoc, Category.assoc, morphismRestrict_ι]
  calc g₁ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π = ρ' ≫ (q₁ L i j ∣_ V) ≫ π := by
        rw [← Category.assoc, ← A, Category.assoc]
    _ = ρ' ≫ (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π := by rw [w]
    _ = g₂ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π := by
        rw [← Category.assoc, B, Category.assoc]

end KernelPair

section Generic

theorem quasiCompact_of_comp_surjective {X U Y : Scheme.{u}} (c : X ⟶ U) [Surjective c] (p : U ⟶ Y)
    [QuasiCompact (c ≫ p)] : QuasiCompact p := by
  refine ⟨fun W hW hWc => ?_⟩
  have h := QuasiCompact.isCompact_preimage (f := c ≫ p) W hW hWc
  have : p.base ⁻¹' W = c.base '' ((c ≫ p).base ⁻¹' W) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_of_subset]
    rw [Set.range_eq_univ.mpr c.surjective]; exact Set.subset_univ _
  rw [this]
  exact h.image c.continuous

theorem surjective_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] (U : Y.Opens) :
    Surjective (f ∣_ U) := by
  refine ⟨fun u => ?_⟩
  obtain ⟨x, hx⟩ := f.surjective (U.ι.base u)
  have hxU : x ∈ f ⁻¹ᵁ U := by
    show f.base x ∈ (U : Set ↥Y); rw [hx, ← Scheme.Opens.range_ι U]; exact ⟨u, rfl⟩
  have : x ∈ Set.range (f ⁻¹ᵁ U).ι.base := by rw [Scheme.Opens.range_ι]; exact hxU
  obtain ⟨x', rfl⟩ := this
  refine ⟨x', U.ι.isOpenEmbedding.injective ?_⟩
  show ((f ∣_ U) ≫ U.ι).base x' = _
  rw [morphismRestrict_ι]; exact hx

end Generic

section Quotient

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)
  [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]
  (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
  (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)

def pdesc : (Uimg L i j V).toScheme ⟶ Y :=
  EffectiveEpi.desc (cover L i j V) ((pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π)
    (fun g₁ g₂ h => kernel_pair L i LN hi j V hV π w g₁ g₂ h)

theorem cover_pdesc : cover L i j V ≫ pdesc L i LN hi j V hV π w = (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π :=
  EffectiveEpi.fac (cover L i j V) _ (fun g₁ g₂ h => kernel_pair L i LN hi j V hV π w g₁ g₂ h)

include LN in
theorem surjective_pdesc [Surjective π] : Surjective (pdesc L i LN hi j V hV π w) := by
  haveI := surjective_if i LN
  haveI := surjective_morphismRestrict (pullback.snd (i ≫ f) (j ≫ f)) V
  haveI : Surjective (cover L i j V ≫ pdesc L i LN hi j V hV π w) := by rw [cover_pdesc]; infer_instance
  exact Surjective.of_comp (cover L i j V) _

theorem flat_pdesc [Flat (i ≫ f)] [Flat π] : Flat (pdesc L i LN hi j V hV π w) := by
  haveI : Flat (cover L i j V ≫ pdesc L i LN hi j V hV π w) := by rw [cover_pdesc]; infer_instance
  exact AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective (cover L i j V) _

theorem quasiCompact_pdesc [QuasiCompact (i ≫ f)] [QuasiCompact π] : QuasiCompact (pdesc L i LN hi j V hV π w) := by
  haveI : QuasiCompact (cover L i j V ≫ pdesc L i LN hi j V hV π w) := by rw [cover_pdesc]; infer_instance
  exact quasiCompact_of_comp_surjective (cover L i j V) _

def yK (hcoeq : IsColimit (Cofork.ofπ π w)) : Y ⟶ Spec (CommRingCat.of k) :=
  (Cofork.IsColimit.desc' hcoeq (V.ι ≫ j ≫ f) (by
    have e : pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f = pullback.snd (amap L i j) j ≫ j ≫ f := by
      rw [← amap_over, ← Category.assoc, pullback.condition, Category.assoc]
    have h1 : (q₁ L i j ∣_ V) ≫ V.ι ≫ j ≫ f = (q₁ L i j ⁻¹ᵁ V).ι ≫ pullback.snd (amap L i j) j ≫ j ≫ f := by
      rw [← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc]
      rw [e]
    have h2 : (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f =
        (q₁ L i j ⁻¹ᵁ V).ι ≫ pullback.snd (amap L i j) j ≫ j ≫ f := by
      have h3 : ((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V) ≫ V.ι = (q₁ L i j ⁻¹ᵁ V).ι ≫ q₂ L i j := by
        rw [morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
      rw [Category.assoc, ← Category.assoc (q₂ L i j ∣_ V), ← Category.assoc ((pullback (amap L i j) j).isoOfEq hV).hom, h3,
        Category.assoc]
    rw [h1, h2])).1

theorem π_yK (hcoeq : IsColimit (Cofork.ofπ π w)) : π ≫ yK L i j V hV π w hcoeq = V.ι ≫ j ≫ f :=
  (Cofork.IsColimit.desc' hcoeq (V.ι ≫ j ≫ f) _).2

theorem pdesc_yK (hcoeq : IsColimit (Cofork.ofπ π w)) :
    pdesc L i LN hi j V hV π w ≫ yK L i j V hV π w hcoeq = (Uimg L i j V).ι ≫ f := by
  rw [← cancel_epi (cover L i j V), ← Category.assoc, cover_pdesc, Category.assoc, π_yK, ← Category.assoc,
    morphismRestrict_ι, Category.assoc, ← amap_over, ← Category.assoc, ← cover_ι L i j V, Category.assoc]

omit [IsClosedImmersion i] in
theorem isLocallyNoetherian_Y [IsAffine S] [LocallyOfFiniteType (j ≫ f)] [Flat π] [Surjective π] [QuasiCompact π] :
    IsLocallyNoetherian Y := by
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (j ≫ f)
  exact AlgebraicGeometry.isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact π

theorem locallyOfFinitePresentation_pdesc (hcoeq : IsColimit (Cofork.ofπ π w)) [LocallyOfFiniteType f]
    [IsAffine S] [LocallyOfFiniteType (j ≫ f)] [Flat π] [Surjective π] [QuasiCompact π] :
    LocallyOfFinitePresentation (pdesc L i LN hi j V hV π w) := by
  haveI : LocallyOfFiniteType (pdesc L i LN hi j V hV π w ≫ yK L i j V hV π w hcoeq) := by
    rw [pdesc_yK]; infer_instance
  haveI : LocallyOfFiniteType (pdesc L i LN hi j V hV π w) := locallyOfFiniteType_of_comp _ (yK L i j V hV π w hcoeq)
  haveI := isLocallyNoetherian_Y (f := f) j V π
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
    (pdesc L i LN hi j V hV π w) (𝟙 Y) (pdesc L i LN hi j V hV π w) (Category.comp_id _)

end Quotient

section Square

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)

include hi in

theorem exists_translate {Q : Scheme.{u}} (α : Q ⟶ pullback (i ≫ f) f)
    (β : Q ⟶ (NV (f := f) i j V).toScheme)
    (hαβ : α ≫ pullback.snd (i ≫ f) f = β ≫ (NV (f := f) i j V).ι ≫ amap L i j) :
    ∃ μ : Q ⟶ (NV (f := f) i j V).toScheme,
      μ ≫ (NV (f := f) i j V).ι ≫ amap L i j = α ≫ L.action i ∧
      μ ≫ (NV (f := f) i j V).ι ≫ pullback.snd (i ≫ f) (j ≫ f) =
        β ≫ (NV (f := f) i j V).ι ≫ pullback.snd (i ≫ f) (j ≫ f) := by
  obtain ⟨t, ht⟩ : ∃ t : Q ⟶ Spec (CommRingCat.of k),
      (β ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := ⟨_, rfl⟩
  have hm : (α ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hαβ, Category.assoc, Category.assoc, amap_over',
      ← Category.assoc]
    exact ht
  let m : SchemeHomOver t (i ≫ f) := ⟨α ≫ pullback.fst (i ≫ f) f, hm⟩
  let n : SchemeHomOver t (i ≫ f) := ⟨(β ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by rw [Category.assoc]; exact ht⟩
  have hs : ((β ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = t := by
    rw [Category.assoc, ← pullback.condition]; exact ht
  let μ₀ : Q ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j (LN.mul t m n) _ hs
  have hμ₀ : μ₀ ≫ amap L i j = α ≫ L.action i := by
    show pairNS i j (LN.mul t m n) _ hs ≫ amap L i j = _
    rw [pairNS_mul_amap L i LN j hi, comp_action L i α t (by rw [Category.assoc] at hm; exact hm)]
    apply mul_coe_congr L rfl _ _ _ _ rfl
    show pairNS i j n _ hs ≫ amap L i j = α ≫ pullback.snd (i ≫ f) f
    rw [← eq_pairNS i j (β ≫ (NV (f := f) i j V).ι) t ht, Category.assoc, hαβ]
  have hμ₀snd : μ₀ ≫ pullback.snd (i ≫ f) (j ≫ f) = (β ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _ :=
    pairNS_snd i j _ _ hs
  have hrange : Set.range μ₀.base ⊆ Set.range (NV (f := f) i j V).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    show (μ₀ ≫ pullback.snd (i ≫ f) (j ≫ f)).base q ∈ (V : Set ↥S)
    rw [hμ₀snd]
    show (pullback.snd (i ≫ f) (j ≫ f)).base ((NV (f := f) i j V).ι.base (β.base q)) ∈ (V : Set ↥S)
    have : (NV (f := f) i j V).ι.base (β.base q) ∈ NV (f := f) i j V := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    exact this
  refine ⟨IsOpenImmersion.lift (NV (f := f) i j V).ι μ₀ hrange, ?_, ?_⟩
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, hμ₀]
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, hμ₀snd, Category.assoc]

variable [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]
  (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
  (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)

include LN hi in

theorem square (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V) :
    (pullback.snd (i ≫ f) f ∣_ Uimg L i j V) ≫ pdesc L i LN hi j V hV π w =
      (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V)) ≫ pdesc L i LN hi j V hV π w := by
  let P₁ := pullback.snd (i ≫ f) f ∣_ Uimg L i j V
  let ν := pullback.fst P₁ (cover L i j V)
  haveI : Epi ν := by
    haveI : EffectiveEpi ν := inferInstance
    infer_instance
  rw [← cancel_epi ν]

  have hαβ : (ν ≫ (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι) ≫ pullback.snd (i ≫ f) f =
      pullback.snd P₁ (cover L i j V) ≫ (NV (f := f) i j V).ι ≫ amap L i j := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, pullback.condition, Category.assoc, cover_ι]
  obtain ⟨μ, hμa, hμb⟩ := exists_translate L i LN hi j V (ν ≫ (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι)
    (pullback.snd P₁ (cover L i j V)) hαβ
  have hμcover : μ ≫ cover L i j V = ν ≫ ((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V) := by
    rw [← cancel_mono (Uimg L i j V).ι, Category.assoc, cover_ι, hμa]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, ← Category.assoc (Iso.hom _), Scheme.isoOfEq_hom_ι]
  have hμsnd : μ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) = pullback.snd P₁ (cover L i j V) ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Category.assoc, morphismRestrict_ι]
    exact hμb
  calc ν ≫ P₁ ≫ pdesc L i LN hi j V hV π w
      = (pullback.snd P₁ (cover L i j V) ≫ cover L i j V) ≫ pdesc L i LN hi j V hV π w := by
        rw [← Category.assoc, pullback.condition]
    _ = pullback.snd P₁ (cover L i j V) ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π := by
        rw [Category.assoc, cover_pdesc]
    _ = μ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V) ≫ π := by rw [← Category.assoc, ← hμsnd, Category.assoc]
    _ = μ ≫ cover L i j V ≫ pdesc L i LN hi j V hV π w := by rw [cover_pdesc]
    _ = ν ≫ (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V)) ≫ pdesc L i LN hi j V hV π w := by
        rw [← Category.assoc, hμcover]; simp only [Category.assoc]

end Square

section Effective

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)
  [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]

abbrev P₁ : (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).toScheme ⟶ (Uimg L i j V).toScheme :=
  pullback.snd (i ≫ f) f ∣_ Uimg L i j V

abbrev P₂ (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V) :
    (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).toScheme ⟶ (Uimg L i j V).toScheme :=
  ((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V)

omit [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)] in
theorem P₁_ι : P₁ L i j V ≫ (Uimg L i j V).ι = (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι ≫ pullback.snd (i ≫ f) f :=
  morphismRestrict_ι _ _

omit [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)] in
theorem P₂_ι (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V) :
    P₂ L i j V hU ≫ (Uimg L i j V).ι = (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι ≫ L.action i := by
  show (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ Uimg L i j V)) ≫ (Uimg L i j V).ι = _
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]

include hi in
omit [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)] in

theorem eq_of_snd_eq_of_action_eq {T : Scheme.{u}} (a b : T ⟶ pullback (i ≫ f) f)
    (h₁ : a ≫ pullback.snd (i ≫ f) f = b ≫ pullback.snd (i ≫ f) f) (h₂ : a ≫ L.action i = b ≫ L.action i) :
    a = b := by
  obtain ⟨t, hta⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k), a ≫ pullback.fst (i ≫ f) f ≫ i ≫ f = t := ⟨_, rfl⟩
  have htb : b ≫ pullback.fst (i ≫ f) f ≫ i ≫ f = t := by
    rw [pullback.condition, ← Category.assoc, ← h₁, Category.assoc, ← pullback.condition]; exact hta
  have ea := comp_action L i a t hta
  have eb := comp_action L i b t htb
  rw [h₂, eb] at ea

  letI := L.pointGroup t
  have hg : (⟨b ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc, ← pullback.condition]; exact htb⟩ : SchemeHomOver t f) =
      ⟨a ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc, ← pullback.condition]; exact hta⟩ := Subtype.ext h₁.symm
  have key : ipt i ⟨b ≫ pullback.fst (i ≫ f) f, htb⟩ = ipt i ⟨a ≫ pullback.fst (i ≫ f) f, hta⟩ := by
    have := Subtype.ext ea
    rw [hg] at this
    exact mul_right_cancel this
  have hm := congrArg Subtype.val (ipt_injective i _ _ key)
  apply pullback.hom_ext
  · exact hm.symm
  · exact h₁

include LN hi in

theorem exists_section (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
    (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)
    (hRπ : IsPullback (q₁ L i j ∣_ V) (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) π π)
    (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V)
    {C : Scheme.{u}} (c₁ c₂ : C ⟶ (NV (f := f) i j V).toScheme)
    (hc : c₁ ≫ cover L i j V ≫ pdesc L i LN hi j V hV π w = c₂ ≫ cover L i j V ≫ pdesc L i LN hi j V hV π w) :
    ∃ s : C ⟶ (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).toScheme,
      s ≫ P₁ L i j V = c₁ ≫ cover L i j V ∧ s ≫ P₂ L i j V hU = c₂ ≫ cover L i j V := by

  have h12 : (c₁ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V)) ≫ π = (c₂ ≫ (pullback.snd (i ≫ f) (j ≫ f) ∣_ V)) ≫ π := by
    rw [Category.assoc, Category.assoc, ← cover_pdesc L i LN hi j V hV π w]; exact hc
  let ρ : C ⟶ pullback (amap L i j) j := hRπ.lift _ _ h12 ≫ (q₁ L i j ⁻¹ᵁ V).ι
  have hρ₁ : ρ ≫ q₁ L i j = (c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) := by
    show (hRπ.lift _ _ h12 ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ q₁ L i j = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hRπ.lift_fst, Category.assoc, morphismRestrict_ι,
      Category.assoc]
  have hρ₂ : ρ ≫ q₂ L i j = (c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) := by
    have hι : (q₁ L i j ⁻¹ᵁ V).ι ≫ q₂ L i j = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ V.ι := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
    show (hRπ.lift _ _ h12 ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ q₂ L i j = _
    rw [Category.assoc, hι, ← Category.assoc, hRπ.lift_snd, Category.assoc, morphismRestrict_ι, Category.assoc]

  obtain ⟨t, ht₁⟩ : ∃ t : C ⟶ Spec (CommRingCat.of k),
      (c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := ⟨_, rfl⟩
  have eRS : q₁ L i j ≫ j ≫ f = q₂ L i j ≫ j ≫ f := by
    show (pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = pullback.snd (amap L i j) j ≫ j ≫ f
    rw [Category.assoc, ← amap_over, ← Category.assoc, pullback.condition, Category.assoc]
  have ht₂ : (c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _ ≫ i ≫ f = t := by
    rw [pullback.condition, ← Category.assoc, ← hρ₂, Category.assoc, ← eRS, ← Category.assoc, hρ₁, Category.assoc,
      ← pullback.condition]
    exact ht₁
  have ht'' : (ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst _ _ ≫ i ≫ f = t := by
    rw [pullback.condition, Category.assoc, ← Category.assoc (pullback.fst (amap L i j) j),
      show (pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)) = q₁ L i j from rfl, ← Category.assoc, hρ₁,
      Category.assoc, ← pullback.condition]
    exact ht₁
  let n : SchemeHomOver t (i ≫ f) := ⟨(c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by rw [Category.assoc]; exact ht₁⟩
  let n' : SchemeHomOver t (i ≫ f) := ⟨(c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.fst _ _, by rw [Category.assoc]; exact ht₂⟩
  let n'' : SchemeHomOver t (i ≫ f) := ⟨(ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst _ _, by rw [Category.assoc]; exact ht''⟩
  let jv : SchemeHomOver t f := ⟨(c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j, by
    simp only [Category.assoc]; rw [← pullback.condition]; simpa only [Category.assoc] using ht₁⟩
  let jv' : SchemeHomOver t f := ⟨(c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j, by
    simp only [Category.assoc]; rw [← pullback.condition]; simpa only [Category.assoc] using ht₂⟩
  letI := L.pointGroup t

  have rel : L.mul t (ipt i n'') jv = jv' := by
    apply Subtype.ext
    have e1 := comp_amap L i j (ρ ≫ pullback.fst (amap L i j) j) t ht''
    have e2 : (ρ ≫ pullback.fst (amap L i j) j) ≫ amap L i j = (c₂ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd _ _ ≫ j := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, show ρ ≫ pullback.snd (amap L i j) j = _ from hρ₂,
        Category.assoc]
    rw [e2] at e1
    refine (mul_coe_congr L rfl _ _ _ _ rfl ?_).trans e1.symm
    show (c₁ ≫ (NV (f := f) i j V).ι) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j = (ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd _ _ ≫ j
    rw [← Category.assoc (ρ ≫ _), Category.assoc ρ, show pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f) = q₁ L i j from rfl,
      hρ₁]
    simp only [Category.assoc]

  have hc₁ : (c₁ ≫ (NV (f := f) i j V).ι) ≫ amap L i j = (L.mul t (ipt i n) jv).1 := by
    rw [comp_amap L i j _ t ht₁]
  have hc₂ : (c₂ ≫ (NV (f := f) i j V).ι) ≫ amap L i j = (L.mul t (ipt i n') jv').1 := by
    rw [comp_amap L i j _ t ht₂]

  let m : SchemeHomOver t (i ≫ f) := LN.mul t (LN.mul t n' n'') (LN.inv t n)
  have hmg : m.1 ≫ i ≫ f = (L.mul t (ipt i n) jv).1 ≫ f := by rw [m.2, (L.mul t _ _).2]
  let s₀ : C ⟶ pullback (i ≫ f) f := pullback.lift m.1 (L.mul t (ipt i n) jv).1 hmg
  have hs₀snd : s₀ ≫ pullback.snd (i ≫ f) f = (c₁ ≫ (NV (f := f) i j V).ι) ≫ amap L i j := by
    rw [hc₁]; exact pullback.lift_snd _ _ _
  have hs₀act : s₀ ≫ L.action i = (c₂ ≫ (NV (f := f) i j V).ι) ≫ amap L i j := by
    rw [hc₂, comp_action L i s₀ t (by rw [← Category.assoc, pullback.lift_fst]; exact m.2)]
    have e3 : L.mul t (ipt i ⟨s₀ ≫ pullback.fst (i ≫ f) f, by rw [← Category.assoc, pullback.lift_fst]; exact m.2⟩)
        ⟨s₀ ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.lift_fst]; exact m.2⟩ =
        L.mul t (ipt i m) (L.mul t (ipt i n) jv) := by
      apply Subtype.ext; apply mul_coe_congr L rfl
      · simp only [ipt_coe]; rw [pullback.lift_fst]
      · exact pullback.lift_snd _ _ _
    rw [congrArg Subtype.val e3]
    congr 1
    show L.mul t (ipt i (LN.mul t (LN.mul t n' n'') (LN.inv t n))) (L.mul t (ipt i n) jv) = L.mul t (ipt i n') jv'
    rw [← rel, ipt_mul L i LN hi, ipt_mul L i LN hi, ipt_inv L i LN hi]
    show ipt i n' * ipt i n'' * (ipt i n)⁻¹ * (ipt i n * jv) = ipt i n' * (ipt i n'' * jv)
    rw [mul_assoc, inv_mul_cancel_left, mul_assoc]

  have hrange : Set.range s₀.base ⊆ Set.range (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    show (s₀ ≫ pullback.snd (i ≫ f) f).base z ∈ (Uimg L i j V : Set ↥G)
    rw [hs₀snd, Category.assoc, ← cover_ι, ← Category.assoc]
    show (Uimg L i j V).ι.base ((c₁ ≫ cover L i j V).base z) ∈ (Uimg L i j V : Set ↥G)
    rw [← Scheme.Opens.range_ι (Uimg L i j V)]; exact ⟨_, rfl⟩
  refine ⟨IsOpenImmersion.lift _ s₀ hrange, ?_, ?_⟩
  · rw [← cancel_mono (Uimg L i j V).ι, Category.assoc, P₁_ι, ← Category.assoc, IsOpenImmersion.lift_fac, hs₀snd]
    simp only [Category.assoc, cover_ι]
  · rw [← cancel_mono (Uimg L i j V).ι, Category.assoc, P₂_ι, ← Category.assoc, IsOpenImmersion.lift_fac, hs₀act]
    simp only [Category.assoc, cover_ι]

end Effective

section Effective2

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)
  [UniversallyOpen (amap L i j)] [Flat (amap L i j)] [LocallyOfFinitePresentation (amap L i j)]
  (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V) {Y : Scheme.{u}} (π : V.toScheme ⟶ Y)
  (w : (q₁ L i j ∣_ V) ≫ π = (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ π)
  (hRπ : IsPullback (q₁ L i j ∣_ V) (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) π π)
  (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V = L.action i ⁻¹ᵁ Uimg L i j V)

include LN hi hRπ in

theorem effective :
    IsPullback (P₁ L i j V) (P₂ L i j V hU) (pdesc L i LN hi j V hV π w) (pdesc L i LN hi j V hV π w) := by
  have sq : P₁ L i j V ≫ pdesc L i LN hi j V hV π w = P₂ L i j V hU ≫ pdesc L i LN hi j V hV π w :=
    square L i LN hi j V hV π w hU
  let κ := pullback.lift (P₁ L i j V) (P₂ L i j V hU) sq
  have hκ₁ : κ ≫ pullback.fst _ _ = P₁ L i j V := pullback.lift_fst _ _ _
  have hκ₂ : κ ≫ pullback.snd _ _ = P₂ L i j V hU := pullback.lift_snd _ _ _

  haveI : Mono κ := ⟨fun {T} a b h => by
    have h1 : a ≫ P₁ L i j V = b ≫ P₁ L i j V := by rw [← hκ₁, ← Category.assoc, h, Category.assoc]
    have h2 : a ≫ P₂ L i j V hU = b ≫ P₂ L i j V hU := by rw [← hκ₂, ← Category.assoc, h, Category.assoc]
    rw [← cancel_mono (pullback.snd (i ≫ f) f ⁻¹ᵁ Uimg L i j V).ι]
    apply eq_of_snd_eq_of_action_eq L i LN hi
    · rw [Category.assoc, Category.assoc, ← P₁_ι, ← Category.assoc, h1, Category.assoc]
    · rw [Category.assoc, Category.assoc, ← P₂_ι L i j V hU, ← Category.assoc, h2, Category.assoc]⟩

  let pp := pdesc L i LN hi j V hV π w
  let d₁ := pullback.fst (pullback.fst pp pp) (cover L i j V)
  let e₁ := pullback.fst (d₁ ≫ pullback.snd pp pp) (cover L i j V)
  let cc := e₁ ≫ d₁
  let c₁ := e₁ ≫ pullback.snd (pullback.fst pp pp) (cover L i j V)
  let c₂ := pullback.snd (d₁ ≫ pullback.snd pp pp) (cover L i j V)
  have hcc₁ : cc ≫ pullback.fst pp pp = c₁ ≫ cover L i j V := by
    show (e₁ ≫ d₁) ≫ pullback.fst pp pp = (e₁ ≫ pullback.snd (pullback.fst pp pp) (cover L i j V)) ≫ cover L i j V
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hcc₂ : cc ≫ pullback.snd pp pp = c₂ ≫ cover L i j V := by
    show (e₁ ≫ d₁) ≫ pullback.snd pp pp = _
    rw [Category.assoc]; exact pullback.condition
  have hc : c₁ ≫ cover L i j V ≫ pp = c₂ ≫ cover L i j V ≫ pp := by
    rw [← Category.assoc, ← hcc₁, Category.assoc, pullback.condition, ← Category.assoc, hcc₂, Category.assoc]
  obtain ⟨s, hs₁, hs₂⟩ := exists_section L i LN hi j V hV π w hRπ hU c₁ c₂ hc
  have hsκ : s ≫ κ = cc := by
    apply pullback.hom_ext
    · rw [Category.assoc, hκ₁, hs₁, hcc₁]
    · rw [Category.assoc, hκ₂, hs₂, hcc₂]

  have hsplit : IsSplitEpi (pullback.fst cc κ) :=
    IsSplitEpi.mk' ⟨pullback.lift (𝟙 _) s (by rw [Category.id_comp, hsκ]), pullback.lift_fst _ _ _⟩
  have hiso : IsIso (pullback.fst cc κ) := isIso_of_mono_of_isSplitEpi _

  have hQ : (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) cc :=
    ⟨⟨(inferInstance : Surjective (e₁ ≫ d₁)), (inferInstance : Flat (e₁ ≫ d₁))⟩,
      (inferInstance : LocallyOfFinitePresentation (e₁ ≫ d₁))⟩
  haveI hκ : IsIso κ := (MorphismProperty.isomorphisms.iff κ).1
    (MorphismProperty.of_pullback_fst_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hQ ((MorphismProperty.isomorphisms.iff _).2 hiso))
  exact IsPullback.of_iso_pullback ⟨sq⟩ (asIso κ) hκ₁ hκ₂

end Effective2

end G2eAsm
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient.G2eAsm"

open G2eAsm in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (V : S.Opens) (hV : (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V = (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ⁻¹ᵁ V) [Nonempty (V.toScheme)]
    {Y : Scheme.{u}} (π : V.toScheme ⟶ Y) (w : ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ≫ π = (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) ≫ π)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] [Surjective π]
    (hRπ : IsPullback ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) π π) (hcoeq : IsColimit (Cofork.ofπ π w)) :
    ∃ (U : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U),
      Nonempty (U.toScheme) ∧
      ∃ (Y : Scheme.{u}) (p : (U).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p := by
  haveI := hEt
  haveI : Smooth (amap L i j) := inferInstance
  haveI : Flat (amap L i j) := instFlatOfSmooth _
  haveI : LocallyOfFinitePresentation (amap L i j) := inferInstance
  haveI : UniversallyOpen (amap L i j) := inferInstance
  haveI : Smooth (i ≫ f) := SmoothOfRelativeDimension.smooth h _
  haveI : Flat (i ≫ f) := inferInstance
  haveI : QuasiCompact (i ≫ f) := inferInstance
  haveI : Smooth f := SmoothOfRelativeDimension.smooth g f
  haveI : LocallyOfFinitePresentation f := inferInstance
  haveI : LocallyOfFiniteType f := inferInstance
  have hU := Uimg_saturated L i LN hi j V
  refine ⟨Uimg L i j V, hU, nonempty_Uimg L i LN j V, Y, pdesc L i LN hi j V hV π w,
    square L i LN hi j V hV π w hU, flat_pdesc L i LN hi j V hV π w,
    locallyOfFinitePresentation_pdesc L i LN hi j V hV π w hcoeq, quasiCompact_pdesc L i LN hi j V hV π w,
    surjective_pdesc L i LN hi j V hV π w, effective L i LN hi j V hV π w hRπ hU⟩

end
end S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient (solution)
