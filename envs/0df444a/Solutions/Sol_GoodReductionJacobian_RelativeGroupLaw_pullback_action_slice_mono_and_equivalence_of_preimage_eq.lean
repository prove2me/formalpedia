-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.pullback_action_slice_mono_and_equivalence_of_preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0ff9bf0b-83d0-5b7a-af8e-dd71d33b0cbc

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_pullback_action_slice_mono_and_equivalence_of_preimage_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace G2cD

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

end Action

section Rel

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
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

variable (hV : q₁ L i j ⁻¹ᵁ V = q₂ L i j ⁻¹ᵁ V)

abbrev r₂ : (q₁ L i j ⁻¹ᵁ V).toScheme ⟶ V.toScheme :=
  ((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)

omit hi in
theorem r₁_ι : (q₁ L i j ∣_ V) ≫ V.ι = (q₁ L i j ⁻¹ᵁ V).ι ≫ q₁ L i j := morphismRestrict_ι _ _

omit hi in
theorem r₂_ι : r₂ L i j V hV ≫ V.ι = (q₁ L i j ⁻¹ᵁ V).ι ≫ q₂ L i j := by
  show (((pullback (amap L i j) j).isoOfEq hV).hom ≫ (q₂ L i j ∣_ V)) ≫ V.ι = _
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]

include LN hi in

theorem rel_of_point {T : Scheme.{u}} (φ : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme) (t : T ⟶ Spec (CommRingCat.of k))
    (ht : (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = t) :
    ∃ (n : SchemeHomOver t (i ≫ f)),
      n.1 = ((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f) ∧
      (L.mul t (ipt i n) ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht⟩).1 =
        (φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j := by
  have hs : (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι = ((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) := by
    rw [Category.assoc, r₁_ι]; simp only [Category.assoc]
  have hs' : (φ ≫ r₂ L i j V hV) ≫ V.ι = (φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.snd (amap L i j) j := by
    rw [Category.assoc, r₂_ι, Category.assoc]
  have htz : ((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) ≫ pullback.fst _ _ ≫ i ≫ f = t := by
    rw [pullback.condition, ← Category.assoc, ← hs, Category.assoc]; exact ht
  refine ⟨⟨((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f), by rw [Category.assoc]; exact htz⟩, rfl, ?_⟩
  have e := comp_amap L i j ((φ ≫ (q₁ L i j ⁻¹ᵁ V).ι) ≫ pullback.fst (amap L i j) j) t htz
  rw [Category.assoc, pullback.condition, ← Category.assoc] at e

  rw [← Category.assoc (φ ≫ r₂ L i j V hV) V.ι j, hs']
  refine (mul_coe_congr L rfl _ _ _ _ rfl ?_).trans e.symm
  show (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j = _
  rw [← Category.assoc, hs, Category.assoc]

include LN hi in

theorem exists_point {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : SchemeHomOver t (i ≫ f))
    (s s' : T ⟶ V.toScheme) (hs : (s ≫ V.ι) ≫ j ≫ f = t)
    (hrel : (L.mul t (ipt i n) ⟨(s ≫ V.ι) ≫ j, by rw [Category.assoc]; exact hs⟩).1 = (s' ≫ V.ι) ≫ j) :
    ∃ φ : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme, φ ≫ (q₁ L i j ∣_ V) = s ∧ φ ≫ r₂ L i j V hV = s' := by
  let r : T ⟶ pullback (i ≫ f) (j ≫ f) := pairNS i j n (s ≫ V.ι) hs
  have hr : r ≫ amap L i j = (s' ≫ V.ι) ≫ j := by
    show pairNS i j n (s ≫ V.ι) hs ≫ amap L i j = _
    rw [pairNS_amap]; exact hrel
  let ρ : T ⟶ pullback (amap L i j) j := pullback.lift r (s' ≫ V.ι) hr
  have hρ₁ : ρ ≫ q₁ L i j = s ≫ V.ι := by
    show ρ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [← Category.assoc, pullback.lift_fst]; exact pairNS_snd i j _ _ hs
  have hρ₂ : ρ ≫ q₂ L i j = s' ≫ V.ι := pullback.lift_snd _ _ _
  have hρV : Set.range ρ.base ⊆ Set.range (q₁ L i j ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    show (ρ ≫ q₁ L i j).base z ∈ (V : Set ↥S)
    rw [hρ₁]
    show V.ι.base (s.base z) ∈ (V : Set ↥S)
    rw [← Scheme.Opens.range_ι V]; exact ⟨_, rfl⟩
  refine ⟨IsOpenImmersion.lift _ ρ hρV, ?_, ?_⟩
  · rw [← cancel_mono V.ι, Category.assoc, r₁_ι, ← Category.assoc, IsOpenImmersion.lift_fac, hρ₁]
  · rw [← cancel_mono V.ι, Category.assoc, r₂_ι, ← Category.assoc, IsOpenImmersion.lift_fac, hρ₂]

omit hi in
theorem eRS : q₁ L i j ≫ j ≫ f = q₂ L i j ≫ j ≫ f := by
  show (pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = pullback.snd (amap L i j) j ≫ j ≫ f
  rw [Category.assoc, ← amap_over, ← Category.assoc, pullback.condition, Category.assoc]

omit hi in

theorem legs_over {T : Scheme.{u}} (φ : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme) :
    (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = (φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j ≫ f := by
  have l : (φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = φ ≫ (q₁ L i j ⁻¹ᵁ V).ι ≫ q₁ L i j ≫ j ≫ f := by
    rw [Category.assoc, ← Category.assoc (q₁ L i j ∣_ V) V.ι, r₁_ι, Category.assoc]
  have r : (φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j ≫ f = φ ≫ (q₁ L i j ⁻¹ᵁ V).ι ≫ q₂ L i j ≫ j ≫ f := by
    rw [Category.assoc, ← Category.assoc (r₂ L i j V hV) V.ι, r₂_ι, Category.assoc]
  rw [l, r, eRS]

include LN hi in

theorem mono {T : Scheme.{u}} (x y : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme)
    (h₁ : x ≫ (q₁ L i j ∣_ V) = y ≫ (q₁ L i j ∣_ V)) (h₂ : x ≫ r₂ L i j V hV = y ≫ r₂ L i j V hV) : x = y := by
  obtain ⟨t, ht⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k), (x ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = t := ⟨_, rfl⟩
  have ht' : (y ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = t := by rw [← h₁]; exact ht
  obtain ⟨nx, hnx, relx⟩ := rel_of_point L i LN hi j V hV x t ht
  obtain ⟨ny, hny, rely⟩ := rel_of_point L i LN hi j V hV y t ht'
  letI := L.pointGroup t
  have hj : (⟨(x ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht⟩ : SchemeHomOver t f) =
      ⟨(y ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht'⟩ :=
    Subtype.ext (by show (x ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j = (y ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j; rw [h₁])
  have key : ipt i nx = ipt i ny := by
    have e : L.mul t (ipt i nx) ⟨(x ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht⟩ =
        L.mul t (ipt i ny) ⟨(y ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht'⟩ :=
      Subtype.ext (by rw [relx, rely, h₂])
    rw [hj] at e
    exact mul_right_cancel e
  have hn := congrArg Subtype.val (ipt_injective i _ _ key)
  rw [hnx, hny] at hn
  have h₁' : (x ≫ (q₁ L i j ∣_ V)) ≫ V.ι = (y ≫ (q₁ L i j ∣_ V)) ≫ V.ι := by rw [h₁]
  rw [Category.assoc, r₁_ι, Category.assoc, r₁_ι] at h₁'
  have h₂' : (x ≫ r₂ L i j V hV) ≫ V.ι = (y ≫ r₂ L i j V hV) ≫ V.ι := by rw [h₂]
  rw [Category.assoc, r₂_ι, Category.assoc, r₂_ι] at h₂'

  rw [← cancel_mono (q₁ L i j ⁻¹ᵁ V).ι]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using hn
    · simpa only [Category.assoc] using h₁'
  · simpa only [Category.assoc] using h₂'

include LN hi in

theorem equivalence (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ V.toScheme =>
      ∃ φ : T ⟶ (q₁ L i j ⁻¹ᵁ V).toScheme, φ ≫ (q₁ L i j ∣_ V) = x ∧ φ ≫ r₂ L i j V hV = y := by
  refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
  ·
    obtain ⟨t, ht⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k), (x ≫ V.ι) ≫ j ≫ f = t := ⟨_, rfl⟩
    refine exists_point L i LN hi j V hV t (LN.one t) x x ht ?_
    rw [ipt_one L i LN hi, L.one_mul]
  ·
    obtain ⟨φ, rfl, rfl⟩ := hxy
    obtain ⟨t, ht⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k), ((φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι) ≫ j ≫ f = t := ⟨_, rfl⟩
    obtain ⟨n, -, rel⟩ := rel_of_point L i LN hi j V hV φ t (by simpa only [Category.assoc] using ht)
    have ht' : ((φ ≫ r₂ L i j V hV) ≫ V.ι) ≫ j ≫ f = t := by
      rw [Category.assoc, ← legs_over L i j V hV φ]; simpa only [Category.assoc] using ht
    refine exists_point L i LN hi j V hV t (LN.inv t n) _ _ ht' ?_
    letI := L.pointGroup t
    rw [ipt_inv L i LN hi]
    have e : (⟨(φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j, by rw [Category.assoc] at ht'; rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht'⟩ : SchemeHomOver t f) =
        L.mul t (ipt i n) ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht⟩ :=
      Subtype.ext rel.symm
    have e2 : L.mul t (L.inv t (ipt i n)) ⟨((φ ≫ r₂ L i j V hV) ≫ V.ι) ≫ j, by rw [Category.assoc]; exact ht'⟩ =
        ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht⟩ := by
      have : (⟨((φ ≫ r₂ L i j V hV) ≫ V.ι) ≫ j, by rw [Category.assoc]; exact ht'⟩ : SchemeHomOver t f) =
          ⟨(φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j, by rw [Category.assoc] at ht'; rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht'⟩ :=
        Subtype.ext (Category.assoc _ _ _)
      rw [this, e]
      show (ipt i n)⁻¹ * (ipt i n * _) = _
      rw [inv_mul_cancel_left]
    rw [congrArg Subtype.val e2]
    exact Category.assoc _ _ _
  ·
    obtain ⟨φ, rfl, rfl⟩ := hxy
    obtain ⟨ψ, hψ, rfl⟩ := hyz
    obtain ⟨t, ht⟩ : ∃ t : T ⟶ Spec (CommRingCat.of k), ((φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι) ≫ j ≫ f = t := ⟨_, rfl⟩
    obtain ⟨n, -, rel⟩ := rel_of_point L i LN hi j V hV φ t (by simpa only [Category.assoc] using ht)
    have htψ : (ψ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j ≫ f = t := by
      rw [hψ, ← legs_over L i j V hV φ]; simpa only [Category.assoc] using ht
    obtain ⟨n', -, rel'⟩ := rel_of_point L i LN hi j V hV ψ t htψ
    refine exists_point L i LN hi j V hV t (LN.mul t n' n) _ _ (by simpa only [Category.assoc] using ht) ?_
    letI := L.pointGroup t
    rw [ipt_mul L i LN hi, L.mul_assoc]
    have e1 : L.mul t (ipt i n) ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht⟩ =
        ⟨(ψ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using htψ⟩ := by
      apply Subtype.ext; rw [rel]; show (φ ≫ r₂ L i j V hV) ≫ V.ι ≫ j = (ψ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j; rw [hψ]
    have e0 : (⟨((φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι) ≫ j, by rw [Category.assoc]; simpa only [Category.assoc] using ht⟩ : SchemeHomOver t f) =
        ⟨(φ ≫ (q₁ L i j ∣_ V)) ≫ V.ι ≫ j, by rw [Category.assoc, Category.assoc]; simpa only [Category.assoc] using ht⟩ :=
      Subtype.ext (Category.assoc _ _ _)
    rw [e0, e1, rel']
    exact Category.assoc _ _ _

end Rel

end G2cD
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_pullback_action_slice_mono_and_equivalence_of_preimage_eq.G2cD"

open G2cD in
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
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (V : S.Opens)
    (hV : (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V = (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ⁻¹ᵁ V) :
    (∀ {T : Scheme.{u}} (x y : T ⟶ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme),
        x ≫ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) = y ≫ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) → x ≫ (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) = y ≫ (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) → x = y) ∧
      (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ V.toScheme =>
        ∃ φ : T ⟶ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme, φ ≫ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) = x ∧ φ ≫ (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) = y) := by
  refine ⟨fun x y h₁ h₂ => G2cD.mono L i LN hi j V hV x y h₁ h₂, fun T => G2cD.equivalence L i LN hi j V hV T⟩

end
end S_GoodReductionJacobian_RelativeGroupLaw_pullback_action_slice_mono_and_equivalence_of_preimage_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_pullback_action_slice_mono_and_equivalence_of_preimage_eq (solution)
