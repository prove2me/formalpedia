-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3965d763-7be3-581d-b693-6b24d05f6c63

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace FinLocus29

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

section Translations

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

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

omit LN in
theorem amap_over : amap L i j ≫ f = pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f := by
  show (pullback.map _ _ _ _ _ _ _ _ _ ≫ L.action i) ≫ f = _
  rw [Category.assoc, RelativeGroupLaw.action_over, RelativeGroupLaw.actionSource, ← Category.assoc,
    pullback.lift_snd, Category.assoc]

omit LN in
theorem amap_over' : amap L i j ≫ f = pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f := by
  rw [amap_over, pullback.condition]

end Translations

section Generic

variable {k : Type u} [Field k] {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} (M : RelativeGroupLaw k g)

def cst (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : SchemeHomOver g g :=
  GoodReductionJacobian.schemeHomOverComp g (Category.comp_id g) P

@[scoped simp] theorem cst_coe (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : (cst P).1 = g ≫ P.1 := rfl

def idpt : SchemeHomOver g g := ⟨𝟙 H, Category.id_comp _⟩

@[scoped simp] theorem idpt_coe : (idpt : SchemeHomOver g g).1 = 𝟙 H := rfl

private def _root_.FinLocus29.trans (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : H ⟶ H := (M.mul g (cst P) idpt).1

p2m_export "FinLocus29" "trans"
theorem trans_over (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : trans M P ≫ g = g := (M.mul g (cst P) idpt).2

theorem comp_trans (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ H) (hx : x ≫ g = t) :
    x ≫ trans M P = (M.mul t ⟨t ≫ P.1, by rw [Category.assoc, P.2, Category.comp_id]⟩ ⟨x, hx⟩).1 := by
  have h := congrArg Subtype.val (M.mul_natural g t x hx (cst P) idpt)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  unfold trans
  rw [h]
  apply mul_coe_congr M rfl
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, cst_coe, ← Category.assoc, hx]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, idpt_coe, Category.comp_id]

theorem cst_mul (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    M.mul g (cst Q) (cst P) = cst (M.mul (𝟙 _) Q P) := by
  unfold cst
  exact (M.mul_natural (𝟙 _) g g (Category.comp_id g) Q P).symm

theorem cst_one : cst (M.one (𝟙 (Spec (CommRingCat.of k)))) = (M.one g : SchemeHomOver g g) := by
  unfold cst
  exact M.one_natural (𝟙 _) g g (Category.comp_id g)

theorem trans_trans (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    trans M P ≫ trans M Q = trans M (M.mul (𝟙 _) Q P) := by
  rw [comp_trans M Q g (trans M P) (trans_over M P)]
  have hP : (⟨trans M P, trans_over M P⟩ : SchemeHomOver g g) = M.mul g (cst P) idpt := Subtype.ext rfl
  have hQ : (⟨g ≫ Q.1, by rw [Category.assoc, Q.2, Category.comp_id]⟩ : SchemeHomOver g g) = cst Q := Subtype.ext rfl
  rw [hP, hQ, ← M.mul_assoc, cst_mul]
  rfl

theorem trans_one : trans M (M.one (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 H := by
  unfold trans
  rw [cst_one, M.one_mul]
  rfl

theorem trans_inv_comp (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    trans M P ≫ trans M (M.inv (𝟙 _) P) = 𝟙 H := by
  rw [trans_trans, M.inv_mul_cancel, trans_one]

theorem trans_comp_inv (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    trans M (M.inv (𝟙 _) P) ≫ trans M P = 𝟙 H := by
  rw [trans_trans, M.mul_inv_cancel, trans_one]

def transIso (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : H ≅ H where
  hom := trans M P
  inv := trans M (M.inv (𝟙 _) P)
  hom_inv_id := trans_inv_comp M P
  inv_hom_id := trans_comp_inv M P

scoped instance isIso_trans (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) : IsIso (trans M P) :=
  (transIso M P).isIso_hom

end Generic

section Equivariance

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) {S : Scheme.{u}} (j : S ⟶ G)

variable (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))

def transNS (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :
    pullback (i ≫ f) (j ≫ f) ⟶ pullback (i ≫ f) (j ≫ f) :=
  pullback.map (i ≫ f) (j ≫ f) (i ≫ f) (j ≫ f) (trans LN Q) (𝟙 S) (𝟙 _)
    (by rw [Category.comp_id, trans_over]) (by rw [Category.comp_id, Category.id_comp])

scoped instance isIso_transNS (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) : IsIso (transNS i LN j Q) := by
  unfold transNS
  infer_instance

theorem transNS_fst (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :
    transNS i LN j Q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ trans LN Q := pullback.lift_fst _ _ _

theorem transNS_snd (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :
    transNS i LN j Q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 S := pullback.lift_snd _ _ _

include hi in

theorem amap_trans (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)) :
    amap L i j ≫ trans L (ipt i Q) = transNS i LN j Q ≫ amap L i j := by

  have ht' : transNS i LN j Q ≫ pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f = pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f := by
    rw [← Category.assoc, transNS_fst, Category.assoc, trans_over]
  rw [comp_amap L i j (transNS i LN j Q) _ ht',
    comp_trans L (ipt i Q) (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) (amap L i j) (amap_over' L i j)]

  have ha : (⟨amap L i j, amap_over' L i j⟩ : SchemeHomOver (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) f) =
      L.mul _ (ipt i ⟨pullback.fst (i ≫ f) (j ≫ f), rfl⟩)
        ⟨pullback.snd (i ≫ f) (j ≫ f) ≫ j, by rw [Category.assoc, ← pullback.condition]⟩ := by
    apply Subtype.ext
    have := comp_amap L i j (𝟙 _) (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) (by rw [Category.id_comp])
    rw [Category.id_comp] at this
    change amap L i j = _
    rw [this]
    apply mul_coe_congr L rfl
    · simp only [ipt_coe, Category.id_comp]
    · show 𝟙 _ ≫ pullback.snd _ _ ≫ j = pullback.snd _ _ ≫ j
      rw [Category.id_comp]

  have hN : (ipt i ⟨transNS i LN j Q ≫ pullback.fst (i ≫ f) (j ≫ f), ht'⟩ :
      SchemeHomOver (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) f) =
      L.mul _ ⟨(pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) ≫ (ipt i Q).1, by
          rw [Category.assoc, (ipt i Q).2, Category.comp_id]⟩
        (ipt i ⟨pullback.fst (i ≫ f) (j ≫ f), rfl⟩) := by
    have h1 : (⟨transNS i LN j Q ≫ pullback.fst (i ≫ f) (j ≫ f), ht'⟩ :
        SchemeHomOver (pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) (i ≫ f)) =
        LN.mul _ ⟨(pullback.fst (i ≫ f) (j ≫ f) ≫ i ≫ f) ≫ Q.1, by rw [Category.assoc, Q.2, Category.comp_id]⟩
          ⟨pullback.fst (i ≫ f) (j ≫ f), rfl⟩ := by
      apply Subtype.ext
      show transNS i LN j Q ≫ pullback.fst (i ≫ f) (j ≫ f) = _
      rw [transNS_fst, comp_trans LN Q _ _ rfl]
    rw [h1, ipt_mul L i LN hi]
    congr 1
  rw [ha, hN, L.mul_assoc]
  apply mul_coe_congr L rfl _ _ _ _ rfl
  apply mul_coe_congr L rfl _ _ _ _ rfl
  show pullback.snd (i ≫ f) (j ≫ f) ≫ j = transNS i LN j Q ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j
  rw [← Category.assoc, transNS_snd, Category.comp_id]

omit LN hi in
theorem preimage_mono' {X Y : Scheme.{u}} (a : X ⟶ Y) {U V : Y.Opens} (h : U ≤ V) :
    a ⁻¹ᵁ U ≤ a ⁻¹ᵁ V := fun _ hx => h hx

omit LN hi in
theorem isFinite_restrict_congr {X Y : Scheme.{u}} {a b : X ⟶ Y} (e : a = b) (W : Y.Opens) (h : IsFinite (a ∣_ W)) :
    IsFinite (b ∣_ W) := by
  subst e; exact h

include hi in

theorem isFinite_restrict_preimage_trans (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f))
    (W : G.Opens) (hW : IsFinite (amap L i j ∣_ W)) :
    IsFinite (amap L i j ∣_ (trans L (ipt i Q) ⁻¹ᵁ W)) := by
  haveI := hW
  haveI : IsFinite (transNS i LN j Q) := MorphismProperty.of_isIso @IsFinite _
  have h1 : IsFinite ((transNS i LN j Q ≫ amap L i j) ∣_ W) := by
    rw [morphismRestrict_comp]
    exact MorphismProperty.comp_mem @IsFinite _ _ (IsZariskiLocalAtTarget.restrict (P := @IsFinite) ‹IsFinite (transNS i LN j Q)› _) hW
  have h2 : IsFinite ((amap L i j ≫ trans L (ipt i Q)) ∣_ W) :=
    isFinite_restrict_congr (amap_trans L i LN j hi Q).symm W h1
  rw [morphismRestrict_comp] at h2
  exact (MorphismProperty.cancel_right_of_respectsIso @IsFinite _ _).1 h2

end Equivariance

end FinLocus29
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable.FinLocus29"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable.FinLocus29"

open FinLocus29

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
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)) :
    ∃ U : G.Opens,
      IsFinite ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ U) ∧
      (∀ W : G.Opens, IsFinite ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ W) → W ≤ U) ∧
      (∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
        (L.mul f ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U = U) := by

  refine ⟨sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}, ?_, fun W hW => le_sSup hW, ?_⟩
  ·
    apply IsZariskiLocalAtTarget.of_iSup_eq_top
      (fun W : {W : G.Opens // IsFinite (amap L i j ∣_ W)} =>
        (sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ⁻¹ᵁ W.1)
    · rw [← Scheme.Hom.preimage_iSup]
      have hs : (⨆ W : {W : G.Opens // IsFinite (amap L i j ∣_ W)}, W.1) =
          sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} := (sSup_eq_iSup' _).symm
      rw [hs]
      exact Scheme.Opens.ι_preimage_self _
    · rintro ⟨W, hW⟩
      haveI := hW
      have hle : W ≤ sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} := le_sSup hW
      have heq : (sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ''ᵁ
          ((sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ⁻¹ᵁ W) = W := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
        exact hle
      have h : IsFinite (amap L i j ∣_ ((sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ''ᵁ
          ((sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}).ι ⁻¹ᵁ W))) := by rw [heq]; exact hW
      exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict _ _ _)).2 h
  ·
    intro n hn
    have key : ∀ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)),
        trans L (ipt i Q) ⁻¹ᵁ sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} ≤
          sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} := by
      intro Q
      rw [sSup_eq_iSup', Scheme.Hom.preimage_iSup]
      refine iSup_le fun W => ?_
      rw [← sSup_eq_iSup']
      exact le_sSup (isFinite_restrict_preimage_trans L i LN j hi Q W.1 W.2)
    have htr : (L.mul f ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 =
        trans L (ipt i ⟨n, hn⟩) := rfl
    rw [htr]
    apply le_antisymm (key ⟨n, hn⟩)

    have hinv := key (LN.inv (𝟙 _) ⟨n, hn⟩)
    have hcomp : trans L (ipt i ⟨n, hn⟩) ≫ trans L (ipt i (LN.inv (𝟙 _) ⟨n, hn⟩)) = 𝟙 G := by
      rw [ipt_inv L i LN hi, trans_inv_comp]
    calc sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}
        = (trans L (ipt i ⟨n, hn⟩) ≫ trans L (ipt i (LN.inv (𝟙 _) ⟨n, hn⟩))) ⁻¹ᵁ
            sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} := by rw [hcomp]; rfl
      _ = trans L (ipt i ⟨n, hn⟩) ⁻¹ᵁ (trans L (ipt i (LN.inv (𝟙 _) ⟨n, hn⟩)) ⁻¹ᵁ
            sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)}) := rfl
      _ ≤ trans L (ipt i ⟨n, hn⟩) ⁻¹ᵁ sSup {W : G.Opens | IsFinite (amap L i j ∣_ W)} :=
            preimage_mono' _ hinv

end S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable (solution)
