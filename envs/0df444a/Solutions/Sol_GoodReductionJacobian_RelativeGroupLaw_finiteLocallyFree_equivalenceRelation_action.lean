-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.finiteLocallyFree_equivalenceRelation_action
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ca5d7ea0-79dc-5ac5-8474-33ddfa745242

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
namespace ActionGroupoid
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Points

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem one_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') : GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
  letI := L.pointGroup t'
  have h := L.mul_natural t t' ψ hψ (L.one t) (L.one t)
  rw [L.one_mul] at h
  have h' : (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) : SchemeHomOver t' f) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) * GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) := h
  exact (left_eq_mul.mp h').symm ▸ rfl

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h := L.mul_natural t t' ψ hψ (L.inv t x) x
  rw [L.inv_mul_cancel, one_natural] at h
  exact (eq_inv_of_mul_eq_one_left h.symm : _)

theorem mul_inv_mul_cancel_left {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t f) :
    (L.mul t (L.inv t a) (L.mul t a b)).1 = (𝟙 T ≫ b.1) := by
  letI := L.pointGroup t
  rw [Category.id_comp]
  exact congrArg Subtype.val (inv_mul_cancel_left a b)

theorem mul_mul_inv_cancel_left {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t f) :
    (L.mul t a (L.mul t (L.inv t a) b)).1 = (𝟙 T ≫ b.1) := by
  letI := L.pointGroup t
  rw [Category.id_comp]
  exact congrArg Subtype.val (mul_inv_cancel_left a b)

variable {E : Scheme.{u}} (ι : E ⟶ J)

theorem action_over : L.action ι ≫ f = RelativeGroupLaw.actionSource f ι := (L.mul _ _ _).2

noncomputable abbrev ePt : SchemeHomOver (RelativeGroupLaw.actionSource f ι) f := L.actionFstPoint ι

noncomputable abbrev xPt : SchemeHomOver (RelativeGroupLaw.actionSource f ι) f := L.actionSndPoint ι

theorem action_eq : L.action ι = (L.mul _ (ePt L ι) (xPt L ι)).1 := rfl

theorem comp_action {T : Scheme.{u}} (φ : T ⟶ pullback (ι ≫ f) f) :
    φ ≫ L.action ι = (L.mul (φ ≫ RelativeGroupLaw.actionSource f ι)
      (GoodReductionJacobian.schemeHomOverComp φ rfl (ePt L ι)) (GoodReductionJacobian.schemeHomOverComp φ rfl (xPt L ι))).1 := by
  rw [← L.mul_natural _ _ φ rfl, GoodReductionJacobian.schemeHomOverComp_coe, action_eq]

end Points

section Shear

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J)

noncomputable def shear : pullback (ι ≫ f) f ⟶ pullback (ι ≫ f) f :=
  pullback.lift (pullback.fst _ _) (L.action ι) (by rw [action_over]; exact pullback.condition)

@[scoped simp] theorem shear_fst : shear L ι ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
@[scoped simp] theorem shear_snd : shear L ι ≫ pullback.snd _ _ = L.action ι := pullback.lift_snd _ _ _
theorem shear_src : shear L ι ≫ RelativeGroupLaw.actionSource f ι = RelativeGroupLaw.actionSource f ι := by
  change shear L ι ≫ pullback.snd _ _ ≫ f = _
  rw [← Category.assoc, shear_snd, action_over]

noncomputable def actInv : pullback (ι ≫ f) f ⟶ J := (L.mul _ (L.inv _ (ePt L ι)) (xPt L ι)).1

theorem actInv_over : actInv L ι ≫ f = RelativeGroupLaw.actionSource f ι := (L.mul _ _ _).2

theorem comp_actInv {T : Scheme.{u}} (φ : T ⟶ pullback (ι ≫ f) f) :
    φ ≫ actInv L ι = (L.mul (φ ≫ RelativeGroupLaw.actionSource f ι)
      (L.inv _ (GoodReductionJacobian.schemeHomOverComp φ rfl (ePt L ι))) (GoodReductionJacobian.schemeHomOverComp φ rfl (xPt L ι))).1 := by
  rw [← inv_natural, ← L.mul_natural _ _ φ rfl, GoodReductionJacobian.schemeHomOverComp_coe]; rfl

noncomputable def unshear : pullback (ι ≫ f) f ⟶ pullback (ι ≫ f) f :=
  pullback.lift (pullback.fst _ _) (actInv L ι) (by rw [actInv_over]; exact pullback.condition)

@[scoped simp] theorem unshear_fst : unshear L ι ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
@[scoped simp] theorem unshear_snd : unshear L ι ≫ pullback.snd _ _ = actInv L ι := pullback.lift_snd _ _ _
theorem unshear_src : unshear L ι ≫ RelativeGroupLaw.actionSource f ι = RelativeGroupLaw.actionSource f ι := by
  change unshear L ι ≫ pullback.snd _ _ ≫ f = _
  rw [← Category.assoc, unshear_snd, actInv_over]

theorem shear_unshear : shear L ι ≫ unshear L ι = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, unshear_fst, shear_fst, Category.id_comp]
  · rw [Category.assoc, unshear_snd, Category.id_comp, comp_actInv]
    letI := L.pointGroup (shear L ι ≫ RelativeGroupLaw.actionSource f ι)
    have he : GoodReductionJacobian.schemeHomOverComp (shear L ι) rfl (ePt L ι) =
        (⟨pullback.fst _ _ ≫ ι, by rw [shear_src, Category.assoc, pullback.condition]⟩ : SchemeHomOver _ f) :=
      Subtype.ext (by
        show shear L ι ≫ (pullback.fst (ι ≫ f) f ≫ ι) = pullback.fst (ι ≫ f) f ≫ ι
        rw [← Category.assoc, shear_fst])
    have hx : GoodReductionJacobian.schemeHomOverComp (shear L ι) rfl (xPt L ι) =
        L.mul _ (⟨pullback.fst _ _ ≫ ι, by rw [shear_src, Category.assoc, pullback.condition]⟩ : SchemeHomOver _ f)
          ⟨pullback.snd _ _, by rw [shear_src]⟩ := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe]
      change shear L ι ≫ pullback.snd _ _ = _
      rw [shear_snd, action_eq]

      have h := congrArg Subtype.val (L.mul_natural (RelativeGroupLaw.actionSource f ι) (shear L ι ≫ RelativeGroupLaw.actionSource f ι) (𝟙 _)
        (by rw [Category.id_comp, shear_src]) (ePt L ι) (xPt L ι))
      rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at h
      rw [h]
      try (congr 1 <;> exact Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]))
    rw [he, hx, mul_inv_mul_cancel_left]
    exact Category.id_comp _

theorem unshear_shear : unshear L ι ≫ shear L ι = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, shear_fst, unshear_fst, Category.id_comp]
  · rw [Category.assoc, shear_snd, Category.id_comp, comp_action]
    letI := L.pointGroup (unshear L ι ≫ RelativeGroupLaw.actionSource f ι)
    have he : GoodReductionJacobian.schemeHomOverComp (unshear L ι) rfl (ePt L ι) =
        (⟨pullback.fst _ _ ≫ ι, by rw [unshear_src, Category.assoc, pullback.condition]⟩ : SchemeHomOver _ f) :=
      Subtype.ext (by
        show unshear L ι ≫ (pullback.fst (ι ≫ f) f ≫ ι) = pullback.fst (ι ≫ f) f ≫ ι
        rw [← Category.assoc, unshear_fst])
    have hx : GoodReductionJacobian.schemeHomOverComp (unshear L ι) rfl (xPt L ι) =
        L.mul _ (L.inv _ (⟨pullback.fst _ _ ≫ ι, by rw [unshear_src, Category.assoc, pullback.condition]⟩ : SchemeHomOver _ f))
          ⟨pullback.snd _ _, by rw [unshear_src]⟩ := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe]
      change unshear L ι ≫ pullback.snd _ _ = _
      rw [unshear_snd, actInv]
      have h := congrArg Subtype.val (L.mul_natural (RelativeGroupLaw.actionSource f ι) (unshear L ι ≫ RelativeGroupLaw.actionSource f ι) (𝟙 _)
        (by rw [Category.id_comp, unshear_src]) (L.inv _ (ePt L ι)) (xPt L ι))
      rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at h
      rw [h, inv_natural]
      try (congr 1 <;> first
        | (congr 1; exact Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]))
        | exact Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]))
    rw [he, hx, mul_mul_inv_cancel_left]
    exact Category.id_comp _

noncomputable def shearIso : pullback (ι ≫ f) f ≅ pullback (ι ≫ f) f :=
  ⟨shear L ι, unshear L ι, shear_unshear L ι, unshear_shear L ι⟩

scoped instance : IsIso (shear L ι) := (shearIso L ι).isIso_hom

theorem action_eq_shear_snd : L.action ι = shear L ι ≫ pullback.snd _ _ := (shear_snd L ι).symm

end Shear

end GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
namespace ActionGroupoid
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Relation

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]

noncomputable def pt {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : T ⟶ pullback (ι ≫ f) f :=
  pullback.lift e x h

@[scoped simp] theorem pt_fst {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : pt ι e x h ≫ pullback.fst _ _ = e :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem pt_snd {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : pt ι e x h ≫ pullback.snd _ _ = x :=
  pullback.lift_snd _ _ _

theorem comp_action' {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (φ : T ⟶ pullback (ι ≫ f) f)
    (ht : φ ≫ RelativeGroupLaw.actionSource f ι = t) :
    φ ≫ L.action ι = (L.mul t ⟨φ ≫ pullback.fst _ _ ≫ ι, by
        rw [← ht, Category.assoc, Category.assoc]; exact congrArg (φ ≫ ·) pullback.condition⟩
      ⟨φ ≫ pullback.snd _ _, by rw [← ht, Category.assoc]⟩).1 := by
  subst ht
  rw [comp_action]
  congr 1 <;> first
    | (congr 1 <;> exact Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]))
    | rfl

theorem comp_action_pt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (x : SchemeHomOver t f)
    (he : e ≫ ι ≫ f = t) (hx : e ≫ ι ≫ f = x.1 ≫ f) :
    pt ι e x.1 hx ≫ L.action ι = (L.mul t ⟨e ≫ ι, he⟩ x).1 := by
  have hsrc : pt ι e x.1 hx ≫ RelativeGroupLaw.actionSource f ι = t := by
    show pt ι e x.1 hx ≫ (pullback.snd _ _ ≫ f) = t
    rw [← Category.assoc, pt_snd]; exact x.2
  rw [comp_action' L ι t _ hsrc]
  congr 2
  · exact Subtype.ext (by show pt ι e x.1 hx ≫ pullback.fst _ _ ≫ ι = e ≫ ι; rw [← Category.assoc, pt_fst])
  · exact Subtype.ext (by show pt ι e x.1 hx ≫ pullback.snd _ _ = x.1; rw [pt_snd])

theorem cancel_aux {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (A₁ A₂ X : SchemeHomOver t f)
    (h : L.mul t A₁ X = L.mul t A₂ X) : A₁ = A₂ := by
  letI := L.pointGroup t
  change A₁ * X = A₂ * X at h
  exact mul_right_cancel h

theorem jointly_mono {T : Scheme.{u}} (a b : T ⟶ pullback (ι ≫ f) f)
    (hs : a ≫ pullback.snd (ι ≫ f) f = b ≫ pullback.snd (ι ≫ f) f) (ht : a ≫ L.action ι = b ≫ L.action ι) : a = b := by
  have hbase : a ≫ RelativeGroupLaw.actionSource f ι = b ≫ RelativeGroupLaw.actionSource f ι := by
    show a ≫ (pullback.snd _ _ ≫ f) = b ≫ (pullback.snd _ _ ≫ f)
    rw [← Category.assoc, hs, Category.assoc]
  rw [comp_action' L ι _ a rfl, comp_action' L ι _ b hbase.symm] at ht
  have ht' := Subtype.ext ht
  have hx : (⟨a ≫ pullback.snd _ _, by rw [Category.assoc]⟩ : SchemeHomOver (a ≫ RelativeGroupLaw.actionSource f ι) f) =
      ⟨b ≫ pullback.snd _ _, by rw [Category.assoc]; exact hbase.symm⟩ := Subtype.ext hs
  rw [hx] at ht'
  have he := congrArg Subtype.val (cancel_aux L _ _ _ _ ht')
  change a ≫ pullback.fst _ _ ≫ ι = b ≫ pullback.fst _ _ ≫ ι at he
  rw [← Category.assoc, ← Category.assoc] at he
  apply pullback.hom_ext
  · exact (cancel_mono ι).mp he
  · exact hs

theorem rel_iff {T : Scheme.{u}} (x y : T ⟶ J) :
    (∃ φ : T ⟶ pullback (ι ≫ f) f, φ ≫ pullback.snd (ι ≫ f) f = x ∧ φ ≫ L.action ι = y) ↔
      ∃ (e : T ⟶ E) (he : e ≫ ι ≫ f = x ≫ f), (L.mul (x ≫ f) ⟨e ≫ ι, he⟩ ⟨x, rfl⟩).1 = y := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    refine ⟨φ ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, Category.assoc], ?_⟩
    rw [comp_action' L ι ((φ ≫ pullback.snd _ _) ≫ f) φ (Category.assoc _ _ _).symm]
    congr 2 <;> exact Subtype.ext (by simp only [Category.assoc])
  · rintro ⟨e, he, rfl⟩
    exact ⟨pt ι e x he, pt_snd ι e x he, comp_action_pt L ι (x ≫ f) e ⟨x, rfl⟩ he he⟩

variable
  (hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∃ e : T ⟶ E, e ≫ ι = (L.one t).1)
  (hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) → ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1)
  (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)

include hE_one hE_mul hE_inv in
theorem equivalence (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ J => ∃ φ : T ⟶ pullback (ι ≫ f) f, φ ≫ pullback.snd (ι ≫ f) f = x ∧ φ ≫ L.action ι = y := by
  simp only [rel_iff L ι]
  refine ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} h₁ h₂ => ?_⟩
  ·
    obtain ⟨e, he⟩ := hE_one (x ≫ f)
    letI := L.pointGroup (x ≫ f)
    have he' : e ≫ ι ≫ f = x ≫ f := by rw [← Category.assoc, he]; exact (L.one (x ≫ f)).2
    refine ⟨e, he', ?_⟩
    have : (⟨e ≫ ι, he'⟩ : SchemeHomOver (x ≫ f) f) = L.one (x ≫ f) := Subtype.ext he
    rw [this, L.one_mul]
  ·
    obtain ⟨e, he, rfl⟩ := h
    letI := L.pointGroup (x ≫ f)
    obtain ⟨e', he'⟩ := hE_inv (x ≫ f) ⟨e ≫ ι, he⟩ ⟨e, rfl⟩
    have hbase : (L.mul (x ≫ f) ⟨e ≫ ι, he⟩ ⟨x, rfl⟩).1 ≫ f = x ≫ f := (L.mul _ _ _).2
    have he'f : e' ≫ ι ≫ f = (L.mul (x ≫ f) ⟨e ≫ ι, he⟩ ⟨x, rfl⟩).1 ≫ f := by
      rw [hbase, ← Category.assoc, he']; exact (L.inv _ _).2
    refine ⟨e', he'f, ?_⟩

    have key : ∀ (t : T ⟶ Spec (CommRingCat.of R)) (ht : t = x ≫ f) (a : SchemeHomOver t f) (b : SchemeHomOver t f)
        (ha : a.1 = (L.inv (x ≫ f) ⟨e ≫ ι, he⟩).1) (hb : b.1 = (L.mul (x ≫ f) ⟨e ≫ ι, he⟩ ⟨x, rfl⟩).1),
        (L.mul t a b).1 = x := by
      intro t ht a b ha hb
      subst ht
      have ha' : a = L.inv (x ≫ f) ⟨e ≫ ι, he⟩ := Subtype.ext ha
      have hb' : b = L.mul (x ≫ f) ⟨e ≫ ι, he⟩ ⟨x, rfl⟩ := Subtype.ext hb
      rw [ha', hb']
      change (((⟨e ≫ ι, he⟩ : SchemeHomOver (x ≫ f) f)⁻¹ * ((⟨e ≫ ι, he⟩ : SchemeHomOver (x ≫ f) f) * ⟨x, rfl⟩)) : SchemeHomOver _ f).1 = x
      rw [inv_mul_cancel_left]
    exact key _ hbase _ _ he' rfl
  ·
    obtain ⟨e₁, he₁, rfl⟩ := h₁
    obtain ⟨e₂, he₂, rfl⟩ := h₂
    letI := L.pointGroup (x ≫ f)
    have hbase : (L.mul (x ≫ f) ⟨e₁ ≫ ι, he₁⟩ ⟨x, rfl⟩).1 ≫ f = x ≫ f := (L.mul _ _ _).2
    have he₂' : e₂ ≫ ι ≫ f = x ≫ f := by rw [he₂, hbase]
    obtain ⟨e, he⟩ := hE_mul (x ≫ f) ⟨e₂ ≫ ι, he₂'⟩ ⟨e₁ ≫ ι, he₁⟩ ⟨e₂, rfl⟩ ⟨e₁, rfl⟩
    have hef : e ≫ ι ≫ f = x ≫ f := by rw [← Category.assoc, he]; exact (L.mul _ _ _).2
    refine ⟨e, hef, ?_⟩
    have hept : (⟨e ≫ ι, hef⟩ : SchemeHomOver (x ≫ f) f) = L.mul (x ≫ f) ⟨e₂ ≫ ι, he₂'⟩ ⟨e₁ ≫ ι, he₁⟩ := Subtype.ext he
    rw [hept]
    have key : ∀ (t : T ⟶ Spec (CommRingCat.of R)) (ht : t = x ≫ f) (a b : SchemeHomOver t f)
        (ha : a.1 = e₂ ≫ ι) (hb : b.1 = (L.mul (x ≫ f) ⟨e₁ ≫ ι, he₁⟩ ⟨x, rfl⟩).1),
        (L.mul t a b).1 = (L.mul (x ≫ f) (L.mul (x ≫ f) ⟨e₂ ≫ ι, he₂'⟩ ⟨e₁ ≫ ι, he₁⟩) ⟨x, rfl⟩).1 := by
      intro t ht a b ha hb
      subst ht
      have ha' : a = ⟨e₂ ≫ ι, he₂'⟩ := Subtype.ext ha
      have hb' : b = L.mul (x ≫ f) ⟨e₁ ≫ ι, he₁⟩ ⟨x, rfl⟩ := Subtype.ext hb
      rw [ha', hb', L.mul_assoc]
    exact (key _ hbase _ _ rfl rfl).symm

end Relation
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

section Orbit

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsFinite (ι ≫ f)]

theorem orbit_subset (hAF : ∀ S : Finset J, ∃ U : J.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) (x : J) :
    ∃ U : J.Opens, IsAffineOpen U ∧ ∀ r : ↑(pullback (ι ≫ f) f), (pullback.snd (ι ≫ f) f) r = x → (L.action ι) r ∈ U := by
  classical
  have hfin : ((pullback.snd (ι ≫ f) f) ⁻¹' {x}).Finite := IsFinite.finite_preimage_singleton _ x
  obtain ⟨U, hU, hmem⟩ := hAF (hfin.image (L.action ι)).toFinset
  refine ⟨U, hU, fun r hr => hmem _ ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨r, hr, rfl⟩

end Orbit
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

end GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

open GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid in
theorem solution
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
    [IsFinite (ι ≫ f)] [Flat (ι ≫ f)] [LocallyOfFinitePresentation (ι ≫ f)]
    (hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      ∃ e : T ⟶ E, e ≫ ι = (L.one t).1)
    (hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) →
        ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1)
    (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)
    (hAF : ∀ S : Finset J, ∃ U : J.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    IsFinite (pullback.snd (ι ≫ f) f) ∧ Flat (pullback.snd (ι ≫ f) f) ∧
      LocallyOfFinitePresentation (pullback.snd (ι ≫ f) f) ∧
    IsFinite (L.action ι) ∧ Flat (L.action ι) ∧ LocallyOfFinitePresentation (L.action ι) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ pullback (ι ≫ f) f),
      a ≫ pullback.snd (ι ≫ f) f = b ≫ pullback.snd (ι ≫ f) f → a ≫ L.action ι = b ≫ L.action ι → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ J =>
      ∃ φ : T ⟶ pullback (ι ≫ f) f, φ ≫ pullback.snd (ι ≫ f) f = x ∧ φ ≫ L.action ι = y) ∧
    (∀ x : J, ∃ U : J.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (ι ≫ f) f), (pullback.snd (ι ≫ f) f) r = x → (L.action ι) r ∈ U) := by
  have h1 : IsFinite (L.action ι) := by rw [action_eq_shear_snd]; infer_instance
  have h2 : Flat (L.action ι) := by rw [action_eq_shear_snd]; infer_instance
  have h3 : LocallyOfFinitePresentation (L.action ι) := by rw [action_eq_shear_snd]; infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance, h1, h2, h3, fun a b hs ht => jointly_mono L ι a b hs ht,
    fun T => equivalence L ι hE_one hE_mul hE_inv T, fun x => orbit_subset L ι hAF x⟩

end S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action (solution)
