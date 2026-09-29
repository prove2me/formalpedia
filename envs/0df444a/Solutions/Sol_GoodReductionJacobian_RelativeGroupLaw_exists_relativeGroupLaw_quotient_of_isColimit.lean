-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_quotient_of_isColimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/aa426adf-d6ac-5b14-b4e9-e3560343b7e5

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource RelativeGroupLaw.action_over"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
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

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid.action_over : L.action ι ≫ f = RelativeGroupLaw.actionSource f ι := (L.mul _ _ _).2

p2m_export "GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid" "action_over"

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
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource RelativeGroupLaw.action_over"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
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
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

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
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

end GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource RelativeGroupLaw.action_over"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
namespace LawDescends
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J)
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)

section Base

theorem snd_f_eq_action_f : pullback.snd (ι ≫ f) f ≫ f = L.action ι ≫ f :=
  (ActionGroupoid.action_over L ι).symm

variable (hcoeq : IsColimit (Cofork.ofπ p w))

noncomputable def base : P ⟶ Spec (CommRingCat.of R) :=
  Cofork.IsColimit.desc hcoeq f (snd_f_eq_action_f L ι)

theorem p_base : p ≫ base L ι p w hcoeq = f := by
  have h := Cofork.IsColimit.π_desc' hcoeq f (snd_f_eq_action_f L ι)
  rwa [Cofork.π_ofπ] at h

end Base
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

section W

variable [IsClosedImmersion ι]

include w in
theorem p_act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (z : SchemeHomOver t f) (he : e ≫ ι ≫ f = t) :
    (L.mul t ⟨e ≫ ι, he⟩ z).1 ≫ p = z.1 ≫ p := by
  have hx : e ≫ ι ≫ f = z.1 ≫ f := by rw [he, z.2]
  rw [← ActionGroupoid.comp_action_pt L ι t e z he hx, Category.assoc, ← w, ← Category.assoc, ActionGroupoid.pt_snd]

end W
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

end GoodReductionJacobian.RelativeGroupLaw.LawDescends
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource RelativeGroupLaw.action_over"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
namespace LawDescends
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Products

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hcoeq : IsColimit (Cofork.ofπ p w))

noncomputable abbrev g := base L ι p w hcoeq

noncomputable def oneP : pullback f f ⟶ pullback f (g L ι p w hcoeq) :=
  pullback.map f f f (g L ι p w hcoeq) (𝟙 J) p (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, p_base])

@[reassoc (attr := simp)] theorem oneP_fst : oneP L ι p w hcoeq ≫ pullback.fst _ _ = pullback.fst f f := by
  rw [oneP, pullback.lift_fst, Category.comp_id]
@[reassoc (attr := simp)] theorem oneP_snd : oneP L ι p w hcoeq ≫ pullback.snd _ _ = pullback.snd f f ≫ p := pullback.lift_snd _ _ _

theorem isPullback_oneP : IsPullback (pullback.snd f f) (oneP L ι p w hcoeq) p (pullback.snd f (g L ι p w hcoeq)) := by
  have outer : IsPullback (oneP L ι p w hcoeq ≫ pullback.fst f (g L ι p w hcoeq)) (pullback.snd f f) f (p ≫ g L ι p w hcoeq) := by
    rw [oneP_fst, p_base]; exact IsPullback.of_hasPullback f f
  exact (IsPullback.of_right outer (oneP_snd L ι p w hcoeq) (IsPullback.of_hasPullback f (g L ι p w hcoeq))).flip

noncomputable def twoP : pullback f (g L ι p w hcoeq) ⟶ pullback (g L ι p w hcoeq) (g L ι p w hcoeq) :=
  pullback.map f (g L ι p w hcoeq) (g L ι p w hcoeq) (g L ι p w hcoeq) p (𝟙 P) (𝟙 _)
    (by rw [Category.comp_id, p_base]) (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)] theorem twoP_fst : twoP L ι p w hcoeq ≫ pullback.fst _ _ = pullback.fst f (g L ι p w hcoeq) ≫ p := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem twoP_snd : twoP L ι p w hcoeq ≫ pullback.snd _ _ = pullback.snd f (g L ι p w hcoeq) := by
  rw [twoP, pullback.lift_snd, Category.comp_id]

theorem isPullback_twoP : IsPullback (pullback.fst f (g L ι p w hcoeq)) (twoP L ι p w hcoeq) p (pullback.fst (g L ι p w hcoeq) (g L ι p w hcoeq)) := by
  have outer : IsPullback (twoP L ι p w hcoeq ≫ pullback.snd (g L ι p w hcoeq) (g L ι p w hcoeq)) (pullback.fst f (g L ι p w hcoeq))
      (g L ι p w hcoeq) (p ≫ g L ι p w hcoeq) := by
    rw [twoP_snd, p_base]; exact (IsPullback.of_hasPullback f (g L ι p w hcoeq)).flip
  exact (IsPullback.of_right outer (twoP_fst L ι p w hcoeq) (IsPullback.of_hasPullback (g L ι p w hcoeq) (g L ι p w hcoeq)).flip).flip

noncomputable def tOne : pullback (pullback.snd f f) (pullback.snd (ι ≫ f) f) ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ L.action ι) (by
    rw [Category.assoc, Category.assoc, RelativeGroupLaw.action_over]
    change _ = pullback.snd _ _ ≫ pullback.snd (ι ≫ f) f ≫ f
    rw [← pullback.condition_assoc, pullback.condition])

@[reassoc (attr := simp)] theorem tOne_fst : tOne L ι ≫ pullback.fst f f = pullback.fst _ _ ≫ pullback.fst f f := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem tOne_snd : tOne L ι ≫ pullback.snd f f = pullback.snd _ _ ≫ L.action ι := pullback.lift_snd _ _ _

include hR in

theorem quotient_oneP :
    ∃ w₁ : pullback.fst (pullback.snd f f) (pullback.snd (ι ≫ f) f) ≫ oneP L ι p w hcoeq = tOne L ι ≫ oneP L ι p w hcoeq,
    IsFinite (oneP L ι p w hcoeq) ∧ Flat (oneP L ι p w hcoeq) ∧ LocallyOfFinitePresentation (oneP L ι p w hcoeq) ∧
      Surjective (oneP L ι p w hcoeq) ∧
      IsPullback (pullback.fst (pullback.snd f f) (pullback.snd (ι ≫ f) f)) (tOne L ι) (oneP L ι p w hcoeq) (oneP L ι p w hcoeq) ∧
      Nonempty (IsColimit (Cofork.ofπ (oneP L ι p w hcoeq) w₁)) := by
  have w₁ : pullback.fst (pullback.snd f f) (pullback.snd (ι ≫ f) f) ≫ oneP L ι p w hcoeq = tOne L ι ≫ oneP L ι p w hcoeq := by
    apply pullback.hom_ext
    · rw [Category.assoc, oneP_fst, Category.assoc, oneP_fst, tOne_fst]
    · rw [Category.assoc, oneP_snd, Category.assoc, oneP_snd, ← Category.assoc (tOne L ι), tOne_snd, Category.assoc, ← w,
        ← Category.assoc, ← Category.assoc, pullback.condition]
  exact ⟨w₁, AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback hR (isPullback_oneP L ι p w hcoeq)
    (IsPullback.of_hasPullback (pullback.snd f f) (pullback.snd (ι ≫ f) f)).flip (tOne_snd L ι).symm w₁⟩

noncomputable def tTwo : pullback (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f) ⟶ pullback f (g L ι p w hcoeq) :=
  pullback.lift (pullback.snd _ _ ≫ L.action ι) (pullback.fst _ _ ≫ pullback.snd f (g L ι p w hcoeq)) (by
    rw [Category.assoc, Category.assoc, RelativeGroupLaw.action_over, ← pullback.condition]
    change pullback.snd _ _ ≫ pullback.snd (ι ≫ f) f ≫ f = _
    rw [← pullback.condition_assoc])

@[reassoc (attr := simp)] theorem tTwo_fst : tTwo L ι p w hcoeq ≫ pullback.fst _ _ = pullback.snd _ _ ≫ L.action ι := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem tTwo_snd : tTwo L ι p w hcoeq ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.snd f (g L ι p w hcoeq) :=
  pullback.lift_snd _ _ _

include hR in

theorem quotient_twoP :
    ∃ w₂ : pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f) ≫ twoP L ι p w hcoeq = tTwo L ι p w hcoeq ≫ twoP L ι p w hcoeq,
    IsFinite (twoP L ι p w hcoeq) ∧ Flat (twoP L ι p w hcoeq) ∧ LocallyOfFinitePresentation (twoP L ι p w hcoeq) ∧
      Surjective (twoP L ι p w hcoeq) ∧
      IsPullback (pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)) (tTwo L ι p w hcoeq)
        (twoP L ι p w hcoeq) (twoP L ι p w hcoeq) ∧
      Nonempty (IsColimit (Cofork.ofπ (twoP L ι p w hcoeq) w₂)) := by
  have w₂ : pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f) ≫ twoP L ι p w hcoeq =
      tTwo L ι p w hcoeq ≫ twoP L ι p w hcoeq := by
    apply pullback.hom_ext
    · rw [Category.assoc, twoP_fst, Category.assoc, twoP_fst, ← Category.assoc (tTwo L ι p w hcoeq), tTwo_fst, Category.assoc, ← w,
        ← Category.assoc, ← Category.assoc, pullback.condition]
    · rw [Category.assoc, twoP_snd, Category.assoc, twoP_snd, tTwo_snd]
  exact ⟨w₂, AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback hR (isPullback_twoP L ι p w hcoeq)
    (IsPullback.of_hasPullback (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)).flip (tTwo_fst L ι p w hcoeq).symm w₂⟩

end Products
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

end GoodReductionJacobian.RelativeGroupLaw.LawDescends
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource RelativeGroupLaw.action_over"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
namespace LawDescends
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Mul

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hcoeq : IsColimit (Cofork.ofπ p w))
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)

noncomputable def mJ : pullback f f ⟶ J :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

theorem mJ_over : mJ L ≫ f = pullback.fst f f ≫ f := (L.mul _ _ _).2

theorem comp_mJ₀ {T : Scheme.{u}} (ψ : T ⟶ pullback f f) :
    ψ ≫ mJ L = (L.mul (ψ ≫ pullback.fst f f ≫ f)
      (GoodReductionJacobian.schemeHomOverComp ψ rfl (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f))
      (GoodReductionJacobian.schemeHomOverComp ψ rfl (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f))).1 := by
  rw [← L.mul_natural _ _ ψ rfl, GoodReductionJacobian.schemeHomOverComp_coe]; rfl

theorem comp_mJ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : T ⟶ pullback f f) (ht : ψ ≫ pullback.fst f f ≫ f = t) :
    ψ ≫ mJ L = (L.mul t ⟨ψ ≫ pullback.fst f f, ht⟩ ⟨ψ ≫ pullback.snd f f, by rw [← ht, Category.assoc, pullback.condition]⟩).1 := by
  subst ht
  rw [comp_mJ₀]
  rfl

include hcomm in

theorem mul_act_comm {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x e y : SchemeHomOver t f) :
    L.mul t x (L.mul t e y) = L.mul t e (L.mul t x y) := by
  rw [← L.mul_assoc, hcomm t x e, L.mul_assoc]

include w hcomm in

theorem cond_one : pullback.fst (pullback.snd f f) (pullback.snd (ι ≫ f) f) ≫ (mJ L ≫ p) = tOne L ι ≫ (mJ L ≫ p) := by

  let t : pullback (pullback.snd f f) (pullback.snd (ι ≫ f) f) ⟶ Spec (CommRingCat.of R) :=
    pullback.fst _ _ ≫ pullback.fst f f ≫ f
  have ht₂ : tOne L ι ≫ pullback.fst f f ≫ f = t := by rw [← Category.assoc, tOne_fst, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, comp_mJ L t _ rfl, comp_mJ L t _ ht₂]

  have hcond : pullback.fst (pullback.snd f f) (pullback.snd (ι ≫ f) f) ≫ pullback.snd f f =
      pullback.snd _ _ ≫ pullback.snd (ι ≫ f) f := pullback.condition
  have he : (pullback.snd (pullback.snd f f) (pullback.snd (ι ≫ f) f) ≫ pullback.fst (ι ≫ f) f) ≫ ι ≫ f = t := by
    rw [Category.assoc, pullback.condition, ← pullback.condition_assoc]
    show pullback.fst _ _ ≫ pullback.snd f f ≫ f = pullback.fst _ _ ≫ pullback.fst f f ≫ f
    rw [← pullback.condition]
  have hX : (⟨tOne L ι ≫ pullback.fst f f, ht₂⟩ : SchemeHomOver t f) = ⟨pullback.fst _ _ ≫ pullback.fst f f, rfl⟩ :=
    Subtype.ext (tOne_fst L ι)
  have hY : (⟨tOne L ι ≫ pullback.snd f f, by rw [← ht₂, Category.assoc, pullback.condition]⟩ : SchemeHomOver t f) =
      L.mul t ⟨(pullback.snd _ _ ≫ pullback.fst (ι ≫ f) f) ≫ ι, he⟩
        ⟨pullback.fst _ _ ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩ := by
    apply Subtype.ext
    change tOne L ι ≫ pullback.snd f f = _
    rw [tOne_snd, ActionGroupoid.comp_action' L ι t _ (by
      change pullback.snd _ _ ≫ pullback.snd (ι ≫ f) f ≫ f = t
      rw [← pullback.condition_assoc]; change pullback.fst _ _ ≫ pullback.snd f f ≫ f = t; rw [← pullback.condition])]
    congr 2
    all_goals first
      | rfl
      | exact Subtype.ext hcond.symm
      | exact Subtype.ext (Category.assoc _ _ _).symm
      | exact Subtype.ext (Category.assoc _ _ _)
  rw [hX, hY, mul_act_comm L hcomm, p_act L ι p w t _ _ he]

noncomputable def mOne : pullback f (g L ι p w hcoeq) ⟶ P :=
  Cofork.IsColimit.desc (quotient_oneP L ι p w hR hcoeq).choose_spec.2.2.2.2.2.some (mJ L ≫ p) (cond_one L ι p w hcomm)

theorem oneP_mOne : oneP L ι p w hcoeq ≫ mOne L ι p w hR hcoeq hcomm = mJ L ≫ p := by
  have h := Cofork.IsColimit.π_desc' (quotient_oneP L ι p w hR hcoeq).choose_spec.2.2.2.2.2.some (mJ L ≫ p) (cond_one L ι p w hcomm)
  rwa [Cofork.π_ofπ] at h

noncomputable abbrev Rt := pullback (pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)) (oneP L ι p w hcoeq)

include hR in
theorem epi_c : Epi (pullback.fst (pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)) (oneP L ι p w hcoeq)) := by
  obtain ⟨_, _, hflat, _, hsurj, _, _⟩ := quotient_oneP L ι p w hR hcoeq
  exact Flat.epi_of_flat_of_surjective _

theorem src_eq : pullback.fst (pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)) (oneP L ι p w hcoeq) ≫
      pullback.snd _ _ ≫ RelativeGroupLaw.actionSource f ι =
    pullback.snd (pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)) (oneP L ι p w hcoeq) ≫ pullback.fst f f ≫ f := by
  dsimp only [RelativeGroupLaw.actionSource]
  rw [← pullback.condition_assoc, pullback.condition_assoc, oneP_fst_assoc]

theorem x_eq : pullback.fst (pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)) (oneP L ι p w hcoeq) ≫
      pullback.snd _ _ ≫ pullback.snd (ι ≫ f) f =
    pullback.snd (pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)) (oneP L ι p w hcoeq) ≫ pullback.fst f f := by
  rw [← @pullback.condition _ _ _ _ _ (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f) _, pullback.condition_assoc, oneP_fst]

noncomputable def ψt : Rt L ι p w hcoeq ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _ ≫ L.action ι) (pullback.snd _ _ ≫ pullback.snd f f) (by
    rw [Category.assoc, Category.assoc, RelativeGroupLaw.action_over, src_eq, Category.assoc, pullback.condition])

@[reassoc]
theorem ψt_oneP : ψt L ι p w hcoeq ≫ oneP L ι p w hcoeq = pullback.fst _ _ ≫ tTwo L ι p w hcoeq := by
  apply pullback.hom_ext
  · rw [Category.assoc, oneP_fst, Category.assoc, tTwo_fst, ψt, pullback.lift_fst]
  · rw [Category.assoc, oneP_snd, Category.assoc, tTwo_snd, pullback.condition_assoc, oneP_snd, ψt, pullback.lift_snd_assoc, Category.assoc]

include hcomm in
theorem cond_two :
    pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f) ≫ mOne L ι p w hR hcoeq hcomm =
      tTwo L ι p w hcoeq ≫ mOne L ι p w hR hcoeq hcomm := by
  haveI := epi_c L ι p w hR hcoeq
  rw [← cancel_epi (pullback.fst (pullback.fst (pullback.fst f (g L ι p w hcoeq)) (pullback.snd (ι ≫ f) f)) (oneP L ι p w hcoeq))]
  rw [pullback.condition_assoc, oneP_mOne, ← ψt_oneP_assoc, oneP_mOne]

  let t : Rt L ι p w hcoeq ⟶ Spec (CommRingCat.of R) := pullback.snd _ _ ≫ pullback.fst f f ≫ f
  have hψ : ψt L ι p w hcoeq ≫ pullback.fst f f ≫ f = t := by
    rw [ψt, pullback.lift_fst_assoc, Category.assoc, Category.assoc, RelativeGroupLaw.action_over, src_eq]
  rw [← Category.assoc, ← Category.assoc (ψt L ι p w hcoeq), comp_mJ L t _ rfl, comp_mJ L t _ hψ]
  have he : (pullback.fst _ _ ≫ pullback.snd _ _ ≫ pullback.fst (ι ≫ f) f) ≫ ι ≫ f = t := by
    rw [Category.assoc, Category.assoc, pullback.condition]
    show _ = pullback.snd _ _ ≫ pullback.fst f f ≫ f
    rw [← src_eq]
  have hX : (⟨ψt L ι p w hcoeq ≫ pullback.fst f f, hψ⟩ : SchemeHomOver t f) =
      L.mul t ⟨(pullback.fst _ _ ≫ pullback.snd _ _ ≫ pullback.fst (ι ≫ f) f) ≫ ι, he⟩ ⟨pullback.snd _ _ ≫ pullback.fst f f, rfl⟩ := by
    apply Subtype.ext
    change ψt L ι p w hcoeq ≫ pullback.fst f f = _
    rw [ψt, pullback.lift_fst, ← Category.assoc, ActionGroupoid.comp_action' L ι t _ (by rw [Category.assoc, src_eq])]
    congr 2
    all_goals apply Subtype.ext
    all_goals first
      | (show (pullback.fst _ _ ≫ pullback.snd _ _) ≫ pullback.snd (ι ≫ f) f = pullback.snd _ _ ≫ pullback.fst f f
         rw [Category.assoc, x_eq])
      | simp only [Category.assoc]
  have hY : (⟨ψt L ι p w hcoeq ≫ pullback.snd f f, by rw [← hψ, Category.assoc, pullback.condition]⟩ : SchemeHomOver t f) =
      ⟨pullback.snd _ _ ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩ :=
    Subtype.ext (by change ψt L ι p w hcoeq ≫ pullback.snd f f = _; rw [ψt, pullback.lift_snd])
  rw [hX, hY, L.mul_assoc, p_act L ι p w t _ _ he]

noncomputable def mP : pullback (g L ι p w hcoeq) (g L ι p w hcoeq) ⟶ P :=
  Cofork.IsColimit.desc (quotient_twoP L ι p w hR hcoeq).choose_spec.2.2.2.2.2.some (mOne L ι p w hR hcoeq hcomm)
    (cond_two L ι p w hR hcoeq hcomm)

theorem twoP_mP : twoP L ι p w hcoeq ≫ mP L ι p w hR hcoeq hcomm = mOne L ι p w hR hcoeq hcomm := by
  have h := Cofork.IsColimit.π_desc' (quotient_twoP L ι p w hR hcoeq).choose_spec.2.2.2.2.2.some (mOne L ι p w hR hcoeq hcomm)
    (cond_two L ι p w hR hcoeq hcomm)
  rwa [Cofork.π_ofπ] at h

theorem pp_mP : (oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq) ≫ mP L ι p w hR hcoeq hcomm = mJ L ≫ p := by
  rw [Category.assoc, twoP_mP, oneP_mOne]

end Mul
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

end GoodReductionJacobian.RelativeGroupLaw.LawDescends
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource RelativeGroupLaw.action_over"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
namespace LawDescends
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section InvOne

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hcoeq : IsColimit (Cofork.ofπ p w))
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
  (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)

noncomputable def iJ : J ⟶ J := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).1

theorem iJ_over : iJ L ≫ f = f := (L.inv f _).2

theorem comp_iJ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) : x.1 ≫ iJ L = (L.inv t x).1 := by
  obtain ⟨x, rfl⟩ := x
  have h := congrArg Subtype.val (ActionGroupoid.inv_natural L f (x ≫ f) x rfl ⟨𝟙 J, Category.id_comp f⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [iJ, h]
  have hx : GoodReductionJacobian.schemeHomOverComp x rfl (⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f) =
      (⟨x, rfl⟩ : SchemeHomOver (x ≫ f) f) := Subtype.ext (Category.comp_id x)
  rw [hx]

noncomputable def eJ : Spec (CommRingCat.of R) ⟶ J := (L.one (𝟙 _)).1

theorem eJ_over : eJ L ≫ f = 𝟙 _ := (L.one _).2

theorem comp_eJ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : t ≫ eJ L = (L.one t).1 := by
  have h := congrArg Subtype.val (ActionGroupoid.one_natural L (𝟙 _) t t (Category.comp_id t))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [eJ, h]

include w hcomm hE_inv in

theorem cond_inv : pullback.snd (ι ≫ f) f ≫ (iJ L ≫ p) = L.action ι ≫ (iJ L ≫ p) := by
  let t := RelativeGroupLaw.actionSource f ι
  rw [← Category.assoc, ← Category.assoc]
  show ((L.actionSndPoint ι).1 ≫ iJ L) ≫ p = ((L.mul t (L.actionFstPoint ι) (L.actionSndPoint ι)).1 ≫ iJ L) ≫ p
  rw [comp_iJ L t (L.actionSndPoint ι), comp_iJ L t (L.mul t (L.actionFstPoint ι) (L.actionSndPoint ι))]
  letI := L.pointGroup t
  obtain ⟨e', he'⟩ := hE_inv t (L.actionFstPoint ι) ⟨pullback.fst _ _, rfl⟩
  have he'f : e' ≫ ι ≫ f = t := by rw [← Category.assoc, he']; exact (L.inv t _).2
  have hpt : (⟨e' ≫ ι, he'f⟩ : SchemeHomOver t f) = L.inv t (L.actionFstPoint ι) := Subtype.ext he'
  have key : L.inv t (L.mul t (L.actionFstPoint ι) (L.actionSndPoint ι)) = L.mul t ⟨e' ≫ ι, he'f⟩ (L.inv t (L.actionSndPoint ι)) := by
    rw [hpt, hcomm t (L.actionFstPoint ι)]
    exact mul_inv_rev (L.actionSndPoint ι) (L.actionFstPoint ι)
  rw [key, p_act L ι p w t e' _ he'f]

noncomputable def iP : P ⟶ P := Cofork.IsColimit.desc hcoeq (iJ L ≫ p) (cond_inv L ι p w hcomm hE_inv)

theorem p_iP : p ≫ iP L ι p w hcoeq hcomm hE_inv = iJ L ≫ p := by
  have h := Cofork.IsColimit.π_desc' hcoeq (iJ L ≫ p) (cond_inv L ι p w hcomm hE_inv)
  rwa [Cofork.π_ofπ] at h

noncomputable def eP : Spec (CommRingCat.of R) ⟶ P := eJ L ≫ p

theorem eP_over : eP L p ≫ g L ι p w hcoeq = 𝟙 _ := by rw [eP, Category.assoc, p_base, eJ_over]

theorem epi_p : Epi p := Flat.epi_of_flat_of_surjective p

theorem iP_over : iP L ι p w hcoeq hcomm hE_inv ≫ g L ι p w hcoeq = g L ι p w hcoeq := by
  haveI := epi_p p
  rw [← cancel_epi p, ← Category.assoc, p_iP, Category.assoc, p_base, iJ_over]

include hR in
theorem epi_pp : Epi (oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq) := by
  obtain ⟨_, _, h1, _, h2, _, _⟩ := quotient_oneP L ι p w hR hcoeq
  obtain ⟨_, _, h3, _, h4, _, _⟩ := quotient_twoP L ι p w hR hcoeq
  haveI := Flat.epi_of_flat_of_surjective (oneP L ι p w hcoeq)
  haveI := Flat.epi_of_flat_of_surjective (twoP L ι p w hcoeq)
  exact epi_comp _ _

theorem pp_fst : (oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq) ≫ pullback.fst _ _ = pullback.fst f f ≫ p := by
  rw [Category.assoc, twoP_fst, oneP_fst_assoc]

theorem pp_snd : (oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq) ≫ pullback.snd _ _ = pullback.snd f f ≫ p := by
  rw [Category.assoc, twoP_snd, oneP_snd]

theorem mP_over : mP L ι p w hR hcoeq hcomm ≫ g L ι p w hcoeq = pullback.fst _ _ ≫ g L ι p w hcoeq := by
  haveI := epi_pp L ι p w hR hcoeq
  rw [← cancel_epi (oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq), ← Category.assoc, pp_mP, Category.assoc, p_base, mJ_over,
    ← Category.assoc, pp_fst, Category.assoc, p_base]

theorem over_p {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f) : (x.1 ≫ p) ≫ g L ι p w hcoeq = t := by
  rw [Category.assoc, p_base, x.2]

theorem over_p' {T : Scheme.{u}} (a : T ⟶ J) : (a ≫ p) ≫ g L ι p w hcoeq = a ≫ f := by rw [Category.assoc, p_base]

theorem over_eP {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : (t ≫ eP L p) ≫ g L ι p w hcoeq = t := by
  rw [Category.assoc, eP_over, Category.comp_id]

theorem over_g_eP : (g L ι p w hcoeq ≫ eP L p) ≫ g L ι p w hcoeq = 𝟙 P ≫ g L ι p w hcoeq := by
  rw [Category.assoc, eP_over, Category.comp_id, Category.id_comp]

theorem over_iP : iP L ι p w hcoeq hcomm hE_inv ≫ g L ι p w hcoeq = 𝟙 P ≫ g L ι p w hcoeq := by rw [iP_over, Category.id_comp]

end InvOne
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

end GoodReductionJacobian.RelativeGroupLaw.LawDescends
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource RelativeGroupLaw.action_over"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
namespace LawDescends
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Identities

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hcoeq : IsColimit (Cofork.ofπ p w))
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
  (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)

noncomputable abbrev pp := oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq

theorem lift_pp {T : Scheme.{u}} (a b : T ⟶ J) (h : a ≫ f = b ≫ f) :
    pullback.lift a b h ≫ pp L ι p w hcoeq =
      pullback.lift (a ≫ p) (b ≫ p) ((over_p' L ι p w hcoeq a).trans (h.trans (over_p' L ι p w hcoeq b).symm)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pp_fst, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, pp_snd, pullback.lift_snd_assoc, pullback.lift_snd]

theorem lift_p_mP {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    pullback.lift (x.1 ≫ p) (y.1 ≫ p) ((over_p L ι p w hcoeq x).trans (over_p L ι p w hcoeq y).symm) ≫ mP L ι p w hR hcoeq hcomm =
      (L.mul t x y).1 ≫ p := by
  rw [← lift_pp L ι p w hcoeq x.1 y.1 (x.2.trans y.2.symm), Category.assoc, pp_mP, ← Category.assoc,
    comp_mJ L t _ (by rw [pullback.lift_fst_assoc]; exact x.2)]
  congr 3 <;> exact Subtype.ext (by simp only [pullback.lift_fst, pullback.lift_snd])

theorem p_iP_pt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    x.1 ≫ p ≫ iP L ι p w hcoeq hcomm hE_inv = (L.inv t x).1 ≫ p := by
  rw [p_iP, ← Category.assoc, comp_iJ]

theorem mP_swap : pullback.lift (pullback.snd _ _) (pullback.fst _ _) pullback.condition.symm ≫ mP L ι p w hR hcoeq hcomm =
    mP L ι p w hR hcoeq hcomm := by
  haveI := epi_pp L ι p w hR hcoeq
  rw [← cancel_epi (oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq)]
  have hsw : (oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq) ≫ pullback.lift (pullback.snd _ _) (pullback.fst _ _) pullback.condition.symm =
      pullback.lift (pullback.snd f f ≫ p) (pullback.fst f f ≫ p)
        ((over_p' L ι p w hcoeq _).trans (pullback.condition.symm.trans (over_p' L ι p w hcoeq _).symm)) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]; exact pp_snd L ι p w hcoeq
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]; exact pp_fst L ι p w hcoeq
  rw [← Category.assoc, hsw]
  change _ = pp L ι p w hcoeq ≫ _
  rw [pp_mP]
  have h := lift_p_mP L ι p w hR hcoeq hcomm (pullback.fst f f ≫ f) ⟨pullback.snd f f, pullback.condition.symm⟩ ⟨pullback.fst f f, rfl⟩
  rw [h, hcomm]
  rfl

theorem one_mul_id : pullback.lift (g L ι p w hcoeq ≫ eP L p) (𝟙 P) (over_g_eP L ι p w hcoeq) ≫ mP L ι p w hR hcoeq hcomm = 𝟙 P := by
  haveI := epi_p p
  rw [← cancel_epi p, Category.comp_id p, ← Category.assoc]
  have h1 : p ≫ pullback.lift (g L ι p w hcoeq ≫ eP L p) (𝟙 P) (over_g_eP L ι p w hcoeq) =
      pullback.lift ((L.one f).1 ≫ p) ((⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ p)
        ((over_p L ι p w hcoeq _).trans (over_p L ι p w hcoeq _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, p_base, eP, ← Category.assoc, comp_eJ]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
  rw [h1, lift_p_mP L ι p w hR hcoeq hcomm f (L.one f) ⟨𝟙 J, Category.id_comp f⟩, L.one_mul]
  exact Category.id_comp _

theorem mul_one_id : pullback.lift (𝟙 P) (g L ι p w hcoeq ≫ eP L p) (over_g_eP L ι p w hcoeq).symm ≫ mP L ι p w hR hcoeq hcomm = 𝟙 P := by
  haveI := epi_p p
  rw [← cancel_epi p, Category.comp_id p, ← Category.assoc]
  have h1 : p ≫ pullback.lift (𝟙 P) (g L ι p w hcoeq ≫ eP L p) (over_g_eP L ι p w hcoeq).symm =
      pullback.lift ((⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ p) ((L.one f).1 ≫ p)
        ((over_p L ι p w hcoeq _).trans (over_p L ι p w hcoeq _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, p_base, eP, ← Category.assoc, comp_eJ]
  rw [h1, lift_p_mP L ι p w hR hcoeq hcomm f ⟨𝟙 J, Category.id_comp f⟩ (L.one f), L.mul_one]
  exact Category.id_comp _

theorem inv_mul_id : pullback.lift (iP L ι p w hcoeq hcomm hE_inv) (𝟙 P) (over_iP L ι p w hcoeq hcomm hE_inv) ≫ mP L ι p w hR hcoeq hcomm =
    g L ι p w hcoeq ≫ eP L p := by
  haveI := epi_p p
  rw [← cancel_epi p, ← Category.assoc, ← Category.assoc, p_base]
  have h1 : p ≫ pullback.lift (iP L ι p w hcoeq hcomm hE_inv) (𝟙 P) (over_iP L ι p w hcoeq hcomm hE_inv) =
      pullback.lift ((L.inv f ⟨𝟙 J, Category.id_comp f⟩).1 ≫ p) ((⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ p)
        ((over_p L ι p w hcoeq _).trans (over_p L ι p w hcoeq _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, p_iP, iJ]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
  rw [h1, lift_p_mP L ι p w hR hcoeq hcomm f (L.inv f ⟨𝟙 J, Category.id_comp f⟩) ⟨𝟙 J, Category.id_comp f⟩, L.inv_mul_cancel, eP,
    ← Category.assoc, comp_eJ]

end Identities
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

end GoodReductionJacobian.RelativeGroupLaw.LawDescends
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource RelativeGroupLaw.action_over"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_over"
namespace LawDescends
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Assoc

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hcoeq : IsColimit (Cofork.ofπ p w))
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)

noncomputable def α3 : pullback (pullback.fst (g L ι p w hcoeq) (g L ι p w hcoeq) ≫ g L ι p w hcoeq) (g L ι p w hcoeq) ⟶ P :=
  pullback.lift (pullback.fst _ _ ≫ mP L ι p w hR hcoeq hcomm) (pullback.snd _ _)
    (by rw [Category.assoc, mP_over]; exact pullback.condition) ≫ mP L ι p w hR hcoeq hcomm

noncomputable def β3 : pullback (pullback.fst (g L ι p w hcoeq) (g L ι p w hcoeq) ≫ g L ι p w hcoeq) (g L ι p w hcoeq) ⟶ P :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
      (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition).symm.trans pullback.condition) ≫
      mP L ι p w hR hcoeq hcomm)
    (by rw [Category.assoc, Category.assoc, mP_over, pullback.lift_fst_assoc]; exact congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition) ≫
  mP L ι p w hR hcoeq hcomm

noncomputable def q3 : pullback (pullback.fst f f ≫ f) f ⟶ pullback (pullback.fst (g L ι p w hcoeq) (g L ι p w hcoeq) ≫ g L ι p w hcoeq) (g L ι p w hcoeq) :=
  pullback.map _ _ _ _ (pp L ι p w hcoeq) p (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc, pp_fst, Category.assoc, p_base]) (by rw [Category.comp_id, p_base])

include hR in
theorem epi_q3 : Epi (q3 L ι p w hcoeq) := by
  obtain ⟨_, _, h1, _, h2, _, _⟩ := quotient_oneP L ι p w hR hcoeq
  obtain ⟨_, _, h3, _, h4, _, _⟩ := quotient_twoP L ι p w hR hcoeq
  have hflat : Flat (pp L ι p w hcoeq) := inferInstance
  have hsurj : Surjective (pp L ι p w hcoeq) := inferInstance
  have e₁ : pullback.fst f f ≫ f = pp L ι p w hcoeq ≫ pullback.fst (g L ι p w hcoeq) (g L ι p w hcoeq) ≫ g L ι p w hcoeq := by
    rw [← Category.assoc, pp_fst, Category.assoc, p_base]
  have e₂ : f = p ≫ g L ι p w hcoeq := (p_base L ι p w hcoeq).symm
  haveI : Flat (q3 L ι p w hcoeq) := MorphismProperty.pullbackMap (P := @Flat) hflat (inferInstance : Flat p) e₁ e₂
  haveI : Surjective (q3 L ι p w hcoeq) := MorphismProperty.pullbackMap (P := @Surjective) hsurj (inferInstance : Surjective p) e₁ e₂
  exact Flat.epi_of_flat_of_surjective _

@[reassoc] theorem q3_fst : q3 L ι p w hcoeq ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pp L ι p w hcoeq := pullback.lift_fst _ _ _
@[reassoc] theorem q3_snd : q3 L ι p w hcoeq ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := pullback.lift_snd _ _ _

theorem pp_mP' : oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq ≫ mP L ι p w hR hcoeq hcomm = mJ L ≫ p := by
  rw [← Category.assoc]; exact pp_mP L ι p w hR hcoeq hcomm
theorem pp_fst' : oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq ≫ pullback.fst _ _ = pullback.fst f f ≫ p := by
  rw [← Category.assoc]; exact pp_fst L ι p w hcoeq
theorem pp_snd' : oneP L ι p w hcoeq ≫ twoP L ι p w hcoeq ≫ pullback.snd _ _ = pullback.snd f f ≫ p := by
  rw [← Category.assoc]; exact pp_snd L ι p w hcoeq

noncomputable abbrev t3 : pullback (pullback.fst f f ≫ f) f ⟶ Spec (CommRingCat.of R) := pullback.fst _ _ ≫ pullback.fst f f ≫ f

noncomputable abbrev X3 : SchemeHomOver (t3 (f := f)) f := ⟨pullback.fst _ _ ≫ pullback.fst f f, rfl⟩
noncomputable abbrev Y3 : SchemeHomOver (t3 (f := f)) f :=
  ⟨pullback.fst _ _ ≫ pullback.snd f f, by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition).symm⟩
noncomputable abbrev Z3 : SchemeHomOver (t3 (f := f)) f := ⟨pullback.snd _ _, pullback.condition.symm⟩

include hcomm in
theorem q3_α3 : q3 L ι p w hcoeq ≫ α3 L ι p w hR hcoeq hcomm = (L.mul t3 (L.mul t3 X3 Y3) Z3).1 ≫ p := by
  have hin : q3 L ι p w hcoeq ≫ pullback.lift (pullback.fst _ _ ≫ mP L ι p w hR hcoeq hcomm) (pullback.snd _ _)
        (by rw [Category.assoc, mP_over]; exact pullback.condition) =
      pullback.lift ((L.mul t3 X3 Y3).1 ≫ p) ((Z3 (f := f)).1 ≫ p) ((over_p L ι p w hcoeq _).trans (over_p L ι p w hcoeq _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc, pp_mP', ← Category.assoc,
        comp_mJ L t3 _ rfl]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, q3_snd]
  rw [α3, ← Category.assoc, hin, lift_p_mP]

include hcomm in
theorem q3_β3 : q3 L ι p w hcoeq ≫ β3 L ι p w hR hcoeq hcomm = (L.mul t3 X3 (L.mul t3 Y3 Z3)).1 ≫ p := by
  have hin : q3 L ι p w hcoeq ≫ pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
      (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
        (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition).symm.trans pullback.condition) ≫
        mP L ι p w hR hcoeq hcomm)
      (by rw [Category.assoc, Category.assoc, mP_over, pullback.lift_fst_assoc]; exact congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition) =
      pullback.lift ((X3 (f := f)).1 ≫ p) ((L.mul t3 Y3 Z3).1 ≫ p) ((over_p L ι p w hcoeq _).trans (over_p L ι p w hcoeq _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc, pp_fst', Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]
      have h2 : q3 L ι p w hcoeq ≫ pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
            (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition).symm.trans pullback.condition) =
          pullback.lift ((Y3 (f := f)).1 ≫ p) ((Z3 (f := f)).1 ≫ p) ((over_p L ι p w hcoeq _).trans (over_p L ι p w hcoeq _).symm) := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc, pp_snd', Category.assoc]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, q3_snd]
      rw [h2, lift_p_mP]
  rw [β3, ← Category.assoc, hin, lift_p_mP]

include hcomm in
theorem α3_eq_β3 : α3 L ι p w hR hcoeq hcomm = β3 L ι p w hR hcoeq hcomm := by
  haveI := epi_q3 L ι p w hR hcoeq
  rw [← cancel_epi (q3 L ι p w hcoeq), q3_α3, q3_β3, L.mul_assoc]

end Assoc
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

section Law

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hcoeq : IsColimit (Cofork.ofπ p w))
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
  (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)

noncomputable abbrev pr2 {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (u v : SchemeHomOver t (g L ι p w hcoeq)) :
    T ⟶ pullback (g L ι p w hcoeq) (g L ι p w hcoeq) :=
  pullback.lift u.1 v.1 (u.2.trans v.2.symm)

noncomputable def lawP : RelativeGroupLaw R (g L ι p w hcoeq) where
  mul t u v := ⟨pr2 L ι p w hcoeq u v ≫ mP L ι p w hR hcoeq hcomm, by rw [Category.assoc, mP_over L ι p w hR hcoeq hcomm, pullback.lift_fst_assoc]; exact u.2⟩
  one t := ⟨t ≫ eP L p, over_eP L ι p w hcoeq t⟩
  inv t u := ⟨u.1 ≫ iP L ι p w hcoeq hcomm hE_inv, by rw [Category.assoc, iP_over L ι p w hcoeq hcomm hE_inv]; exact u.2⟩
  mul_assoc t u v x := by
    apply Subtype.ext
    have h3 : pullback.lift (pr2 L ι p w hcoeq u v) x.1 (by rw [pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ α3 L ι p w hR hcoeq hcomm =
        pullback.lift (pr2 L ι p w hcoeq u v) x.1 (by rw [pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ β3 L ι p w hR hcoeq hcomm := by
      rw [α3_eq_β3]
    have hl : pullback.lift (pr2 L ι p w hcoeq u v) x.1 (by rw [pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ α3 L ι p w hR hcoeq hcomm =
        pullback.lift (pr2 L ι p w hcoeq u v ≫ mP L ι p w hR hcoeq hcomm) x.1
          (by rw [Category.assoc, mP_over L ι p w hR hcoeq hcomm, pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ mP L ι p w hR hcoeq hcomm := by
      rw [α3, ← Category.assoc]; congr 1
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    have hr : pullback.lift (pr2 L ι p w hcoeq u v) x.1 (by rw [pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ β3 L ι p w hR hcoeq hcomm =
        pullback.lift u.1 (pullback.lift v.1 x.1 (v.2.trans x.2.symm) ≫ mP L ι p w hR hcoeq hcomm)
          (by rw [Category.assoc, mP_over L ι p w hR hcoeq hcomm, pullback.lift_fst_assoc]; exact u.2.trans v.2.symm) ≫ mP L ι p w hR hcoeq hcomm := by
      rw [β3, ← Category.assoc]; congr 1
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]; congr 1
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    change pullback.lift (pr2 L ι p w hcoeq u v ≫ mP L ι p w hR hcoeq hcomm) x.1 _ ≫ mP L ι p w hR hcoeq hcomm =
      pullback.lift u.1 (pullback.lift v.1 x.1 _ ≫ mP L ι p w hR hcoeq hcomm) _ ≫ mP L ι p w hR hcoeq hcomm
    rw [← hl, ← hr, h3]
  one_mul t u := by
    apply Subtype.ext
    change pullback.lift (t ≫ eP L p) u.1 _ ≫ mP L ι p w hR hcoeq hcomm = u.1
    have h : pullback.lift (t ≫ eP L p) u.1 ((over_eP L ι p w hcoeq t).trans u.2.symm) =
        u.1 ≫ pullback.lift (g L ι p w hcoeq ≫ eP L p) (𝟙 P) (over_g_eP L ι p w hcoeq) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, u.2]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h, Category.assoc, one_mul_id, Category.comp_id]
  mul_one t u := by
    apply Subtype.ext
    change pullback.lift u.1 (t ≫ eP L p) _ ≫ mP L ι p w hR hcoeq hcomm = u.1
    have h : pullback.lift u.1 (t ≫ eP L p) (u.2.trans (over_eP L ι p w hcoeq t).symm) =
        u.1 ≫ pullback.lift (𝟙 P) (g L ι p w hcoeq ≫ eP L p) (over_g_eP L ι p w hcoeq).symm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, u.2]
    rw [h, Category.assoc, mul_one_id, Category.comp_id]
  inv_mul_cancel t u := by
    apply Subtype.ext
    change pullback.lift (u.1 ≫ iP L ι p w hcoeq hcomm hE_inv) u.1 _ ≫ mP L ι p w hR hcoeq hcomm = t ≫ eP L p
    have h : pullback.lift (u.1 ≫ iP L ι p w hcoeq hcomm hE_inv) u.1 (by rw [Category.assoc, iP_over L ι p w hcoeq hcomm hE_inv]) =
        u.1 ≫ pullback.lift (iP L ι p w hcoeq hcomm hE_inv) (𝟙 P) (over_iP L ι p w hcoeq hcomm hE_inv) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h, Category.assoc, inv_mul_id, ← Category.assoc, u.2]
  mul_natural t t' ψ hψ u v := by
    apply Subtype.ext
    change ψ ≫ pullback.lift u.1 v.1 _ ≫ mP L ι p w hR hcoeq hcomm = pullback.lift (ψ ≫ u.1) (ψ ≫ v.1) _ ≫ mP L ι p w hR hcoeq hcomm
    rw [← Category.assoc]; congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

theorem lawP_mul_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t (g L ι p w hcoeq)) :
    ((lawP L ι p w hR hcoeq hcomm hE_inv).mul t u v).1 = pr2 L ι p w hcoeq u v ≫ mP L ι p w hR hcoeq hcomm := rfl

theorem lawP_one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : ((lawP L ι p w hR hcoeq hcomm hE_inv).one t).1 = t ≫ eP L p := rfl

theorem hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, p_base, (L.mul t x y).2]⟩ : SchemeHomOver t (g L ι p w hcoeq)) =
      (lawP L ι p w hR hcoeq hcomm hE_inv).mul t ⟨x.1 ≫ p, by rw [Category.assoc, p_base, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, p_base, y.2]⟩ := by
  apply Subtype.ext
  rw [lawP_mul_coe]
  exact (lift_p_mP L ι p w hR hcoeq hcomm t x y).symm

theorem comm {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t (g L ι p w hcoeq)) :
    (lawP L ι p w hR hcoeq hcomm hE_inv).mul t u v = (lawP L ι p w hR hcoeq hcomm hE_inv).mul t v u := by
  apply Subtype.ext
  rw [lawP_mul_coe, lawP_mul_coe]
  conv_rhs => rw [← mP_swap L ι p w hR hcoeq hcomm, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · show pullback.lift u.1 v.1 _ ≫ pullback.fst _ _ = (pullback.lift v.1 u.1 _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
    rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_snd]
  · show pullback.lift u.1 v.1 _ ≫ pullback.snd _ _ = (pullback.lift v.1 u.1 _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ _
    rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_fst]

include w in

theorem ker {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (⟨x.1 ≫ p, by rw [Category.assoc, p_base, x.2]⟩ : SchemeHomOver t (g L ι p w hcoeq)) = (lawP L ι p w hR hcoeq hcomm hE_inv).one t ↔
      ∃ e : T ⟶ E, e ≫ ι = x.1 := by
  constructor
  · intro h
    have h' : x.1 ≫ p = (L.one t).1 ≫ p := by
      have := congrArg Subtype.val h
      rw [lawP_one_coe, eP] at this
      have e2 : (t ≫ eJ L) ≫ p = (L.one t).1 ≫ p := by rw [comp_eJ]
      exact (this.trans (Category.assoc _ _ _).symm).trans e2

    let φ := hR.lift (L.one t).1 x.1 h'.symm
    have hφs : φ ≫ pullback.snd (ι ≫ f) f = (L.one t).1 := hR.lift_fst _ _ _
    have hφt : φ ≫ L.action ι = x.1 := hR.lift_snd _ _ _
    have hbase : φ ≫ RelativeGroupLaw.actionSource f ι = t := by
      show φ ≫ (pullback.snd _ _ ≫ f) = t
      rw [← Category.assoc, hφs]; exact (L.one t).2
    refine ⟨φ ≫ pullback.fst _ _, ?_⟩
    rw [ActionGroupoid.comp_action' L ι t φ hbase] at hφt
    have hone : (⟨φ ≫ pullback.snd (ι ≫ f) f, by rw [← hbase, Category.assoc]⟩ : SchemeHomOver t f) = L.one t := Subtype.ext hφs
    rw [hone, L.mul_one] at hφt
    rw [Category.assoc]; exact hφt
  · rintro ⟨e, he⟩
    apply Subtype.ext
    show x.1 ≫ p = ((lawP L ι p w hR hcoeq hcomm hE_inv).one t).1
    rw [lawP_one_coe, eP, ← Category.assoc t, comp_eJ]
    have hef : e ≫ ι ≫ f = t := by rw [← Category.assoc, he, x.2]
    have h := p_act L ι p w t e (L.one t) hef
    rw [L.mul_one] at h
    rw [← h]
    congr 1
    exact he.symm

end Law
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

end GoodReductionJacobian.RelativeGroupLaw.LawDescends
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid"

open GoodReductionJacobian.RelativeGroupLaw.LawDescends in
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
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
    (hcoeq : IsColimit (Cofork.ofπ p w)) :
    ∃ (g : P ⟶ Spec (CommRingCat.of R)) (hg : p ≫ g = f) (LP : RelativeGroupLaw R g),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
        LP.mul t x y = LP.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        (⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ : SchemeHomOver t g) = LP.one t ↔
          ∃ e : T ⟶ E, e ≫ ι = x.1) :=
  ⟨g L ι p w hcoeq, p_base L ι p w hcoeq, lawP L ι p w hR hcoeq hcomm hE_inv,
    fun t x y => hom L ι p w hR hcoeq hcomm hE_inv t x y, fun t x y => comm L ι p w hR hcoeq hcomm hE_inv t x y,
    fun t x => ker L ι p w hR hcoeq hcomm hE_inv t x⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit (solution)
