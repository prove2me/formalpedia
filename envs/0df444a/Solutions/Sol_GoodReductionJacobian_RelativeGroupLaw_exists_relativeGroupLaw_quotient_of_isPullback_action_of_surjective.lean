-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/778d334d-3930-5cb5-8430-915297d88f0f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.one_natural RelativeGroupLaw.actionSource RelativeGroupLaw.action_def"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "IsCommutative pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul actionSource actionFstPoint actionSndPoint action action_def"
namespace LawDescN
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Points

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.LawDescN.one_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') : GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) = L.one t' :=
  RelativeGroupLaw.one_natural L t t' ψ hψ

p2m_export "GoodReductionJacobian.RelativeGroupLaw.LawDescN" "one_natural"
theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h := L.mul_natural t t' ψ hψ (L.inv t x) x
  rw [L.inv_mul_cancel, one_natural] at h
  exact (eq_inv_of_mul_eq_one_left h.symm : _)

variable {E : Scheme.{u}} (ι : E ⟶ J)

theorem comp_action {T : Scheme.{u}} (φ : T ⟶ pullback (ι ≫ f) f) :
    φ ≫ L.action ι = (L.mul (φ ≫ RelativeGroupLaw.actionSource f ι)
      (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionFstPoint ι))
      (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionSndPoint ι))).1 := by
  rw [← L.mul_natural _ _ φ rfl, GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.action_def]

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

noncomputable def pt {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : T ⟶ pullback (ι ≫ f) f :=
  pullback.lift e x h

@[scoped simp] theorem pt_fst {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : pt ι e x h ≫ pullback.fst _ _ = e :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem pt_snd {T : Scheme.{u}} (e : T ⟶ E) (x : T ⟶ J) (h : e ≫ ι ≫ f = x ≫ f) : pt ι e x h ≫ pullback.snd _ _ = x :=
  pullback.lift_snd _ _ _

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

variable {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)

include w in

theorem p_act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (z : SchemeHomOver t f) (he : e ≫ ι ≫ f = t) :
    (L.mul t ⟨e ≫ ι, he⟩ z).1 ≫ p = z.1 ≫ p := by
  have hx : e ≫ ι ≫ f = z.1 ≫ f := by rw [he, z.2]
  rw [← comp_action_pt L ι t e z he hx, Category.assoc, ← w, ← Category.assoc, pt_snd]

theorem exists_eq_mul_of_comp_eq (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y₁ y₂ : SchemeHomOver t f) (h : y₁.1 ≫ p = y₂.1 ≫ p) :
    ∃ (e : T ⟶ E) (he : e ≫ ι ≫ f = t), y₂ = L.mul t ⟨e ≫ ι, he⟩ y₁ := by
  let φ := hR.lift y₁.1 y₂.1 h
  have hφ₁ : φ ≫ pullback.snd (ι ≫ f) f = y₁.1 := hR.lift_fst _ _ _
  have hφ₂ : φ ≫ L.action ι = y₂.1 := hR.lift_snd _ _ _
  have ht : φ ≫ RelativeGroupLaw.actionSource f ι = t := by
    show φ ≫ (pullback.snd _ _ ≫ f) = t
    rw [← Category.assoc, hφ₁]; exact y₁.2
  refine ⟨φ ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, hφ₁]; exact y₁.2, ?_⟩
  apply Subtype.ext
  rw [← hφ₂, comp_action' L ι t φ ht]
  congr 2
  all_goals first | exact Subtype.ext hφ₁ | exact Subtype.ext (Category.assoc _ _ _).symm

end Points

section Maps

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

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

noncomputable def iJ : J ⟶ J := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).1

theorem iJ_over : iJ L ≫ f = f := (L.inv f _).2

theorem comp_iJ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) : x.1 ≫ iJ L = (L.inv t x).1 := by
  obtain ⟨x, rfl⟩ := x
  have h := congrArg Subtype.val (inv_natural L f (x ≫ f) x rfl ⟨𝟙 J, Category.id_comp f⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [iJ, h]
  have hx : GoodReductionJacobian.schemeHomOverComp x rfl (⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f) =
      (⟨x, rfl⟩ : SchemeHomOver (x ≫ f) f) := Subtype.ext (Category.comp_id x)
  rw [hx]

noncomputable def eJ : Spec (CommRingCat.of R) ⟶ J := (L.one (𝟙 _)).1

theorem eJ_over : eJ L ≫ f = 𝟙 _ := (L.one _).2

theorem comp_eJ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : t ≫ eJ L = (L.one t).1 := by
  have h := congrArg Subtype.val (one_natural L (𝟙 _) t t (Category.comp_id t))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [eJ, h]

end Maps

section Products

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
  {P : Scheme.{u}} (g : P ⟶ Spec (CommRingCat.of R)) (p : J ⟶ P) (hg : p ≫ g = f)

noncomputable def oneP : pullback f f ⟶ pullback f g :=
  pullback.map f f f g (𝟙 J) p (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hg])

@[reassoc (attr := simp)] theorem oneP_fst : oneP g p hg ≫ pullback.fst _ _ = pullback.fst f f := by
  rw [oneP, pullback.lift_fst, Category.comp_id]
@[reassoc (attr := simp)] theorem oneP_snd : oneP g p hg ≫ pullback.snd _ _ = pullback.snd f f ≫ p := pullback.lift_snd _ _ _

theorem isPullback_oneP : IsPullback (pullback.snd f f) (oneP g p hg) p (pullback.snd f g) := by
  have outer : IsPullback (oneP g p hg ≫ pullback.fst f g) (pullback.snd f f) f (p ≫ g) := by
    rw [oneP_fst, hg]; exact IsPullback.of_hasPullback f f
  exact (IsPullback.of_right outer (oneP_snd g p hg) (IsPullback.of_hasPullback f g)).flip

noncomputable def twoP : pullback f g ⟶ pullback g g :=
  pullback.map f g g g p (𝟙 P) (𝟙 _) (by rw [Category.comp_id, hg]) (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)] theorem twoP_fst : twoP g p hg ≫ pullback.fst _ _ = pullback.fst f g ≫ p := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem twoP_snd : twoP g p hg ≫ pullback.snd _ _ = pullback.snd f g := by
  rw [twoP, pullback.lift_snd, Category.comp_id]

theorem isPullback_twoP : IsPullback (pullback.fst f g) (twoP g p hg) p (pullback.fst g g) := by
  have outer : IsPullback (twoP g p hg ≫ pullback.snd g g) (pullback.fst f g) g (p ≫ g) := by
    rw [twoP_snd, hg]; exact (IsPullback.of_hasPullback f g).flip
  exact (IsPullback.of_right outer (twoP_fst g p hg) (IsPullback.of_hasPullback g g).flip).flip

variable [Flat p] [Surjective p] [QuasiCompact p]

scoped instance flat_oneP : Flat (oneP g p hg) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_oneP g p hg) inferInstance
scoped instance surjective_oneP : Surjective (oneP g p hg) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_oneP g p hg) inferInstance
scoped instance quasiCompact_oneP : QuasiCompact (oneP g p hg) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_oneP g p hg) inferInstance
scoped instance flat_twoP : Flat (twoP g p hg) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_twoP g p hg) inferInstance
scoped instance surjective_twoP : Surjective (twoP g p hg) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_twoP g p hg) inferInstance
scoped instance quasiCompact_twoP : QuasiCompact (twoP g p hg) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_twoP g p hg) inferInstance

theorem epi_p : Epi p := Flat.epi_of_flat_of_surjective p

theorem epi_pp : Epi (oneP g p hg ≫ twoP g p hg) := by
  haveI := Flat.epi_of_flat_of_surjective (oneP g p hg)
  haveI := Flat.epi_of_flat_of_surjective (twoP g p hg)
  exact epi_comp _ _

theorem pp_fst : (oneP g p hg ≫ twoP g p hg) ≫ pullback.fst _ _ = pullback.fst f f ≫ p := by
  rw [Category.assoc, twoP_fst, oneP_fst_assoc]

theorem pp_snd : (oneP g p hg ≫ twoP g p hg) ≫ pullback.snd _ _ = pullback.snd f f ≫ p := by
  rw [Category.assoc, twoP_snd, oneP_snd]

end Products

section Descent

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J)
  {P : Scheme.{u}} (g : P ⟶ Spec (CommRingCat.of R)) (p : J ⟶ P) (hg : p ≫ g = f)
  (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [Flat p] [Surjective p] [QuasiCompact p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (he : e ≫ ι ≫ f = t),
    ∃ e' : T ⟶ E, e' ≫ ι = (L.inv t ⟨e ≫ ι, he⟩).1)
  (hE_norm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (e : T ⟶ E)
    (he : e ≫ ι ≫ f = t), ∃ e' : T ⟶ E, e' ≫ ι = (L.mul t (L.mul t x ⟨e ≫ ι, he⟩) (L.inv t x)).1)

include hg w hR hE_inv hE_norm

theorem exists_mul_act_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a y : SchemeHomOver t f) (e : T ⟶ E)
    (he : e ≫ ι ≫ f = t) :
    ∃ (e' : T ⟶ E) (he' : e' ≫ ι ≫ f = t), L.mul t a (L.mul t ⟨e ≫ ι, he⟩ y) = L.mul t ⟨e' ≫ ι, he'⟩ (L.mul t a y) := by
  obtain ⟨e', he'⟩ := hE_norm t a e he
  have he'f : e' ≫ ι ≫ f = t := by rw [← Category.assoc, he']; exact (L.mul t _ _).2
  refine ⟨e', he'f, ?_⟩
  have hpt : (⟨e' ≫ ι, he'f⟩ : SchemeHomOver t f) = L.mul t (L.mul t a ⟨e ≫ ι, he⟩) (L.inv t a) := Subtype.ext he'
  rw [hpt]
  letI := L.pointGroup t
  change a * (⟨e ≫ ι, he⟩ * y) = (a * ⟨e ≫ ι, he⟩ * a⁻¹) * (a * y)
  group

theorem cond_one {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback f f) (h : g₁ ≫ oneP g p hg = g₂ ≫ oneP g p hg) :
    g₁ ≫ (mJ L ≫ p) = g₂ ≫ (mJ L ≫ p) := by
  have ha : g₁ ≫ pullback.fst f f = g₂ ≫ pullback.fst f f := by
    rw [← oneP_fst g p hg, ← Category.assoc, h, Category.assoc]
  have hy : (g₁ ≫ pullback.snd f f) ≫ p = (g₂ ≫ pullback.snd f f) ≫ p := by
    rw [Category.assoc, Category.assoc, ← oneP_snd g p hg, ← Category.assoc, h, Category.assoc]
  let t : Z ⟶ Spec (CommRingCat.of R) := g₁ ≫ pullback.fst f f ≫ f
  have ht₂ : g₂ ≫ pullback.fst f f ≫ f = t := by rw [← Category.assoc, ← ha, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, comp_mJ L t g₁ rfl, comp_mJ L t g₂ ht₂]
  obtain ⟨e, he, hey⟩ := exists_eq_mul_of_comp_eq L ι p hR t
    ⟨g₁ ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩
    ⟨g₂ ≫ pullback.snd f f, by rw [← ht₂, Category.assoc, ← pullback.condition]⟩ hy
  have hX : (⟨g₂ ≫ pullback.fst f f, ht₂⟩ : SchemeHomOver t f) = ⟨g₁ ≫ pullback.fst f f, rfl⟩ := Subtype.ext ha.symm
  rw [hX, hey]
  obtain ⟨e', he', hmul⟩ := exists_mul_act_eq L ι g p hg w hR hE_inv hE_norm t ⟨g₁ ≫ pullback.fst f f, rfl⟩
    ⟨g₁ ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩ e he
  rw [hmul, p_act L ι p w t e' _ he']

noncomputable def mOne : pullback f g ⟶ P :=
  EffectiveEpi.desc (oneP g p hg) (mJ L ≫ p) (cond_one L ι g p hg w hR hE_inv hE_norm)

theorem oneP_mOne : oneP g p hg ≫ mOne L ι g p hg w hR hE_inv hE_norm = mJ L ≫ p :=
  EffectiveEpi.fac (oneP g p hg) (mJ L ≫ p) (cond_one L ι g p hg w hR hE_inv hE_norm)

theorem cond_two {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback f g) (h : g₁ ≫ twoP g p hg = g₂ ≫ twoP g p hg) :
    g₁ ≫ mOne L ι g p hg w hR hE_inv hE_norm = g₂ ≫ mOne L ι g p hg w hR hE_inv hE_norm := by

  have hv : g₁ ≫ pullback.snd f g = g₂ ≫ pullback.snd f g := by
    rw [← twoP_snd g p hg, ← Category.assoc, h, Category.assoc]
  have hx : (g₁ ≫ pullback.fst f g) ≫ p = (g₂ ≫ pullback.fst f g) ≫ p := by
    rw [Category.assoc, Category.assoc, ← twoP_fst g p hg, ← Category.assoc, h, Category.assoc]

  let c := pullback.fst g₁ (oneP g p hg)
  let d₁ := pullback.snd g₁ (oneP g p hg)
  have hcd : c ≫ g₁ = d₁ ≫ oneP g p hg := pullback.condition
  haveI : Flat c := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Surjective c := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Epi c := Flat.epi_of_flat_of_surjective c
  rw [← cancel_epi c, ← Category.assoc, ← Category.assoc, hcd, Category.assoc, oneP_mOne]

  have e1 : c ≫ g₂ ≫ pullback.snd f g ≫ g = d₁ ≫ pullback.snd f f ≫ f :=
    calc c ≫ g₂ ≫ pullback.snd f g ≫ g = c ≫ g₁ ≫ pullback.snd f g ≫ g := by
          rw [← Category.assoc g₂, ← hv, Category.assoc]
      _ = d₁ ≫ oneP g p hg ≫ pullback.snd f g ≫ g := by rw [← Category.assoc, hcd, Category.assoc]
      _ = d₁ ≫ pullback.snd f f ≫ p ≫ g := by rw [oneP_snd_assoc]
      _ = d₁ ≫ pullback.snd f f ≫ f := by rw [hg]
  have hd₂ : (c ≫ g₂ ≫ pullback.fst f g) ≫ f = (d₁ ≫ pullback.snd f f) ≫ f := by
    simp only [Category.assoc]
    rw [pullback.condition]
    exact e1
  let d₂ : _ ⟶ pullback f f := pullback.lift (c ≫ g₂ ≫ pullback.fst f g) (d₁ ≫ pullback.snd f f) hd₂
  have hd₂P : d₂ ≫ oneP g p hg = c ≫ g₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, oneP_fst, pullback.lift_fst, Category.assoc]
    · rw [Category.assoc, oneP_snd, pullback.lift_snd_assoc, Category.assoc, Category.assoc, ← hv,
        ← Category.assoc c g₁, hcd, Category.assoc, oneP_snd]
  rw [← hd₂P, Category.assoc, oneP_mOne]

  let t := d₁ ≫ pullback.fst f f ≫ f
  have ht₂ : d₂ ≫ pullback.fst f f ≫ f = t := by
    show d₂ ≫ pullback.fst f f ≫ f = d₁ ≫ pullback.fst f f ≫ f
    rw [pullback.condition, ← Category.assoc, pullback.lift_snd, Category.assoc]
  rw [← Category.assoc, ← Category.assoc d₂, comp_mJ L t d₁ rfl, comp_mJ L t d₂ ht₂]
  have hx' : (d₁ ≫ pullback.fst f f) ≫ p = (d₂ ≫ pullback.fst f f) ≫ p := by
    have e1 : d₁ ≫ pullback.fst f f = c ≫ g₁ ≫ pullback.fst f g := by
      rw [← oneP_fst g p hg, ← Category.assoc, ← hcd, Category.assoc]
    have e2 : d₂ ≫ pullback.fst f f = c ≫ g₂ ≫ pullback.fst f g := pullback.lift_fst _ _ _
    have hx2 : g₁ ≫ pullback.fst f g ≫ p = g₂ ≫ pullback.fst f g ≫ p := by simpa only [Category.assoc] using hx
    rw [e1, e2]
    simp only [Category.assoc]
    rw [hx2]
  obtain ⟨e, he, hey⟩ := exists_eq_mul_of_comp_eq L ι p hR t ⟨d₁ ≫ pullback.fst f f, rfl⟩ ⟨d₂ ≫ pullback.fst f f, ht₂⟩ hx'
  have hY : (⟨d₂ ≫ pullback.snd f f, by rw [← ht₂, Category.assoc, pullback.condition]⟩ : SchemeHomOver t f) =
      ⟨d₁ ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩ := Subtype.ext (pullback.lift_snd _ _ _)
  rw [hY, hey, L.mul_assoc, p_act L ι p w t e _ he]

noncomputable def mP : pullback g g ⟶ P :=
  EffectiveEpi.desc (twoP g p hg) (mOne L ι g p hg w hR hE_inv hE_norm) (cond_two L ι g p hg w hR hE_inv hE_norm)

theorem twoP_mP : twoP g p hg ≫ mP L ι g p hg w hR hE_inv hE_norm = mOne L ι g p hg w hR hE_inv hE_norm :=
  EffectiveEpi.fac (twoP g p hg) (mOne L ι g p hg w hR hE_inv hE_norm) (cond_two L ι g p hg w hR hE_inv hE_norm)

theorem pp_mP : (oneP g p hg ≫ twoP g p hg) ≫ mP L ι g p hg w hR hE_inv hE_norm = mJ L ≫ p := by
  rw [Category.assoc, twoP_mP, oneP_mOne]

theorem mP_over : mP L ι g p hg w hR hE_inv hE_norm ≫ g = pullback.fst _ _ ≫ g := by
  haveI := epi_pp g p hg
  rw [← cancel_epi (oneP g p hg ≫ twoP g p hg), ← Category.assoc, pp_mP, Category.assoc, hg, mJ_over,
    ← Category.assoc, pp_fst, Category.assoc, hg]

theorem cond_inv {Z : Scheme.{u}} (y₁ y₂ : Z ⟶ J) (h : y₁ ≫ p = y₂ ≫ p) : y₁ ≫ (iJ L ≫ p) = y₂ ≫ (iJ L ≫ p) := by
  let t : Z ⟶ Spec (CommRingCat.of R) := y₁ ≫ f
  have ht₂ : y₂ ≫ f = t := by
    show y₂ ≫ f = y₁ ≫ f
    rw [← hg, ← Category.assoc, ← h, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, comp_iJ L t ⟨y₁, rfl⟩, comp_iJ L t ⟨y₂, ht₂⟩]
  obtain ⟨e, he, hey⟩ := exists_eq_mul_of_comp_eq L ι p hR t ⟨y₁, rfl⟩ ⟨y₂, ht₂⟩ h
  rw [hey]
  obtain ⟨e', he'⟩ := hE_inv t e he
  have he'f : e' ≫ ι ≫ f = t := by rw [← Category.assoc, he']; exact (L.inv t _).2
  obtain ⟨e'', he''⟩ := hE_norm t (L.inv t ⟨y₁, rfl⟩) e' he'f
  have he''f : e'' ≫ ι ≫ f = t := by rw [← Category.assoc, he'']; exact (L.mul t _ _).2
  have key : L.inv t (L.mul t ⟨e ≫ ι, he⟩ ⟨y₁, rfl⟩) = L.mul t ⟨e'' ≫ ι, he''f⟩ (L.inv t ⟨y₁, rfl⟩) := by
    have h1 : (⟨e' ≫ ι, he'f⟩ : SchemeHomOver t f) = L.inv t ⟨e ≫ ι, he⟩ := Subtype.ext he'
    have h2 : (⟨e'' ≫ ι, he''f⟩ : SchemeHomOver t f) =
        L.mul t (L.mul t (L.inv t ⟨y₁, rfl⟩) ⟨e' ≫ ι, he'f⟩) (L.inv t (L.inv t ⟨y₁, rfl⟩)) := Subtype.ext he''
    rw [h2, h1]
    letI := L.pointGroup t
    change ((⟨e ≫ ι, he⟩ : SchemeHomOver t f) * ⟨y₁, rfl⟩)⁻¹ =
      ((⟨y₁, rfl⟩ : SchemeHomOver t f)⁻¹ * (⟨e ≫ ι, he⟩ : SchemeHomOver t f)⁻¹ * ((⟨y₁, rfl⟩ : SchemeHomOver t f)⁻¹)⁻¹) *
        (⟨y₁, rfl⟩ : SchemeHomOver t f)⁻¹
    group
  rw [key, p_act L ι p w t e'' _ he''f]

noncomputable def iP : P ⟶ P := EffectiveEpi.desc p (iJ L ≫ p) (cond_inv L ι g p hg w hR hE_inv hE_norm)

theorem p_iP : p ≫ iP L ι g p hg w hR hE_inv hE_norm = iJ L ≫ p :=
  EffectiveEpi.fac p (iJ L ≫ p) (cond_inv L ι g p hg w hR hE_inv hE_norm)

noncomputable def eP : Spec (CommRingCat.of R) ⟶ P := eJ L ≫ p

theorem eP_over : eP L p ≫ g = 𝟙 _ := by rw [eP, Category.assoc, hg, eJ_over]

theorem iP_over : iP L ι g p hg w hR hE_inv hE_norm ≫ g = g := by
  haveI := epi_p p
  rw [← cancel_epi p, ← Category.assoc, p_iP, Category.assoc, hg, iJ_over]

theorem over_p {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f) : (x.1 ≫ p) ≫ g = t := by
  rw [Category.assoc, hg, x.2]

theorem over_p' {T : Scheme.{u}} (a : T ⟶ J) : (a ≫ p) ≫ g = a ≫ f := by rw [Category.assoc, hg]

theorem over_eP {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : (t ≫ eP L p) ≫ g = t := by
  rw [Category.assoc, eP_over L ι g p hg w hR hE_inv hE_norm, Category.comp_id]

theorem over_g_eP : (g ≫ eP L p) ≫ g = 𝟙 P ≫ g := by
  rw [Category.assoc, eP_over L ι g p hg w hR hE_inv hE_norm, Category.comp_id, Category.id_comp]

theorem over_iP : iP L ι g p hg w hR hE_inv hE_norm ≫ g = 𝟙 P ≫ g := by rw [iP_over, Category.id_comp]

noncomputable abbrev pp := oneP g p hg ≫ twoP g p hg

theorem lift_pp {T : Scheme.{u}} (a b : T ⟶ J) (h : a ≫ f = b ≫ f) :
    pullback.lift a b h ≫ pp g p hg =
      pullback.lift (a ≫ p) (b ≫ p) ((over_p' L ι g p hg w hR hE_inv hE_norm a).trans (h.trans (over_p' L ι g p hg w hR hE_inv hE_norm b).symm)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pp_fst, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, pp_snd, pullback.lift_snd_assoc, pullback.lift_snd]

theorem lift_p_mP {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    pullback.lift (x.1 ≫ p) (y.1 ≫ p) ((over_p L ι g p hg w hR hE_inv hE_norm x).trans (over_p L ι g p hg w hR hE_inv hE_norm y).symm) ≫ mP L ι g p hg w hR hE_inv hE_norm =
      (L.mul t x y).1 ≫ p := by
  rw [← lift_pp L ι g p hg w hR hE_inv hE_norm x.1 y.1 (x.2.trans y.2.symm), Category.assoc, pp_mP, ← Category.assoc,
    comp_mJ L t _ (by rw [pullback.lift_fst_assoc]; exact x.2)]
  congr 3 <;> exact Subtype.ext (by simp only [pullback.lift_fst, pullback.lift_snd])

theorem p_iP_pt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    x.1 ≫ p ≫ iP L ι g p hg w hR hE_inv hE_norm = (L.inv t x).1 ≫ p := by
  rw [p_iP L ι g p hg w hR hE_inv hE_norm, ← Category.assoc, comp_iJ]

theorem mP_swap (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) : pullback.lift (pullback.snd _ _) (pullback.fst _ _) pullback.condition.symm ≫ mP L ι g p hg w hR hE_inv hE_norm =
    mP L ι g p hg w hR hE_inv hE_norm := by
  haveI := epi_pp g p hg
  rw [← cancel_epi (oneP g p hg ≫ twoP g p hg)]
  have hsw : (oneP g p hg ≫ twoP g p hg) ≫ pullback.lift (pullback.snd _ _) (pullback.fst _ _) pullback.condition.symm =
      pullback.lift (pullback.snd f f ≫ p) (pullback.fst f f ≫ p)
        ((over_p' L ι g p hg w hR hE_inv hE_norm _).trans (pullback.condition.symm.trans (over_p' L ι g p hg w hR hE_inv hE_norm _).symm)) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]; exact pp_snd g p hg
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]; exact pp_fst g p hg
  rw [← Category.assoc, hsw]
  change _ = pp g p hg ≫ _
  rw [pp_mP]
  have h := lift_p_mP L ι g p hg w hR hE_inv hE_norm (pullback.fst f f ≫ f) ⟨pullback.snd f f, pullback.condition.symm⟩ ⟨pullback.fst f f, rfl⟩
  rw [h, hcomm]
  rfl

theorem one_mul_id : pullback.lift (g ≫ eP L p) (𝟙 P) (over_g_eP L ι g p hg w hR hE_inv hE_norm) ≫ mP L ι g p hg w hR hE_inv hE_norm = 𝟙 P := by
  haveI := epi_p p
  rw [← cancel_epi p, Category.comp_id p, ← Category.assoc]
  have h1 : p ≫ pullback.lift (g ≫ eP L p) (𝟙 P) (over_g_eP L ι g p hg w hR hE_inv hE_norm) =
      pullback.lift ((L.one f).1 ≫ p) ((⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ p)
        ((over_p L ι g p hg w hR hE_inv hE_norm _).trans (over_p L ι g p hg w hR hE_inv hE_norm _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, hg, eP, ← Category.assoc, comp_eJ]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
  rw [h1, lift_p_mP L ι g p hg w hR hE_inv hE_norm f (L.one f) ⟨𝟙 J, Category.id_comp f⟩, L.one_mul]
  exact Category.id_comp _

theorem mul_one_id : pullback.lift (𝟙 P) (g ≫ eP L p) (over_g_eP L ι g p hg w hR hE_inv hE_norm).symm ≫ mP L ι g p hg w hR hE_inv hE_norm = 𝟙 P := by
  haveI := epi_p p
  rw [← cancel_epi p, Category.comp_id p, ← Category.assoc]
  have h1 : p ≫ pullback.lift (𝟙 P) (g ≫ eP L p) (over_g_eP L ι g p hg w hR hE_inv hE_norm).symm =
      pullback.lift ((⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ p) ((L.one f).1 ≫ p)
        ((over_p L ι g p hg w hR hE_inv hE_norm _).trans (over_p L ι g p hg w hR hE_inv hE_norm _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, hg, eP, ← Category.assoc, comp_eJ]
  rw [h1, lift_p_mP L ι g p hg w hR hE_inv hE_norm f ⟨𝟙 J, Category.id_comp f⟩ (L.one f), L.mul_one]
  exact Category.id_comp _

theorem inv_mul_id : pullback.lift (iP L ι g p hg w hR hE_inv hE_norm) (𝟙 P) (over_iP L ι g p hg w hR hE_inv hE_norm) ≫ mP L ι g p hg w hR hE_inv hE_norm =
    g ≫ eP L p := by
  haveI := epi_p p
  rw [← cancel_epi p, ← Category.assoc, ← Category.assoc, hg]
  have h1 : p ≫ pullback.lift (iP L ι g p hg w hR hE_inv hE_norm) (𝟙 P) (over_iP L ι g p hg w hR hE_inv hE_norm) =
      pullback.lift ((L.inv f ⟨𝟙 J, Category.id_comp f⟩).1 ≫ p) ((⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f).1 ≫ p)
        ((over_p L ι g p hg w hR hE_inv hE_norm _).trans (over_p L ι g p hg w hR hE_inv hE_norm _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, p_iP L ι g p hg w hR hE_inv hE_norm, iJ]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (Category.comp_id p).trans (Category.id_comp p).symm
  rw [h1, lift_p_mP L ι g p hg w hR hE_inv hE_norm f (L.inv f ⟨𝟙 J, Category.id_comp f⟩) ⟨𝟙 J, Category.id_comp f⟩, L.inv_mul_cancel, eP,
    ← Category.assoc, comp_eJ]

noncomputable def α3 : pullback (pullback.fst (g) (g) ≫ g) (g) ⟶ P :=
  pullback.lift (pullback.fst _ _ ≫ mP L ι g p hg w hR hE_inv hE_norm) (pullback.snd _ _)
    (by rw [Category.assoc, mP_over]; exact pullback.condition) ≫ mP L ι g p hg w hR hE_inv hE_norm

noncomputable def β3 : pullback (pullback.fst (g) (g) ≫ g) (g) ⟶ P :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
      (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition).symm.trans pullback.condition) ≫
      mP L ι g p hg w hR hE_inv hE_norm)
    (by rw [Category.assoc, Category.assoc, mP_over, pullback.lift_fst_assoc]; exact congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition) ≫
  mP L ι g p hg w hR hE_inv hE_norm

noncomputable def q3 : pullback (pullback.fst f f ≫ f) f ⟶ pullback (pullback.fst (g) (g) ≫ g) (g) :=
  pullback.map _ _ _ _ (pp g p hg) p (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc, pp_fst, Category.assoc, hg]) (by rw [Category.comp_id, hg])

theorem epi_q3 : Epi (q3 g p hg) := by
  have hflat : Flat (pp g p hg) := inferInstance
  have hsurj : Surjective (pp g p hg) := inferInstance
  have e₁ : pullback.fst f f ≫ f = pp g p hg ≫ pullback.fst (g) (g) ≫ g := by
    rw [← Category.assoc, pp_fst, Category.assoc, hg]
  have e₂ : f = p ≫ g := (hg).symm
  haveI : Flat (q3 g p hg) := MorphismProperty.pullbackMap (P := @Flat) hflat (inferInstance : Flat p) e₁ e₂
  haveI : Surjective (q3 g p hg) := MorphismProperty.pullbackMap (P := @Surjective) hsurj (inferInstance : Surjective p) e₁ e₂
  exact Flat.epi_of_flat_of_surjective _

@[reassoc] theorem q3_fst : q3 g p hg ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pp g p hg := pullback.lift_fst _ _ _
@[reassoc] theorem q3_snd : q3 g p hg ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := pullback.lift_snd _ _ _

theorem pp_mP' : oneP g p hg ≫ twoP g p hg ≫ mP L ι g p hg w hR hE_inv hE_norm = mJ L ≫ p := by
  rw [← Category.assoc]; exact pp_mP L ι g p hg w hR hE_inv hE_norm
theorem pp_fst' : oneP g p hg ≫ twoP g p hg ≫ pullback.fst _ _ = pullback.fst f f ≫ p := by
  rw [← Category.assoc]; exact pp_fst g p hg
theorem pp_snd' : oneP g p hg ≫ twoP g p hg ≫ pullback.snd _ _ = pullback.snd f f ≫ p := by
  rw [← Category.assoc]; exact pp_snd g p hg

noncomputable abbrev t3 : pullback (pullback.fst f f ≫ f) f ⟶ Spec (CommRingCat.of R) := pullback.fst _ _ ≫ pullback.fst f f ≫ f

noncomputable abbrev X3 : SchemeHomOver (t3 (f := f)) f := ⟨pullback.fst _ _ ≫ pullback.fst f f, rfl⟩
noncomputable abbrev Y3 : SchemeHomOver (t3 (f := f)) f :=
  ⟨pullback.fst _ _ ≫ pullback.snd f f, by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition).symm⟩
noncomputable abbrev Z3 : SchemeHomOver (t3 (f := f)) f := ⟨pullback.snd _ _, pullback.condition.symm⟩

theorem q3_α3 : q3 g p hg ≫ α3 L ι g p hg w hR hE_inv hE_norm = (L.mul t3 (L.mul t3 X3 Y3) Z3).1 ≫ p := by
  have hin : q3 g p hg ≫ pullback.lift (pullback.fst _ _ ≫ mP L ι g p hg w hR hE_inv hE_norm) (pullback.snd _ _)
        (by rw [Category.assoc, mP_over]; exact pullback.condition) =
      pullback.lift ((L.mul t3 X3 Y3).1 ≫ p) ((Z3 (f := f)).1 ≫ p) ((over_p L ι g p hg w hR hE_inv hE_norm _).trans (over_p L ι g p hg w hR hE_inv hE_norm _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc L ι g p hg w hR hE_inv hE_norm, pp_mP' L ι g p hg w hR hE_inv hE_norm, ← Category.assoc,
        comp_mJ L t3 _ rfl]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, q3_snd L ι g p hg w hR hE_inv hE_norm]
  rw [α3, ← Category.assoc, hin, lift_p_mP]

theorem q3_β3 : q3 g p hg ≫ β3 L ι g p hg w hR hE_inv hE_norm = (L.mul t3 X3 (L.mul t3 Y3 Z3)).1 ≫ p := by
  have hin : q3 g p hg ≫ pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
      (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
        (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition).symm.trans pullback.condition) ≫
        mP L ι g p hg w hR hE_inv hE_norm)
      (by rw [Category.assoc, Category.assoc, mP_over, pullback.lift_fst_assoc]; exact congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition) =
      pullback.lift ((X3 (f := f)).1 ≫ p) ((L.mul t3 Y3 Z3).1 ≫ p) ((over_p L ι g p hg w hR hE_inv hE_norm _).trans (over_p L ι g p hg w hR hE_inv hE_norm _).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc L ι g p hg w hR hE_inv hE_norm, pp_fst' L ι g p hg w hR hE_inv hE_norm, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]
      have h2 : q3 g p hg ≫ pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
            (by rw [Category.assoc]; exact (congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition).symm.trans pullback.condition) =
          pullback.lift ((Y3 (f := f)).1 ≫ p) ((Z3 (f := f)).1 ≫ p) ((over_p L ι g p hg w hR hE_inv hE_norm _).trans (over_p L ι g p hg w hR hE_inv hE_norm _).symm) := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, q3_fst_assoc L ι g p hg w hR hE_inv hE_norm, pp_snd' L ι g p hg w hR hE_inv hE_norm, Category.assoc]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, q3_snd L ι g p hg w hR hE_inv hE_norm]
      rw [h2, lift_p_mP]
  rw [β3, ← Category.assoc, hin, lift_p_mP]

theorem α3_eq_β3 : α3 L ι g p hg w hR hE_inv hE_norm = β3 L ι g p hg w hR hE_inv hE_norm := by
  haveI := epi_q3 L ι g p hg w hR hE_inv hE_norm
  rw [← cancel_epi (q3 g p hg), q3_α3, q3_β3, L.mul_assoc]

noncomputable abbrev pr2 {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (u v : SchemeHomOver t (g)) :
    T ⟶ pullback (g) (g) :=
  pullback.lift u.1 v.1 (u.2.trans v.2.symm)

noncomputable def lawP : RelativeGroupLaw R (g) where
  mul t u v := ⟨pr2 g u v ≫ mP L ι g p hg w hR hE_inv hE_norm, by rw [Category.assoc, mP_over L ι g p hg w hR hE_inv hE_norm, pullback.lift_fst_assoc]; exact u.2⟩
  one t := ⟨t ≫ eP L p, over_eP L ι g p hg w hR hE_inv hE_norm t⟩
  inv t u := ⟨u.1 ≫ iP L ι g p hg w hR hE_inv hE_norm, by rw [Category.assoc, iP_over L ι g p hg w hR hE_inv hE_norm]; exact u.2⟩
  mul_assoc t u v x := by
    apply Subtype.ext
    have h3 : pullback.lift (pr2 g u v) x.1 (by rw [pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ α3 L ι g p hg w hR hE_inv hE_norm =
        pullback.lift (pr2 g u v) x.1 (by rw [pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ β3 L ι g p hg w hR hE_inv hE_norm := by
      rw [α3_eq_β3]
    have hl : pullback.lift (pr2 g u v) x.1 (by rw [pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ α3 L ι g p hg w hR hE_inv hE_norm =
        pullback.lift (pr2 g u v ≫ mP L ι g p hg w hR hE_inv hE_norm) x.1
          (by rw [Category.assoc, mP_over L ι g p hg w hR hE_inv hE_norm, pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ mP L ι g p hg w hR hE_inv hE_norm := by
      rw [α3, ← Category.assoc]; congr 1
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    have hr : pullback.lift (pr2 g u v) x.1 (by rw [pullback.lift_fst_assoc]; exact u.2.trans x.2.symm) ≫ β3 L ι g p hg w hR hE_inv hE_norm =
        pullback.lift u.1 (pullback.lift v.1 x.1 (v.2.trans x.2.symm) ≫ mP L ι g p hg w hR hE_inv hE_norm)
          (by rw [Category.assoc, mP_over L ι g p hg w hR hE_inv hE_norm, pullback.lift_fst_assoc]; exact u.2.trans v.2.symm) ≫ mP L ι g p hg w hR hE_inv hE_norm := by
      rw [β3, ← Category.assoc]; congr 1
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]; congr 1
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    change pullback.lift (pr2 g u v ≫ mP L ι g p hg w hR hE_inv hE_norm) x.1 _ ≫ mP L ι g p hg w hR hE_inv hE_norm =
      pullback.lift u.1 (pullback.lift v.1 x.1 _ ≫ mP L ι g p hg w hR hE_inv hE_norm) _ ≫ mP L ι g p hg w hR hE_inv hE_norm
    rw [← hl, ← hr, h3]
  one_mul t u := by
    apply Subtype.ext
    change pullback.lift (t ≫ eP L p) u.1 _ ≫ mP L ι g p hg w hR hE_inv hE_norm = u.1
    have h : pullback.lift (t ≫ eP L p) u.1 ((over_eP L ι g p hg w hR hE_inv hE_norm t).trans u.2.symm) =
        u.1 ≫ pullback.lift (g ≫ eP L p) (𝟙 P) (over_g_eP L ι g p hg w hR hE_inv hE_norm) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, u.2]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h, Category.assoc, one_mul_id, Category.comp_id]
  mul_one t u := by
    apply Subtype.ext
    change pullback.lift u.1 (t ≫ eP L p) _ ≫ mP L ι g p hg w hR hE_inv hE_norm = u.1
    have h : pullback.lift u.1 (t ≫ eP L p) (u.2.trans (over_eP L ι g p hg w hR hE_inv hE_norm t).symm) =
        u.1 ≫ pullback.lift (𝟙 P) (g ≫ eP L p) (over_g_eP L ι g p hg w hR hE_inv hE_norm).symm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, u.2]
    rw [h, Category.assoc, mul_one_id, Category.comp_id]
  inv_mul_cancel t u := by
    apply Subtype.ext
    change pullback.lift (u.1 ≫ iP L ι g p hg w hR hE_inv hE_norm) u.1 _ ≫ mP L ι g p hg w hR hE_inv hE_norm = t ≫ eP L p
    have h : pullback.lift (u.1 ≫ iP L ι g p hg w hR hE_inv hE_norm) u.1 (by rw [Category.assoc, iP_over L ι g p hg w hR hE_inv hE_norm]) =
        u.1 ≫ pullback.lift (iP L ι g p hg w hR hE_inv hE_norm) (𝟙 P) (over_iP L ι g p hg w hR hE_inv hE_norm) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h, Category.assoc, inv_mul_id, ← Category.assoc, u.2]
  mul_natural t t' ψ hψ u v := by
    apply Subtype.ext
    change ψ ≫ pullback.lift u.1 v.1 _ ≫ mP L ι g p hg w hR hE_inv hE_norm = pullback.lift (ψ ≫ u.1) (ψ ≫ v.1) _ ≫ mP L ι g p hg w hR hE_inv hE_norm
    rw [← Category.assoc]; congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

theorem lawP_mul_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t (g)) :
    ((lawP L ι g p hg w hR hE_inv hE_norm).mul t u v).1 = pr2 g u v ≫ mP L ι g p hg w hR hE_inv hE_norm := rfl

theorem lawP_one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : ((lawP L ι g p hg w hR hE_inv hE_norm).one t).1 = t ≫ eP L p := rfl

theorem hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t (g)) =
      (lawP L ι g p hg w hR hE_inv hE_norm).mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩ := by
  apply Subtype.ext
  rw [lawP_mul_coe]
  exact (lift_p_mP L ι g p hg w hR hE_inv hE_norm t x y).symm

theorem comm (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t (g)) :
    (lawP L ι g p hg w hR hE_inv hE_norm).mul t u v = (lawP L ι g p hg w hR hE_inv hE_norm).mul t v u := by
  apply Subtype.ext
  rw [lawP_mul_coe, lawP_mul_coe]
  conv_rhs => rw [← mP_swap L ι g p hg w hR hE_inv hE_norm hcomm, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · show pullback.lift u.1 v.1 _ ≫ pullback.fst _ _ = (pullback.lift v.1 u.1 _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
    rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_snd]
  · show pullback.lift u.1 v.1 _ ≫ pullback.snd _ _ = (pullback.lift v.1 u.1 _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ _
    rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_fst]

theorem ker {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ : SchemeHomOver t (g)) = (lawP L ι g p hg w hR hE_inv hE_norm).one t ↔
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
    rw [comp_action' L ι t φ hbase] at hφt
    have hone : (⟨φ ≫ pullback.snd (ι ≫ f) f, by rw [← hbase, Category.assoc]⟩ : SchemeHomOver t f) = L.one t := Subtype.ext hφs
    rw [hone, L.mul_one] at hφt
    rw [Category.assoc]; exact hφt
  · rintro ⟨e, he⟩
    apply Subtype.ext
    show x.1 ≫ p = ((lawP L ι g p hg w hR hE_inv hE_norm).one t).1
    rw [lawP_one_coe, eP, ← Category.assoc t, comp_eJ]
    have hef : e ≫ ι ≫ f = t := by rw [← Category.assoc, he, x.2]
    have h := p_act L ι p w t e (L.one t) hef
    rw [L.mul_one] at h
    rw [← h]
    congr 1
    exact he.symm

end Descent

end GoodReductionJacobian.RelativeGroupLaw.LawDescN
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.GoodReductionJacobian.RelativeGroupLaw.LawDescN"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.GoodReductionJacobian"

open GoodReductionJacobian.RelativeGroupLaw.LawDescN in
theorem solution
    {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw R (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
      (n : SchemeHomOver t (i ≫ f)), ∃ n' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
            (L.inv t x))
    {Q : Scheme.{u}} {fQ : Q ⟶ Spec (CommRingCat.of R)} (q : SchemeHomOver f fQ)
    [Flat q.1] [LocallyOfFinitePresentation q.1] [Surjective q.1] [QuasiCompact q.1]
    (w : CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ q.1 = L.action i ≫ q.1)
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q.1 q.1)
    (hcoeq : IsColimit (Cofork.ofπ q.1 w)) :
    ∃ LQ : RelativeGroupLaw R fQ,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
          LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q)) ∧
      (L.IsCommutative → LQ.IsCommutative) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
          ∃ y : SchemeHomOver t (i ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) := by

  let iPt : SchemeHomOver (i ≫ f) f := ⟨i, rfl⟩

  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      NeronModelInfra.schemeHomOverComp (LN.one t) iPt = L.one t := by
    intro T t
    letI := L.pointGroup t
    have h := hi t (LN.one t) (LN.one t)
    rw [LN.one_mul] at h
    have h' : (NeronModelInfra.schemeHomOverComp (LN.one t) iPt : SchemeHomOver t f) =
        NeronModelInfra.schemeHomOverComp (LN.one t) iPt * NeronModelInfra.schemeHomOverComp (LN.one t) iPt := h
    exact left_eq_mul.mp h'

  have hinv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.inv t n) iPt = L.inv t (NeronModelInfra.schemeHomOverComp n iPt) := by
    intro T t n
    letI := L.pointGroup t
    have h := hi t (LN.inv t n) n
    rw [LN.inv_mul_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ N) (he : e ≫ i ≫ f = t),
      ∃ e' : T ⟶ N, e' ≫ i = (L.inv t ⟨e ≫ i, he⟩).1 := by
    intro T t e he
    refine ⟨(LN.inv t ⟨e, he⟩).1, ?_⟩
    have := congrArg Subtype.val (hinv t ⟨e, he⟩)
    simpa [NeronModelInfra.schemeHomOverComp] using this
  have hE_norm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (e : T ⟶ N)
      (he : e ≫ i ≫ f = t), ∃ e' : T ⟶ N, e' ≫ i = (L.mul t (L.mul t x ⟨e ≫ i, he⟩) (L.inv t x)).1 := by
    intro T t x e he
    obtain ⟨n', hn'⟩ := hnormal t x ⟨e, he⟩
    refine ⟨n'.1, ?_⟩
    have := congrArg Subtype.val hn'
    simpa [NeronModelInfra.schemeHomOverComp] using this
  refine ⟨lawP L i fQ q.1 q.2 w hR hE_inv hE_norm, ?_, ?_, ?_⟩
  · intro T t x y
    exact hom L i fQ q.1 q.2 w hR hE_inv hE_norm t x y
  · intro hc T t u v
    exact comm L i fQ q.1 q.2 w hR hE_inv hE_norm (fun t x y => hc t x y) t u v
  · intro T t x
    rw [show NeronModelInfra.schemeHomOverComp x q = (⟨x.1 ≫ q.1, by rw [Category.assoc, q.2, x.2]⟩ : SchemeHomOver t fQ) from rfl,
      ker L i fQ q.1 q.2 w hR hE_inv hE_norm t x]
    constructor
    · rintro ⟨e, he⟩
      have hef : e ≫ i ≫ f = t := by rw [← Category.assoc, he, x.2]
      exact ⟨⟨e, hef⟩, Subtype.ext he⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.1, congrArg Subtype.val hy⟩

#print axioms solution

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective (solution)
