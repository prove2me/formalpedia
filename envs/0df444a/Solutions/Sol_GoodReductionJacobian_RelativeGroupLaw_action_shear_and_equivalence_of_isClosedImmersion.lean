-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.action_shear_and_equivalence_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2ecfa3d2-ecf3-5f69-a168-735ab22f21de

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace G1AuxFFX

open GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left (G := SchemeHomOver t' f) h

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (v w : T ⟶ G) (hv : v ≫ f = t) (hw : w ≫ f = t) (hv' : v ≫ f = t') (hw' : w ≫ f = t') :
    (L.mul t ⟨v, hv⟩ ⟨w, hw⟩).1 = (L.mul t' ⟨v, hv'⟩ ⟨w, hw'⟩).1 := by
  subst h; rfl

theorem inv_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (v : T ⟶ G) (hv : v ≫ f = t) (hv' : v ≫ f = t') :
    (L.inv t ⟨v, hv⟩).1 = (L.inv t' ⟨v, hv'⟩).1 := by
  subst h; rfl

variable (L : RelativeGroupLaw R f) {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw R (i ≫ f))

theorem hom_one
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = L.one t := by
  letI := L.pointGroup t
  have h := hi t (LN.one t) (LN.one t)
  rw [LN.one_mul] at h

  have : L.mul t (NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) (L.one t) =
      L.mul t (NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
        (NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by
    rw [L.mul_one]; exact h
  exact (mul_left_cancel (G := SchemeHomOver t f) this).symm

theorem hom_inv
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : SchemeHomOver t (i ≫ f)) :
    NeronModelInfra.schemeHomOverComp (LN.inv t n) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
      L.inv t (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by
  letI := L.pointGroup t
  have h := hi t (LN.inv t n) n
  rw [LN.inv_mul_cancel, hom_one L i LN hi] at h
  exact eq_inv_of_mul_eq_one_left (G := SchemeHomOver t f) h.symm

theorem comp_action {T : Scheme.{u}} (φ : T ⟶ pullback (i ≫ f) f) :
    φ ≫ L.action i =
      (L.mul (φ ≫ actionSource f i)
        (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionFstPoint i))
        (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionSndPoint i))).1 :=
  congrArg Subtype.val (L.mul_natural _ _ φ rfl (L.actionFstPoint i) (L.actionSndPoint i))

theorem comp_action' {T : Scheme.{u}} (φ : T ⟶ pullback (i ≫ f) f) (t : T ⟶ Spec (CommRingCat.of R))
    (ht : φ ≫ actionSource f i = t) :
    φ ≫ L.action i =
      (L.mul t ⟨φ ≫ pullback.fst (i ≫ f) f ≫ i, by rw [← ht, Category.assoc, Category.assoc, pullback.condition]⟩
        ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [← ht, Category.assoc]⟩).1 := by
  rw [comp_action L i φ]
  exact mul_val_congr L ht _ _ _ _ _ _

def shearHom : pullback (i ≫ f) f ⟶ pullback (i ≫ f) f :=
  pullback.lift (pullback.fst (i ≫ f) f) (L.action i)
    (by rw [L.action_over]; exact pullback.condition)

def shearInv : pullback (i ≫ f) f ⟶ pullback (i ≫ f) f :=
  pullback.lift (pullback.fst (i ≫ f) f)
    (L.mul (actionSource f i) (L.inv (actionSource f i) (L.actionFstPoint i)) (L.actionSndPoint i)).1
    (by rw [(L.mul (actionSource f i) _ _).2]; exact pullback.condition)

@[scoped simp] theorem shearHom_fst : shearHom L i ≫ pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) f := pullback.lift_fst _ _ _
@[scoped simp] theorem shearHom_snd : shearHom L i ≫ pullback.snd (i ≫ f) f = L.action i := pullback.lift_snd _ _ _
@[scoped simp] theorem shearInv_fst : shearInv L i ≫ pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) f := pullback.lift_fst _ _ _
@[scoped simp] theorem shearInv_snd : shearInv L i ≫ pullback.snd (i ≫ f) f =
    (L.mul (actionSource f i) (L.inv (actionSource f i) (L.actionFstPoint i)) (L.actionSndPoint i)).1 :=
  pullback.lift_snd _ _ _

theorem shearHom_src : shearHom L i ≫ actionSource f i = actionSource f i := by
  show shearHom L i ≫ pullback.snd (i ≫ f) f ≫ f = pullback.snd (i ≫ f) f ≫ f
  rw [← Category.assoc, shearHom_snd, L.action_over]

theorem shearInv_src : shearInv L i ≫ actionSource f i = actionSource f i := by
  show shearInv L i ≫ pullback.snd (i ≫ f) f ≫ f = pullback.snd (i ≫ f) f ≫ f
  rw [← Category.assoc, shearInv_snd, (L.mul (actionSource f i) _ _).2]

def shear : pullback (i ≫ f) f ≅ pullback (i ≫ f) f where
  hom := shearHom L i
  inv := shearInv L i
  hom_inv_id := by
    have ha : GoodReductionJacobian.schemeHomOverComp (shearHom L i) (shearHom_src L i) (L.actionFstPoint i) =
        L.actionFstPoint i := Subtype.ext (by
          show shearHom L i ≫ pullback.fst (i ≫ f) f ≫ i = pullback.fst (i ≫ f) f ≫ i
          rw [← Category.assoc, shearHom_fst])
    have hb : GoodReductionJacobian.schemeHomOverComp (shearHom L i) (shearHom_src L i) (L.actionSndPoint i) =
        L.mul (actionSource f i) (L.actionFstPoint i) (L.actionSndPoint i) :=
      Subtype.ext ((shearHom_snd L i).trans (L.action_def i))
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, shearInv_fst, shearHom_fst]
    · rw [Category.id_comp, Category.assoc, shearInv_snd]
      have := congrArg Subtype.val (L.mul_natural _ _ (shearHom L i) (shearHom_src L i)
        (L.inv (actionSource f i) (L.actionFstPoint i)) (L.actionSndPoint i))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, inv_natural, ha, hb, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
      rfl
  inv_hom_id := by
    have ha : GoodReductionJacobian.schemeHomOverComp (shearInv L i) (shearInv_src L i) (L.actionFstPoint i) =
        L.actionFstPoint i := Subtype.ext (by
          show shearInv L i ≫ pullback.fst (i ≫ f) f ≫ i = pullback.fst (i ≫ f) f ≫ i
          rw [← Category.assoc, shearInv_fst])
    have hb : GoodReductionJacobian.schemeHomOverComp (shearInv L i) (shearInv_src L i) (L.actionSndPoint i) =
        L.mul (actionSource f i) (L.inv (actionSource f i) (L.actionFstPoint i)) (L.actionSndPoint i) :=
      Subtype.ext (shearInv_snd L i)
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, shearHom_fst, shearInv_fst]
    · rw [Category.id_comp, Category.assoc, shearHom_snd, L.action_def]
      have := congrArg Subtype.val (L.mul_natural _ _ (shearInv L i) (shearInv_src L i)
        (L.actionFstPoint i) (L.actionSndPoint i))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, ha, hb, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul]
      rfl

end G1AuxFFX
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion.G1AuxFFX"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion.G1AuxFFX"

open G1AuxFFX GoodReductionJacobian.RelativeGroupLaw in
theorem solution
    {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw R (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    L.action i ≫ f = CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ f ∧
    (∃ σ : CategoryTheory.Limits.pullback (i ≫ f) f ≅ CategoryTheory.Limits.pullback (i ≫ f) f,
      σ.hom ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = L.action i ∧
      σ.hom ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) f = CategoryTheory.Limits.pullback.fst (i ≫ f) f) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f),
      a ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = b ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f → a ≫ L.action i = b ≫ L.action i → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ G =>
      ∃ φ : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f, φ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = x ∧ φ ≫ L.action i = y) := by
  refine ⟨L.action_over i, ⟨shear L i, shearHom_snd L i, shearHom_fst L i⟩, ?_, ?_⟩
  ·
    intro T a b hs ht
    apply pullback.hom_ext _ hs

    let t : T ⟶ Spec (CommRingCat.of R) := a ≫ actionSource f i
    have hbt : b ≫ actionSource f i = t := by
      show b ≫ pullback.snd (i ≫ f) f ≫ f = a ≫ pullback.snd (i ≫ f) f ≫ f
      rw [← Category.assoc, ← hs, Category.assoc]
    rw [comp_action' L i a t rfl, comp_action' L i b t hbt] at ht
    letI := L.pointGroup t
    have hx : (⟨b ≫ pullback.snd (i ≫ f) f, by rw [← hbt, Category.assoc]⟩ : SchemeHomOver t f) =
        ⟨a ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩ := Subtype.ext hs.symm
    rw [hx] at ht
    have := mul_right_cancel (G := SchemeHomOver t f) (Subtype.ext ht)
    have h1 : (a ≫ pullback.fst (i ≫ f) f) ≫ i = (b ≫ pullback.fst (i ≫ f) f) ≫ i := by
      simpa only [Category.assoc] using congrArg Subtype.val this
    exact (cancel_mono i).mp h1
  ·
    intro T
    refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
    ·
      refine ⟨pullback.lift (LN.one (x ≫ f)).1 x (LN.one (x ≫ f)).2, pullback.lift_snd _ _ _, ?_⟩
      rw [comp_action' L i _ (x ≫ f) (by
        show pullback.lift (LN.one (x ≫ f)).1 x (LN.one (x ≫ f)).2 ≫ pullback.snd (i ≫ f) f ≫ f = x ≫ f
        rw [← Category.assoc, pullback.lift_snd])]
      have key : L.mul (x ≫ f) (NeronModelInfra.schemeHomOverComp (LN.one (x ≫ f)) ⟨i, rfl⟩) ⟨x, rfl⟩ = ⟨x, rfl⟩ := by
        rw [hom_one L i LN hi, L.one_mul]
      refine Eq.trans ?_ (congrArg Subtype.val key)
      congr 2 <;> apply Subtype.ext
      · show pullback.lift (LN.one (x ≫ f)).1 x _ ≫ pullback.fst (i ≫ f) f ≫ i = (LN.one (x ≫ f)).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · exact pullback.lift_snd _ _ _
    ·
      obtain ⟨φ, rfl, rfl⟩ := hxy
      let t : T ⟶ Spec (CommRingCat.of R) := φ ≫ actionSource f i
      let n : SchemeHomOver t (i ≫ f) := ⟨φ ≫ pullback.fst (i ≫ f) f, by
        show (φ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = φ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      let x : SchemeHomOver t f := ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩
      have hact : φ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n ⟨i, rfl⟩) x).1 :=
        (comp_action' L i φ t rfl).trans (mul_val_congr L rfl _ _ _ _ _ _)
      refine ⟨pullback.lift (LN.inv t n).1 (φ ≫ L.action i)
        (by rw [(LN.inv t n).2, Category.assoc, L.action_over]), pullback.lift_snd _ _ _, ?_⟩
      have hsrc : pullback.lift (LN.inv t n).1 (φ ≫ L.action i)
          (by rw [(LN.inv t n).2, Category.assoc, L.action_over]) ≫ actionSource f i = t := by
        show _ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, pullback.lift_snd, Category.assoc, L.action_over]
      rw [comp_action' L i _ t hsrc]
      letI := L.pointGroup t
      have key : L.mul t (NeronModelInfra.schemeHomOverComp (LN.inv t n) ⟨i, rfl⟩)
          (L.mul t (NeronModelInfra.schemeHomOverComp n ⟨i, rfl⟩) x) = x := by
        rw [hom_inv L i LN hi, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
      refine Eq.trans ?_ (congrArg Subtype.val key)
      congr 2 <;> apply Subtype.ext
      · show pullback.lift (LN.inv t n).1 (φ ≫ L.action i) _ ≫ pullback.fst (i ≫ f) f ≫ i = (LN.inv t n).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · show pullback.lift (LN.inv t n).1 (φ ≫ L.action i) _ ≫ pullback.snd (i ≫ f) f = (L.mul t _ x).1
        rw [pullback.lift_snd, hact]
    ·
      obtain ⟨φ, rfl, rfl⟩ := hxy
      obtain ⟨ψ, hψ, rfl⟩ := hyz
      let t : T ⟶ Spec (CommRingCat.of R) := φ ≫ actionSource f i
      let n₁ : SchemeHomOver t (i ≫ f) := ⟨φ ≫ pullback.fst (i ≫ f) f, by
        show (φ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = φ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      let x : SchemeHomOver t f := ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩
      have hψt : ψ ≫ actionSource f i = t := by
        show ψ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, hψ, Category.assoc, L.action_over]
      let n₂ : SchemeHomOver t (i ≫ f) := ⟨ψ ≫ pullback.fst (i ≫ f) f, by
        rw [← hψt]
        show (ψ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = ψ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      have hact1 : φ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n₁ ⟨i, rfl⟩) x).1 :=
        (comp_action' L i φ t rfl).trans (mul_val_congr L rfl _ _ _ _ _ _)
      have hact2 : ψ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n₂ ⟨i, rfl⟩)
          (L.mul t (NeronModelInfra.schemeHomOverComp n₁ ⟨i, rfl⟩) x)).1 := by
        rw [comp_action' L i ψ t hψt]
        congr 2
        apply Subtype.ext
        show ψ ≫ pullback.snd (i ≫ f) f = _
        rw [hψ, hact1]
      refine ⟨pullback.lift (LN.mul t n₂ n₁).1 (φ ≫ pullback.snd (i ≫ f) f)
        (by rw [(LN.mul t n₂ n₁).2, Category.assoc]), pullback.lift_snd _ _ _, ?_⟩
      have hsrc : pullback.lift (LN.mul t n₂ n₁).1 (φ ≫ pullback.snd (i ≫ f) f)
          (by rw [(LN.mul t n₂ n₁).2, Category.assoc]) ≫ actionSource f i = t := by
        show _ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, pullback.lift_snd, Category.assoc]
      rw [comp_action' L i _ t hsrc, hact2, ← L.mul_assoc, ← hi]
      congr 2 <;> apply Subtype.ext
      · show pullback.lift (LN.mul t n₂ n₁).1 _ _ ≫ pullback.fst (i ≫ f) f ≫ i = (LN.mul t n₂ n₁).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · exact pullback.lift_snd _ _ _

#print axioms solution

end S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion (solution)
