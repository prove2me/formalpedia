-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.division_fibre_points
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:18.348057+00:00
-- url     : https://prove2.me/submissions/90d045bd-4b52-4b9f-9fc8-c02d183e1b07

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_fibre_point_equiv
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_sigma_point_equiv_of_localRing
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

/-- The geometric points of the actual coproduct of division fibres retain
their component and ambient coordinates. -/
theorem _root_.solution
    {R : Type} [CommRing R] {B : Scheme.{0}}
    {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {K : Type} [CommRing K] [IsLocalRing K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {W : Type} [AddCommGroup W]
    (e : W ≃ SchemeHomOver t f)
    (he_add : ∀ x y, e (x + y) = L.mul t (e x) (e y))
    (P : W) (hP : e P = GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ E : (Σ a : ZMod 71, {x : W // 71 • x = a.val • P}) ≃
        SchemeHomOver t (Sigma.desc g),
      ∀ x, ∃ h : (e x.2.1).1 ≫ L.schemeNsmul 71 =
          t ≫ (L.nsmul (𝟙 _) x.1.val S).1,
        (E x).1 = pullback.lift (e x.2.1).1 t h ≫ Sigma.ι X x.1 ∧
        ∃ z : SchemeHomOver t (g x.1),
          z.1 ≫ Sigma.ι X x.1 = (E x).1 ∧
          z.1 ≫ pullback.fst (L.schemeNsmul 71)
            (L.nsmul (𝟙 _) x.1.val S).1 = (e x.2.1).1 := by
  classical
  dsimp only
  let X : ZMod 71 → Scheme.{0} := fun a =>
    pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
    pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  have he_zero : e 0 = L.one t := by
    letI := L.pointGroup t
    apply mul_left_cancel (a := e 0)
    change L.mul t (e 0) (e 0) = L.mul t (e 0) (L.one t)
    rw [← he_add, zero_add, L.mul_one]
  have he_nsmul (n : ℕ) (x : W) : e (n • x) = L.nsmul t n (e x) := by
    induction n with
    | zero => simpa using he_zero
    | succ n ih => rw [succ_nsmul, he_add, L.nsmul_succ, ih]
  have hcrit (a : ZMod 71) (x : W) :
      (71 • x = a.val • P) ↔
        L.nsmul t 71 (e x) = GoodReductionJacobian.schemeHomOverComp t
          (Category.comp_id t) (L.nsmul (𝟙 _) a.val S) := by
    rw [L.nsmul_natural, ← hP, ← he_nsmul, ← he_nsmul]
    exact e.injective.eq_iff.symm
  let q (a : ZMod 71) : {x : W // 71 • x = a.val • P} ≃
      {x : SchemeHomOver t f // L.nsmul t 71 x =
        GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t)
          (L.nsmul (𝟙 _) a.val S)} :=
    { toFun := fun x => ⟨e x.1, (hcrit a x.1).mp x.2⟩
      invFun := fun y => ⟨e.symm y.1, (hcrit a (e.symm y.1)).mpr (by
        simpa only [e.apply_symm_apply] using y.2)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
  choose A hA using fun a : ZMod 71 =>
    L.exists_division_fibre_point_equiv 71 (L.nsmul (𝟙 _) a.val S) t
  let C (a : ZMod 71) := (q a).trans (A a).symm
  have hC (a : ZMod 71) (x : {x : W // 71 • x = a.val • P}) :
      (C a x).1 ≫ pullback.fst (L.schemeNsmul 71)
          (L.nsmul (𝟙 _) a.val S).1 = (e x.1).1 := by
    rw [← hA a]
    change ((A a) ((A a).symm (q a x))).1.1 = (e x.1).1
    rw [Equiv.apply_symm_apply]
    rfl
  obtain ⟨D, hD⟩ := Scheme.exists_sigma_point_equiv_of_localRing X g t
  let E := (Equiv.sigmaCongrRight C).trans D
  refine ⟨E, ?_⟩
  intro x
  have hx : (e x.2.1).1 ≫ L.schemeNsmul 71 =
      t ≫ (L.nsmul (𝟙 _) x.1.val S).1 := by
    rw [← L.coe_nsmul_eq_comp_schemeNsmul]
    exact congrArg Subtype.val ((q x.1 x.2).2)
  have hCx : (C x.1 x.2).1 = pullback.lift (e x.2.1).1 t hx := by
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using hC x.1 x.2
    · simpa only [pullback.lift_snd] using (C x.1 x.2).2
  have hEx : (E x).1 = (C x.1 x.2).1 ≫ Sigma.ι X x.1 := by
    exact hD ⟨x.1, C x.1 x.2⟩
  refine ⟨hx, ?_, C x.1 x.2, hEx.symm, hC x.1 x.2⟩
  rw [hEx, hCx]

end GoodReductionJacobian.RelativeGroupLaw
