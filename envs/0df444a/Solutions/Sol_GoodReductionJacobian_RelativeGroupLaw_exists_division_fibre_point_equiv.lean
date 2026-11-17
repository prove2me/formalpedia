-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_division_fibre_point_equiv
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:12.303197+00:00
-- url     : https://prove2.me/submissions/7a468b43-22b0-407c-b68b-ef8650cc94b8

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

/-- The points of an actual division fibre are exactly the points satisfying
the division equation, with the original relative group law retained. -/
theorem _root_.solution
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∃ e : SchemeHomOver t (pullback.snd (L.schemeNsmul n) S.1) ≃
        {x : SchemeHomOver t f // L.nsmul t n x =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S},
      ∀ x, (e x).1.1 = x.1 ≫ pullback.fst (L.schemeNsmul n) S.1 := by
  classical
  have hfst : pullback.fst (L.schemeNsmul n) S.1 ≫ f =
      pullback.snd (L.schemeNsmul n) S.1 := by
    calc
      pullback.fst (L.schemeNsmul n) S.1 ≫ f =
          pullback.fst (L.schemeNsmul n) S.1 ≫ L.schemeNsmul n ≫ f := by
            rw [L.schemeNsmul_over]
      _ = pullback.snd (L.schemeNsmul n) S.1 ≫ S.1 ≫ f := by
            rw [pullback.condition_assoc]
      _ = pullback.snd (L.schemeNsmul n) S.1 := by rw [S.2]; simp
  let F : SchemeHomOver t (pullback.snd (L.schemeNsmul n) S.1) →
      {x : SchemeHomOver t f // L.nsmul t n x =
        GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S} := fun u =>
    ⟨⟨u.1 ≫ pullback.fst (L.schemeNsmul n) S.1, by
        rw [Category.assoc, hfst]; exact u.2⟩, by
      apply Subtype.ext
      rw [L.coe_nsmul_eq_comp_schemeNsmul]
      change (u.1 ≫ pullback.fst (L.schemeNsmul n) S.1) ≫ L.schemeNsmul n = t ≫ S.1
      rw [Category.assoc, pullback.condition, ← Category.assoc, u.2]⟩
  have hinj : Function.Injective F := by
    intro u v huv
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg (fun x => x.1.1) huv
    · exact u.2.trans v.2.symm
  have hsurj : Function.Surjective F := by
    intro x
    have hx : x.1.1 ≫ L.schemeNsmul n = t ≫ S.1 := by
      rw [← L.coe_nsmul_eq_comp_schemeNsmul]
      exact congrArg Subtype.val x.2
    let u : SchemeHomOver t (pullback.snd (L.schemeNsmul n) S.1) :=
      ⟨pullback.lift x.1.1 t hx, pullback.lift_snd _ _ _⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun _ => rfl⟩

end GoodReductionJacobian.RelativeGroupLaw
