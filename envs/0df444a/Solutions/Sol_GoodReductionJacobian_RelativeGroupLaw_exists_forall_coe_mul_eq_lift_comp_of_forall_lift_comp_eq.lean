-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_forall_coe_mul_eq_lift_comp_of_forall_lift_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/14639abb-a2bd-50c8-a120-eaa97e2a6420

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_coe_mul_eq_lift_comp_of_forall_lift_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (m : pullback f f ⟶ A) (hm : m ≫ f = pullback.fst f f ≫ f)
    (e : Spec (CommRingCat.of R) ⟶ A) (he : e ≫ f = 𝟙 _)
    (ι : A ⟶ A) (hι : ι ≫ f = f)
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver t f),
      pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
          (by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2, z.2]) ≫ m =
        pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
          (by rw [Category.assoc, hm, pullback.lift_fst_assoc, y.2, x.2]) ≫ m)
    (hone_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      pullback.lift (t ≫ e) x.1 (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1)
    (hmul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      pullback.lift x.1 (t ≫ e) (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1)
    (hinv_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      pullback.lift (x.1 ≫ ι) x.1 (by rw [Category.assoc, hι]) ≫ m = t ≫ e) :
    ∃ L : RelativeGroupLaw R f,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (L.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (L.one t).1 = t ≫ e) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), (L.inv t x).1 = x.1 ≫ ι) := by
  refine ⟨{ mul := fun t x y => ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m,
              by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2]⟩
            one := fun t => ⟨t ≫ e, by rw [Category.assoc, he, Category.comp_id]⟩
            inv := fun t x => ⟨x.1 ≫ ι, by rw [Category.assoc, hι, x.2]⟩
            mul_assoc := fun t x y z => Subtype.ext (hassoc t x y z)
            one_mul := fun t x => Subtype.ext (hone_mul t x)
            mul_one := fun t x => Subtype.ext (hmul_one t x)
            inv_mul_cancel := fun t x => Subtype.ext (hinv_mul t x)
            mul_natural := fun t t' ψ hψ x y => Subtype.ext ?_ }, fun t x y => rfl, fun t => rfl, fun t x => rfl⟩
  show ψ ≫ (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) = pullback.lift (ψ ≫ x.1) (ψ ≫ y.1) _ ≫ m
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_coe_mul_eq_lift_comp_of_forall_lift_comp_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_coe_mul_eq_lift_comp_of_forall_lift_comp_eq (solution)
