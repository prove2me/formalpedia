-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:09.947056+00:00
-- url     : https://prove2.me/submissions/78d6cdc6-53c8-445f-a9c3-99f55ae87f06

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_carry_group
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibreProjection

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem point_power_eq_nsmul
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointCommGroup hc t
    x ^ n = L.nsmul t n x := by
  letI := L.pointCommGroup hc t
  induction n with
  | zero => rfl
  | succ n ih =>
      change x ^ (n + 1) = L.nsmul t n x * x
      rw [pow_succ, ih]

/-- The division-carry law admits explicit ambient coordinates expressed in
terms of the original relative multiplication, inverse and natural multiples. -/
theorem _root_.solution
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ H : RelativeGroupLaw R (Sigma.desc g), H.IsCommutative ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : ZMod 71)
        (x : SchemeHomOver t (g a)) (y : SchemeHomOver t (g b))
        (px py : SchemeHomOver t f),
        x.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1 = px.1 →
        y.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) b.val S).1 = py.1 →
        ∃ z : SchemeHomOver t (g (a + b)),
          (H.mul t ⟨x.1 ≫ Sigma.ι X a, by rw [Category.assoc, Sigma.ι_desc]; exact x.2⟩
            ⟨y.1 ≫ Sigma.ι X b, by rw [Category.assoc, Sigma.ι_desc]; exact y.2⟩).1 =
              z.1 ≫ Sigma.ι X (a + b) ∧
          z.1 ≫ pullback.fst (L.schemeNsmul 71)
              (L.nsmul (𝟙 _) (a + b).val S).1 =
            (L.mul t (L.mul t px py)
              (L.inv t (L.nsmul t ((a.val + b.val) / 71)
                (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S)))).1 := by
  classical
  obtain ⟨H, hcomm, hmul⟩ := L.exists_division_carry_group hc S
  refine ⟨H, hcomm, ?_⟩
  intro T t a b x y px py hpx hpy
  letI := L.pointCommGroup hc t
  obtain ⟨z, hz, hp⟩ := hmul t a b x y
  have hx : (⟨x.1 ≫ pullback.fst (L.schemeNsmul 71)
      (L.nsmul (𝟙 _) a.val S).1, by rw [hpx]; exact px.2⟩ : SchemeHomOver t f) = px :=
    Subtype.ext hpx
  have hy : (⟨y.1 ≫ pullback.fst (L.schemeNsmul 71)
      (L.nsmul (𝟙 _) b.val S).1, by rw [hpy]; exact py.2⟩ : SchemeHomOver t f) = py :=
    Subtype.ext hpy
  rw [hx, hy, div_eq_mul_inv, point_power_eq_nsmul L hc t] at hp
  exact ⟨z, hz, hp⟩

end GoodReductionJacobian.RelativeGroupLaw
