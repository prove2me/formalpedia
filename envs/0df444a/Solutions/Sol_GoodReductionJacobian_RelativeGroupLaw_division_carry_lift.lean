-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.division_carry_lift
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:46.448691+00:00
-- url     : https://prove2.me/submissions/1ab1b44f-c992-4547-a9de-f4e81228f10c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem nsmul_eq_point_pow
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointCommGroup hc t
    L.nsmul t n x = x ^ n := by
  letI := L.pointCommGroup hc t
  induction n with
  | zero => rfl
  | succ n ih =>
      change L.nsmul t n x * x = x ^ (n + 1)
      rw [ih, pow_succ]

/-- The carry formula is a morphism into the actual division fibre. This
statement works over every test scheme, including disconnected schemes. -/
theorem _root_.solution
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n a b : ℕ) :
    letI := L.pointCommGroup hc t
    let s := GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S
    ∀ x y : SchemeHomOver t f, x ^ n = s ^ a → y ^ n = s ^ b →
      ∃ z : SchemeHomOver t
          (pullback.snd (L.schemeNsmul n)
            (L.nsmul (𝟙 (Spec (CommRingCat.of R))) ((a + b) % n) S).1),
        z.1 ≫ pullback.fst (L.schemeNsmul n)
            (L.nsmul (𝟙 (Spec (CommRingCat.of R))) ((a + b) % n) S).1 =
          (x * y / s ^ ((a + b) / n)).1 := by
  letI := L.pointCommGroup hc t
  let s := GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S
  dsimp only
  intro x y hx hy
  let z := x * y / s ^ ((a + b) / n)
  have hz : z ^ n = s ^ ((a + b) % n) := by
    dsimp [z]
    rw [div_pow, mul_pow, hx, hy, ← pow_add, ← pow_mul]
    have hdiv : a + b = (a + b) % n + ((a + b) / n) * n := by
      simpa [Nat.mul_comm] using (Nat.mod_add_div (a + b) n).symm
    conv_lhs => arg 1; rw [hdiv, pow_add]
    exact mul_div_cancel_right _ _
  have hcomp : z.1 ≫ L.schemeNsmul n =
      t ≫ (L.nsmul (𝟙 (Spec (CommRingCat.of R))) ((a + b) % n) S).1 := by
    rw [← L.coe_nsmul_eq_comp_schemeNsmul t n z,
      nsmul_eq_point_pow L hc t n z, hz]
    have h := congrArg Subtype.val
      (L.nsmul_natural (𝟙 (Spec (CommRingCat.of R))) t t
        (by simp) ((a + b) % n) S)
    rw [nsmul_eq_point_pow L hc t] at h
    exact h.symm
  refine ⟨⟨pullback.lift z.1 t hcomp, pullback.lift_snd _ _ _⟩, ?_⟩
  exact pullback.lift_fst _ _ _

end GoodReductionJacobian.RelativeGroupLaw
