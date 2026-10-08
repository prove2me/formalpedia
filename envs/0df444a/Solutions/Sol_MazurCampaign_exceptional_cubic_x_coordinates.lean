-- Prove2me | solution 1 for MazurCampaign.exceptional_cubic_x_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T08:49:55.030558+00:00
-- url     : https://prove2.me/submissions/3c744bba-e4dd-4fa4-9f58-2b6c33e2d732

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_exceptional_cubic_finite
import Theorems.Thm_MazurCampaign_good_reduction_card_bound


/- Source module: MazurTorsion.Arithmetic.ExceptionalTwoTwelve. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The exceptional `C₂ × C₁₂` torsion configuration

An embedding of `ZMod 2 × ZMod 12` supplies full rational two-torsion, a rational half of one
nonzero two-torsion point, and a nonzero rational three-torsion point. The halving identity and
the three-division polynomial reduce those data to a nondegenerate rational point on

`w² = (t² - 1)(9t² - 1)`.

The final Diophantine leaf says that this quartic has only the evident degenerate rational points.
This file proves the complete reduction to that leaf, together with the explicit map to the cubic
`Y² = (X - 10)(X - 6)(X + 6)`.
-/

namespace MazurTorsion







open scoped WeierstrassCurve.Affine











/-- The statement that the cubic birational to the exceptional quartic has only its seven
evident affine rational points. -/
def ExceptionalCubicIsTrivial : Prop :=
  ∀ X Y : ℚ, Y ^ 2 = (X - 10) * (X - 6) * (X + 6) →
    X = -6 ∨ X = 2 ∨ X = 6 ∨ X = 10 ∨ X = 18









end MazurTorsion

end


/- Source module: MazurTorsion.NumberTheory.ExceptionalCubicDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Explicit two-isogeny descent on the exceptional cubic

This file studies the rational elliptic curve

`y² = u(u² + 2u - 3) = u(u - 1)(u + 3)`,

which is obtained from
`Y² = (X - 10)(X - 6)(X + 6)` by `X = 4u + 6` and `Y = 8y`.

An explicit two-isogeny descent proves that `E(ℚ) / 2E(ℚ)` has at most
four elements.  Naïve-height descent then gives finite generation, and
the exact four rational two-torsion points force Mordell--Weil rank zero.
Consequently the rational point group is finite.

The last theorem deliberately records the remaining sharp boundary:
an independent bound `#E(ℚ) ≤ 8` would classify all points and prove
`ExceptionalCubicIsTrivial`.  Rank zero alone does not supply that bound,
because odd torsion or higher two-primary torsion must still be excluded.
-/

namespace MazurTorsion.ExceptionalCubic

open scoped WeierstrassCurve.Affine

/-- The translated `X₀(24)` model `y² = u(u² + 2u - 3)`. -/
def curve : WeierstrassCurve ℚ :=
  ⟨0, 2, 0, -3, 0⟩

/-- The curve two-isogenous to `curve`. -/
def dualCurve : WeierstrassCurve ℚ :=
  ⟨0, -4, 0, 16, 0⟩

private instance curve_isElliptic : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private instance dualCurve_isElliptic : dualCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [dualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma nonsingular_zero_zero :
    curve.toAffine.Nonsingular 0 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_neg_one_two :
    curve.toAffine.Nonsingular (-1) 2 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_neg_one_neg_two :
    curve.toAffine.Nonsingular (-1) (-2) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_three_six :
    curve.toAffine.Nonsingular 3 6 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_three_neg_six :
    curve.toAffine.Nonsingular 3 (-6) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_one_zero :
    curve.toAffine.Nonsingular 1 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_neg_three_zero :
    curve.toAffine.Nonsingular (-3) 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

/-- The rational two-torsion point `(0, 0)`. -/
def T : curve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

/-- The rational point `(-1, 2)`. -/
def D : curve.toAffine.Point :=
  .some (-1) 2 nonsingular_neg_one_two

private def Dneg : curve.toAffine.Point :=
  .some (-1) (-2) nonsingular_neg_one_neg_two

/-- The rational point `(3, 6)`. -/
def F : curve.toAffine.Point :=
  .some 3 6 nonsingular_three_six

private def Fneg : curve.toAffine.Point :=
  .some 3 (-6) nonsingular_three_neg_six

private def A : curve.toAffine.Point :=
  .some 1 0 nonsingular_one_zero

private def B : curve.toAffine.Point :=
  .some (-3) 0 nonsingular_neg_three_zero





































































private def eightPoints : Fin 8 → curve.toAffine.Point
  | 0 => 0
  | 1 => T
  | 2 => A
  | 3 => B
  | 4 => D
  | 5 => Dneg
  | 6 => F
  | 7 => Fneg

private lemma eightPoints_injective :
    Function.Injective eightPoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [eightPoints, T, A, B, D, Dneg, F, Fneg] at hij ⊢
  all_goals norm_num at hij

private theorem point_eq_one_of_eight [Finite curve.toAffine.Point]
    (hcard : Nat.card curve.toAffine.Point ≤ 8)
    (P : curve.toAffine.Point) :
    P = 0 ∨ P = T ∨ P = A ∨ P = B ∨
      P = D ∨ P = Dneg ∨ P = F ∨ P = Fneg := by
  have hbijective : Function.Bijective eightPoints :=
    eightPoints_injective.bijective_of_nat_card_le (by simpa using hcard)
  obtain ⟨i, hi⟩ := hbijective.2 P
  fin_cases i
  · left
    simpa [eightPoints] using hi.symm
  · right; left
    simpa [eightPoints] using hi.symm
  · right; right; left
    simpa [eightPoints] using hi.symm
  · right; right; right; left
    simpa [eightPoints] using hi.symm
  · right; right; right; right; left
    simpa [eightPoints] using hi.symm
  · right; right; right; right; right; left
    simpa [eightPoints] using hi.symm
  · right; right; right; right; right; right; left
    simpa [eightPoints] using hi.symm
  · right; right; right; right; right; right; right
    simpa [eightPoints] using hi.symm

/-- A cardinality bound of eight for this rational point group closes the
exceptional cubic classification. -/
theorem exceptionalCubicIsTrivial_of_point_card_le_eight
    [Finite curve.toAffine.Point]
    (hcard : Nat.card curve.toAffine.Point ≤ 8) :
    MazurTorsion.ExceptionalCubicIsTrivial := by
  intro X Y hXY
  let u : ℚ := (X - 6) / 4
  let y : ℚ := Y / 8
  have hcurve : y ^ 2 = u * (u ^ 2 + 2 * u - 3) := by
    dsimp [u, y]
    nlinarith [hXY]
  have hP : curve.toAffine.Nonsingular u y := by
    apply curve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curve]
    nlinarith [hcurve]
  rcases point_eq_one_of_eight hcard (.some u y hP) with
      h | h | h | h | h | h | h | h
  · exact (WeierstrassCurve.Affine.Point.some_ne_zero hP h).elim
  · right; right; left
    simp only [T, WeierstrassCurve.Affine.Point.some.injEq] at h
    dsimp [u] at h
    linarith [h.1]
  · right; right; right; left
    simp only [A, WeierstrassCurve.Affine.Point.some.injEq] at h
    dsimp [u] at h
    linarith [h.1]
  · left
    simp only [B, WeierstrassCurve.Affine.Point.some.injEq] at h
    dsimp [u] at h
    linarith [h.1]
  · right; left
    simp only [D, WeierstrassCurve.Affine.Point.some.injEq] at h
    dsimp [u] at h
    linarith [h.1]
  · right; left
    simp only [Dneg, WeierstrassCurve.Affine.Point.some.injEq] at h
    dsimp [u] at h
    linarith [h.1]
  · right; right; right; right
    simp only [F, WeierstrassCurve.Affine.Point.some.injEq] at h
    dsimp [u] at h
    linarith [h.1]
  · right; right; right; right
    simp only [Fneg, WeierstrassCurve.Affine.Point.some.injEq] at h
    dsimp [u] at h
    linarith [h.1]

end MazurTorsion.ExceptionalCubic

end

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Points of Weierstrass curves over finite fields: decidability and finiteness

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file provides `Decidable` instances for the predicates `WeierstrassCurve.Affine.Equation`
and `WeierstrassCurve.Affine.Nonsingular` (over any commutative ring with decidable equality),
and deduces `Finite` and `Fintype` instances for the type `WeierstrassCurve.Affine.Point` of
nonsingular points of a Weierstrass curve over a finite ring, via Mathlib's
`WeierstrassCurve.Affine.nonsingularPointEquiv`.

The decision procedure goes through `equation_iff`/`nonsingular_iff`, so it evaluates the
Weierstrass polynomials directly in the base ring, with no `Polynomial` arithmetic involved.
Consequently, for a concrete curve over `ZMod p` the number of points is computable by `decide`:
`Fintype.card W.Point` enumerates the pairs in `ZMod p × ZMod p` and filters by the (decidable)
nonsingularity condition.

We also provide `WeierstrassCurve.Affine.Point.mapEquiv`, the group *isomorphism* on points
induced by an isomorphism of base fields (the equiv version of
`WeierstrassCurve.Affine.Point.map`); it transports point counts along residue-field
identifications such as `ℤ ⧸ (p) ≃+* ZMod p`.
-/


namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

instance instDecidableEquationOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Equation x y) :=
  decidable_of_iff _ (W'.equation_iff x y).symm

instance instDecidableNonsingularOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Nonsingular x y) :=
  decidable_of_iff _ (W'.nonsingular_iff x y).symm

instance instFinitePoint [Finite R] : Finite W'.Point :=
  .of_equiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

instance instFintypePointOfDecidableEq [Fintype R] [DecidableEq R] : Fintype W'.Point :=
  .ofEquiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

end WeierstrassCurve.Affine

def cubicIntegralModel : WeierstrassCurve ℤ := ⟨0, 2, 0, -3, 0⟩

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma cubicIntegralModel_map : cubicIntegralModel.map (Int.castRingHom ℚ) =
    MazurTorsion.ExceptionalCubic.curve := by
  ext <;> simp [cubicIntegralModel, MazurTorsion.ExceptionalCubic.curve]

instance : (cubicIntegralModel.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [cubicIntegralModel_map]
  infer_instance

lemma cubicIntegralModel_count :
    Nat.card (cubicIntegralModel.map (Int.castRingHom (ZMod 5))).toAffine.Point = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem solution :
    ∀ X Y : ℚ, Y ^ 2 = (X - 10) * (X - 6) * (X + 6) →
      X = -6 ∨ X = 2 ∨ X = 6 ∨ X = 10 ∨ X = 18 := by
  letI : Finite MazurTorsion.ExceptionalCubic.curve.toAffine.Point :=
    MazurCampaign.exceptional_cubic_finite
  have hb := MazurCampaign.good_reduction_card_bound cubicIntegralModel 5
    (by decide) (by norm_num [cubicIntegralModel, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])
  rw [cubicIntegralModel_map, cubicIntegralModel_count] at hb
  have hcardTorsion : Nat.card (MazurCampaign.RationalTorsion
      MazurTorsion.ExceptionalCubic.curve) ≤ 8 := Nat.le_of_dvd (by decide) hb.2
  have hcard : Nat.card MazurTorsion.ExceptionalCubic.curve.toAffine.Point ≤ 8 := by
    have ht : AddCommGroup.torsion MazurTorsion.ExceptionalCubic.curve.toAffine.Point = ⊤ := by
      ext P
      change IsOfFinAddOrder P ↔ True
      exact ⟨fun _ ↦ trivial, fun _ ↦ isOfFinAddOrder_of_finite P⟩
    change Nat.card (AddCommGroup.torsion
      MazurTorsion.ExceptionalCubic.curve.toAffine.Point) ≤ 8 at hcardTorsion
    rw [ht] at hcardTorsion
    simpa only [Nat.card_congr
      (AddSubgroup.topEquiv : (⊤ : AddSubgroup
        MazurTorsion.ExceptionalCubic.curve.toAffine.Point) ≃+
        MazurTorsion.ExceptionalCubic.curve.toAffine.Point).toEquiv] using hcardTorsion
  exact MazurTorsion.ExceptionalCubic.exceptionalCubicIsTrivial_of_point_card_le_eight hcard
#print axioms solution
