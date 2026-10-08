-- Prove2me | solution 1 for MazurTransfer.x0_49_rational_points_two_cusps
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:06:24.917199+00:00
-- url     : https://prove2.me/submissions/8556ab80-bebb-4cce-9ec4-be4f8290f4e7

import Mathlib
import Definitions.Def_MazurTransfer_XZeroFortyNineCurveData
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_good_reduction_card_bound
import Theorems.Thm_MazurTransfer_x0_49_rational_points_finite


/- Source module: EllipticCurves.Mathlib.EllipticCurvePoint. Original headers retained. -/
section
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

section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

instance instDecidableEquationOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Equation x y) :=
  decidable_of_iff _ (W'.equation_iff x y).symm

instance instDecidableNonsingularOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Nonsingular x y) :=
  decidable_of_iff _ (W'.nonsingular_iff x y).symm



instance instFintypePointOfDecidableEq [Fintype R] [DecidableEq R] : Fintype W'.Point :=
  .ofEquiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

section PointMap

variable {K : Type*} [Field K] (W : Affine K)



variable [DecidableEq K]

/-- Transport of points along an equality of Weierstrass curves. -/
def Point.congr {W₁ W₂ : Affine K} (h : W₁ = W₂) : W₁.Point ≃+ W₂.Point := by
  subst h
  exact AddEquiv.refl _





variable (L : Type*) [Field L] [Algebra K L] [DecidableEq L]











end PointMap

namespace Point

variable {S F K : Type*} [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] (σ : F ≃ₐ[S] K)





end Point

end WeierstrassCurve.Affine

end

end


/- Source module: MazurTransfer.FinitePointReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


open scoped WeierstrassCurve.Affine
namespace MazurTransfer

/-- Boundary: identify a finite rational point group with its full torsion
subgroup. Downstream consumers: the X_1(14), X_1(15), and X_0(21) point counts. -/
noncomputable def finitePointTorsionEquiv (E : WeierstrassCurve ℚ)
    [Finite (E⁄ℚ).Point] : (E⁄ℚ).Point ≃+ MazurCampaign.RationalTorsion E :=
  (AddEquiv.ofBijective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
    ⟨Subtype.val_injective, fun P => ⟨⟨P, isOfFinAddOrder_of_finite P⟩, rfl⟩⟩).symm

lemma finite_point_card_dvd (W : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime]
    [(W.map (Int.castRingHom ℚ)).IsElliptic]
    [Finite ((W.map (Int.castRingHom ℚ))⁄ℚ).Point]
    (hp : 2 < p) (hgood : ¬ (p : ℤ) ∣ W.Δ) :
    Nat.card ((W.map (Int.castRingHom ℚ))⁄ℚ).Point ∣
      Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  rw [Nat.card_congr (finitePointTorsionEquiv (W.map (Int.castRingHom ℚ))).toEquiv]
  exact (MazurCampaign.good_reduction_card_bound W p hp hgood).2

lemma finite_toAffine_card_dvd (W : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime]
    [(W.map (Int.castRingHom ℚ)).IsElliptic]
    [Finite (W.map (Int.castRingHom ℚ)).toAffine.Point]
    (hp : 2 < p) (hgood : ¬ (p : ℤ) ∣ W.Δ) :
    Nat.card (W.map (Int.castRingHom ℚ)).toAffine.Point ∣
      Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  let E := W.map (Int.castRingHom ℚ)
  let e : (E⁄ℚ).Point ≃+ E.toAffine.Point :=
    WeierstrassCurve.Affine.Point.congr (by
      ext <;> simp [E, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.map])
  letI : Finite (E⁄ℚ).Point := Finite.of_equiv E.toAffine.Point e.symm.toEquiv
  rw [← Nat.card_congr e.toEquiv]
  exact finite_point_card_dvd W p hp hgood

end MazurTransfer
#print axioms MazurTransfer.finite_point_card_dvd

end


/- Source module: MazurTorsion.NumberTheory.XZeroFortyNineDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The two-isogeny descent for the `X₀(49)` model

The modular curve `X₀(49)` is the conductor-`49` elliptic curve
`y² + xy = x³ - x² - 2x - 1`; completing the square and shifting gives the
model

`y² = x(x² + 21x + 112)`

used here.  The two-isogenous curve is `Y² = X(X² - 42X - 7)`.  The
original descent images are `{1, 7}`: negative classes die by positivity,
and the classes `2` and `14` die modulo eight.  The dual images are
`{1, -7}`: the classes `-1` and `7` die by a two-step seven-adic descent.
Consequently every rational point lies in one of the two cosets of
doubling represented by `0` and `(0,0)`, the group is finitely generated
of rank zero, and, since the curve has no rational point of order four and
reduction modulo three bounds the cardinality by four, the rational point
group is exactly `{0, (0,0)}`.
-/

namespace MazurTorsion.XZeroFortyNine





private lemma curve_equation_of_nonsingular
    {U V : ℚ} (hP : curve.toAffine.Nonsingular U V) :
    V ^ 2 = U * (U ^ 2 + 21 * U + 112) := by
  have heq := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [curve] at heq
  nlinarith [heq]

/-! ## The dual squareclasses `-1` and `7` are impossible -/















/-! ## Dual abscissas have squareclass `1` or `-7` -/







/-! ## Curve abscissas have squareclass `1`, `2`, `7`, or `14` -/





























/-! ## Reverse doubling from a square abscissa -/









/-! ## The two doubling cosets and rank zero -/























private lemma double_T : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, curve]

private def twoToTwoTorsion :
    Fin 2 → {P : curve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T⟩



private lemma twoToTwoTorsion_surjective :
    Function.Surjective twoToTwoTorsion := by
  rintro ⟨P, htwo⟩
  cases P with
  | zero =>
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hself :
          WeierstrassCurve.Affine.Point.some U V hP =
            -WeierstrassCurve.Affine.Point.some U V hP := by
        rw [← add_eq_zero_iff_eq_neg]
        simpa [two_nsmul] using htwo
      have hV : V = 0 := by
        rw [WeierstrassCurve.Affine.Point.neg_some] at hself
        simp only [WeierstrassCurve.Affine.Point.some.injEq,
          true_and] at hself
        norm_num [WeierstrassCurve.Affine.negY, curve] at hself
        linarith
      have hcurve := curve_equation_of_nonsingular hP
      have hquadratic : 0 < U ^ 2 + 21 * U + 112 := by
        nlinarith [sq_nonneg (2 * U + 21)]
      have hU : U = 0 := by
        rw [hV] at hcurve
        norm_num at hcurve
        rcases hcurve with hU | hquad
        · exact hU
        · exact (ne_of_gt hquadratic hquad).elim
      subst U
      subst V
      refine ⟨1, ?_⟩
      apply Subtype.ext
      rfl

/-- A rational point killed by two is `0` or `(0,0)`. -/
theorem eq_zero_or_T_of_two_nsmul_eq_zero
    (P : curve.toAffine.Point) (h2 : (2 : ℕ) • P = 0) :
    P = 0 ∨ P = T := by
  obtain ⟨i, hi⟩ := twoToTwoTorsion_surjective ⟨P, h2⟩
  fin_cases i
  · left
    have := congrArg Subtype.val hi
    simpa [twoToTwoTorsion] using this.symm
  · right
    have := congrArg Subtype.val hi
    simpa [twoToTwoTorsion] using this.symm





/-- All rational points are torsion; the rational point group is
finite. -/
theorem point_finite : Finite curve.toAffine.Point := by
  exact MazurTransfer.x0_49_rational_points_finite


/-! ## No rational point of order four -/

private lemma sq_ne_oneHundredTwelve (x : ℚ) : x ^ 2 ≠ 112 := by
  intro hx
  have h7int : IsSquare (7 : ℤ) := by
    apply (Rat.isSquare_intCast_iff (z := 7)).mp
    refine ⟨x / 4, ?_⟩
    push_cast
    field_simp
    linear_combination -hx
  obtain ⟨k, hk⟩ := h7int
  have hk2 : k ^ 2 = 7 := by rw [hk]; ring
  have hub : k ≤ 3 := by nlinarith
  have hlb : -3 ≤ k := by nlinarith
  interval_cases k <;> omega

/-- The `X₀(49)` model has no rational point of order four. -/
theorem no_order_four (Q : curve.toAffine.Point)
    (hQ : (2 : ℕ) • Q = T) : False := by
  cases Q with
  | zero =>
      change (2 : ℕ) • (0 : curve.toAffine.Point) = T at hQ
      rw [nsmul_zero] at hQ
      exact WeierstrassCurve.Affine.Point.some_ne_zero
        nonsingular_zero_zero hQ.symm
  | some v w hvw =>
      have hcurve := curve_equation_of_nonsingular hvw
      have hw0 : w ≠ 0 := by
        intro hw
        subst hw
        have hvzero : v = 0 := by
          norm_num at hcurve
          rcases hcurve with h | h
          · exact h
          · exfalso
            nlinarith [sq_nonneg (2 * v + 21)]
        subst hvzero
        rw [show (WeierstrassCurve.Affine.Point.some 0 0 hvw :
          curve.toAffine.Point) = T from rfl] at hQ
        rw [two_nsmul, T] at hQ
        have hTT :
            (WeierstrassCurve.Affine.Point.some 0 0
              nonsingular_zero_zero : curve.toAffine.Point) +
              WeierstrassCurve.Affine.Point.some 0 0
                nonsingular_zero_zero = 0 := by
          apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
          norm_num [WeierstrassCurve.Affine.negY, curve]
        rw [hTT] at hQ
        exact WeierstrassCurve.Affine.Point.some_ne_zero
          nonsingular_zero_zero hQ.symm
      have hneg : w ≠ curve.toAffine.negY v w := by
        simp only [WeierstrassCurve.Affine.negY]
        norm_num [curve]
        intro h
        apply hw0
        linarith
      have hdouble :=
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne
          (h₁ := hvw) hneg
      rw [two_nsmul, hdouble, T] at hQ
      have hx :=
        (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp
          hQ |>.1
      have hwneneg : w ≠ -w := by
        intro h
        exact hw0 (by linarith)
      have hslope :
          curve.toAffine.slope v v w w =
            (3 * v ^ 2 + 42 * v + 112) / (2 * w) := by
        simp [WeierstrassCurve.Affine.slope,
          WeierstrassCurve.Affine.negY, curve, hwneneg]
        ring
      rw [WeierstrassCurve.Affine.addX, hslope] at hx
      norm_num [curve] at hx
      have hv0 : v ≠ 0 := by
        intro hv
        subst hv
        norm_num at hcurve
        exact hw0 hcurve
      have hxcleared : (v ^ 2 - 112) ^ 2 = 0 := by
        have h4w : (4 : ℚ) * w ^ 2 ≠ 0 := by positivity
        field_simp at hx
        nlinarith [hx, hcurve]
      exact sq_ne_oneHundredTwelve v
        (by nlinarith [hxcleared])

end MazurTorsion.XZeroFortyNine

end


/- Source module: MazurTorsion.NumberTheory.XZeroFortyNineReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




/-!
# Rational points on the `X₀(49)` model

The two-isogeny descent proves that the rational point group of

`y² = x(x² + 21x + 112)`

is finite with no point of order four.  Good reduction at three bounds
the cardinality by four, and an element of order three would force the
cardinality to be at least six.  Hence every rational point is killed by
two, and the group is exactly `{0, (0,0)}`: the two rational cusps of
`X₀(49)`.
-/

open WeierstrassCurve

namespace MazurTorsion.XZeroFortyNine

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum





































/-- The full rational point group has cardinality at most four by good reduction at three. -/
theorem point_card_le_four : Nat.card curve.toAffine.Point ≤ 4 := by
  let W : WeierstrassCurve ℤ := ⟨0, 21, 0, 112, 0⟩
  have hW : W.map (Int.castRingHom ℚ) = curve := by
    ext <;> norm_num [W, curve, WeierstrassCurve.map]
  letI : (W.map (Int.castRingHom ℚ)).IsElliptic := hW.symm ▸ inferInstance
  letI : Finite (W.map (Int.castRingHom ℚ)).toAffine.Point := hW.symm ▸ point_finite
  have hgood : ¬ (3 : ℤ) ∣ W.Δ := by
    norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hdiv := MazurTransfer.finite_toAffine_card_dvd W 3 (by decide) hgood
  have hcount : Nat.card (W.map (Int.castRingHom (ZMod 3))).toAffine.Point = 4 := by
    exact Nat.card_eq_fintype_card.trans (by decide +kernel)
  have hle : Nat.card curve.toAffine.Point ≤
      Nat.card (W.map (Int.castRingHom (ZMod 3))).toAffine.Point := by
    rw [← hW]
    exact Nat.le_of_dvd (by rw [hcount]; decide) hdiv
  simpa only [hcount] using hle


/-- Every rational point of the `X₀(49)` model is `0` or `(0,0)`: the two
rational cusps. -/
theorem point_eq_zero_or_T (P : curve.toAffine.Point) :
    P = 0 ∨ P = T := by
  letI : Finite curve.toAffine.Point := point_finite
  have hcard := point_card_le_four
  have hcard_pos : 0 < Nat.card curve.toAffine.Point :=
    Nat.card_pos
  have hT0 : T ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero
      nonsingular_zero_zero
  have hT2smul : (2 : ℕ) • T = 0 := by
    simp only [two_nsmul]
    rw [T]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    norm_num [WeierstrassCurve.Affine.negY, curve]
  have hT2 : (2 : ℕ) ∣ Nat.card curve.toAffine.Point := by
    have hTorder : addOrderOf T = 2 := by
      have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hT2smul
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exfalso
        apply hT0
        simpa [h1] using addOrderOf_nsmul_eq_zero T
      · exact h2
    rw [← hTorder]
    exact addOrderOf_dvd_natCard T
  have hP2 : (2 : ℕ) • P = 0 := by
    have horder := addOrderOf_dvd_natCard P
    have hpos : 0 < addOrderOf P :=
      (isOfFinAddOrder_of_finite P).addOrderOf_pos
    have hle : addOrderOf P ≤ 4 :=
      (Nat.le_of_dvd hcard_pos horder).trans hcard
    interval_cases h : addOrderOf P
    · -- order one
      have h1 := addOrderOf_nsmul_eq_zero P
      rw [h, one_nsmul] at h1
      rw [h1, nsmul_zero]
    · -- order two
      rw [← h]
      exact addOrderOf_nsmul_eq_zero P
    · -- order three forces cardinality at least six
      exfalso
      have h3 : (3 : ℕ) ∣ Nat.card curve.toAffine.Point := by
        rw [← h]
        exact addOrderOf_dvd_natCard P
      have h6 : (6 : ℕ) ∣ Nat.card curve.toAffine.Point :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hT2 h3
      have := Nat.le_of_dvd hcard_pos h6
      omega
    · -- order four is impossible
      exfalso
      have h4 : (4 : ℕ) • P = 0 := by
        rw [← h]
        exact addOrderOf_nsmul_eq_zero P
      have h22 : (2 : ℕ) • ((2 : ℕ) • P) = 0 := by
        rw [← mul_nsmul]
        exact h4
      have h20 : (2 : ℕ) • P ≠ 0 := by
        intro hzero
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hzero
        rw [h] at hdvd
        omega
      have h2T : (2 : ℕ) • P = T := by
        rcases eq_zero_or_T_of_two_nsmul_eq_zero _ h22 with h0 | hT
        · exact absurd h0 h20
        · exact hT
      exact no_order_four P h2T
  exact eq_zero_or_T_of_two_nsmul_eq_zero P hP2

end MazurTorsion.XZeroFortyNine

end

theorem solution :
  ∀ P : MazurTorsion.XZeroFortyNine.curve.toAffine.Point,
    P = 0 ∨ P = MazurTorsion.XZeroFortyNine.T := by
  exact MazurTorsion.XZeroFortyNine.point_eq_zero_or_T

#print axioms solution
