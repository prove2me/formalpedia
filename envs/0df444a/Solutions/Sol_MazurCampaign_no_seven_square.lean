-- Prove2me | solution 1 for MazurCampaign.no_seven_square
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T07:18:59.8673+00:00
-- url     : https://prove2.me/submissions/067a7b10-b54c-4f29-8a32-b8930f63755a

import Definitions.Def_MazurCampaign_group_constraints
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/


/-!
# The full rational three-torsion obstruction

This file proves that the rational points of a Weierstrass curve over `ℚ`
cannot contain a subgroup isomorphic to `ZMod 3 × ZMod 3`. The proof derives
the three-division polynomial from the tangent formulas and uses its four
hypothetical rational roots to contradict the Weierstrass coefficient
relation.
-/

namespace MazurTorsion.ThreeTorsion

open WeierstrassCurve

lemma tangent_forces_three_division
    {a₁ a₂ a₃ a₄ a₆ x y slope : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : slope ^ 2 + a₁ * slope - a₂ - 3 * x = 0) :
    3 * x ^ 4 + (a₁ ^ 2 + 4 * a₂) * x ^ 3 +
      3 * (a₁ * a₃ + 2 * a₄) * x ^ 2 +
      3 * (a₃ ^ 2 + 4 * a₆) * x +
      (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ +
        a₂ * a₃ ^ 2 - a₄ ^ 2) = 0 := by
  linear_combination
    -(2 * y + a₁ * x + a₃) ^ 2 * hx +
    ((3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      slope * (2 * y + a₁ * x + a₃) +
      a₁ * (2 * y + a₁ * x + a₃)) * hslope -
    (a₁ ^ 2 + 4 * a₂ + 12 * x) * hcurve

/-- The exact algebraic identity behind the three-division polynomial:
on the curve, the value of `Ψ₃` is the negative square of the tangent
denominator times the difference between the doubled and original
x-coordinates. -/
lemma three_division_tangent_identity
    {a₁ a₂ a₃ a₄ a₆ x y slope : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) :
    3 * x ^ 4 + (a₁ ^ 2 + 4 * a₂) * x ^ 3 +
        3 * (a₁ * a₃ + 2 * a₄) * x ^ 2 +
        3 * (a₃ ^ 2 + 4 * a₆) * x +
        (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ +
          a₂ * a₃ ^ 2 - a₄ ^ 2) =
      -(2 * y + a₁ * x + a₃) ^ 2 *
        (slope ^ 2 + a₁ * slope - a₂ - 3 * x) := by
  linear_combination
    ((3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      slope * (2 * y + a₁ * x + a₃) +
      a₁ * (2 * y + a₁ * x + a₃)) * hslope -
    (a₁ ^ 2 + 4 * a₂ + 12 * x) * hcurve

open scoped WeierstrassCurve.Affine

lemma nonzero_three_torsion_abscissa
    (W : WeierstrassCurve.Affine ℚ) (P : W.Point)
    (hthree : (3 : ℕ) • P = 0) (hne : P ≠ 0) :
    ∃ x y, ∃ hP : W.Nonsingular x y,
      P = .some x y hP ∧ Polynomial.eval x W.Ψ₃ = 0 := by
  cases P with
  | zero => exact (hne rfl).elim
  | some x y hP =>
      have hthree' :
          (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP = 0 := by
        simpa [three_nsmul, two_nsmul, add_assoc] using hthree
      have hdouble :
          (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some x y hP := by
        rw [← add_eq_zero_iff_eq_neg]
        exact hthree'
      have hy : y ≠ W.negY x y := by
        intro hy
        have htwo :
            (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
          rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
        have : WeierstrassCurve.Affine.Point.some x y hP = 0 := by
          rw [htwo, zero_add] at hthree'
          exact hthree'
        exact hne this
      let slope := W.slope x x y y
      have hadd :=
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
      have hxcoord : W.addX x x slope = x := by
        have hsum :
            WeierstrassCurve.Affine.Point.some x y hP +
                WeierstrassCurve.Affine.Point.some x y hP =
              -WeierstrassCurve.Affine.Point.some x y hP := by
          simpa [two_nsmul] using hdouble
        have hsome := hadd.symm.trans hsum
        exact (WeierstrassCurve.Affine.Point.some.inj hsome).1
      have hslope :
          slope * (2 * y + W.a₁ * x + W.a₃) =
            3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
        have hden : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
          simp only [WeierstrassCurve.Affine.negY]
          ring
        dsimp [slope]
        rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
          div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
      have hx : slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x = 0 := by
        have := hxcoord
        simp only [WeierstrassCurve.Affine.addX] at this
        linarith
      have hcurve := hP.1
      rw [WeierstrassCurve.Affine.equation_iff] at hcurve
      have hψ := tangent_forces_three_division hcurve hslope hx
      refine ⟨x, y, hP, rfl, ?_⟩
      simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring_nf at hψ ⊢
      exact hψ

/-- For a nonsingular affine point over `ℚ`, vanishing of the
three-division polynomial is equivalent to the point being killed by `3`. -/
theorem three_nsmul_some_eq_zero_iff
    (W : WeierstrassCurve.Affine ℚ) {x y : ℚ}
    (hP : W.Nonsingular x y) :
    (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 ↔
      Polynomial.eval x W.Ψ₃ = 0 := by
  constructor
  · intro hthree
    obtain ⟨x', y', hP', heq, hψ⟩ :=
      nonzero_three_torsion_abscissa W
        (WeierstrassCurve.Affine.Point.some x y hP) hthree
        (WeierstrassCurve.Affine.Point.some_ne_zero hP)
    have hcoords := WeierstrassCurve.Affine.Point.some.inj heq
    simpa [hcoords.1] using hψ
  · intro hψ
    have hcurve := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at hcurve
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hψ
    let D := 2 * y + W.a₁ * x + W.a₃
    let N := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
    have hD : D ≠ 0 := by
      intro hD0
      have hN2 : N ^ 2 = 0 := by
        dsimp [D, N] at hD0 ⊢
        linear_combination
          -hψ - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * hcurve -
          (W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) -
            (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃)) * hD0
      have hN : N = 0 := sq_eq_zero_iff.mp hN2
      rw [WeierstrassCurve.Affine.nonsingular_iff'] at hP
      rcases hP.2 with hX | hY
      · apply hX
        dsimp [N] at hN
        linarith
      · exact hY (by simpa [D] using hD0)
    let slope := W.slope x x y y
    have hy : y ≠ W.negY x y := by
      intro hy
      apply hD
      dsimp [D]
      simp only [WeierstrassCurve.Affine.negY] at hy
      linarith
    have hslope :
        slope * D = N := by
      have hden : y - W.negY x y = D := by
        dsimp [D]
        ring
      dsimp [slope]
      rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
        div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
    have hidentity :=
      three_division_tangent_identity hcurve hslope
    have hx : slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x = 0 := by
      have hmul : D ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) = 0 := by
        dsimp [D, N] at hidentity ⊢
        linear_combination hidentity - hψ
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hD)
    have hadd :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
    have hxcoord : W.addX x x slope = x := by
      simp only [WeierstrassCurve.Affine.addX]
      linarith
    change W.addX x x (W.slope x x y y) = x at hxcoord
    have hxrep :
        ((2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP).xRep =
          (WeierstrassCurve.Affine.Point.some x y hP).xRep := by
      rw [two_nsmul, hadd]
      simp only [WeierstrassCurve.Affine.Point.xRep_some, hxcoord]
    rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
      with hdouble | hdouble
    · have hzero : WeierstrassCurve.Affine.Point.some x y hP = 0 := by
        have hsum :
            WeierstrassCurve.Affine.Point.some x y hP +
                WeierstrassCurve.Affine.Point.some x y hP =
              WeierstrassCurve.Affine.Point.some x y hP + 0 := by
          rw [add_zero]
          rw [two_nsmul] at hdouble
          exact hdouble
        exact add_left_cancel hsum
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hzero).elim
    · rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
        hdouble, neg_add_cancel]

private noncomputable def threeTorsionRootMap
    (W : WeierstrassCurve.Affine ℚ) :
    {P : W.Point // (3 : ℕ) • P = 0} →
      Option (W.Ψ₃.rootSet ℚ × Bool)
  | ⟨0, _⟩ => none
  | ⟨WeierstrassCurve.Affine.Point.some x y hP, hthree⟩ =>
      some (⟨x, by
        rw [Polynomial.mem_rootSet_of_ne (W.Ψ₃_ne_zero (by norm_num))]
        exact (three_nsmul_some_eq_zero_iff W hP).mp hthree⟩,
        decide (y ≤ W.negY x y))

private theorem threeTorsionRootMap_injective
    (W : WeierstrassCurve.Affine ℚ) :
    Function.Injective (threeTorsionRootMap W) := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hmap
  apply Subtype.ext
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y hxy => simp [threeTorsionRootMap] at hmap
  | some x y hxy =>
      cases Q with
      | zero => simp [threeTorsionRootMap] at hmap
      | some x' y' hxy' =>
          have hpair :
              ((⟨x, by
                rw [Polynomial.mem_rootSet_of_ne (W.Ψ₃_ne_zero (by norm_num))]
                exact (three_nsmul_some_eq_zero_iff W hxy).mp hP⟩,
                decide (y ≤ W.negY x y)) : W.Ψ₃.rootSet ℚ × Bool) =
              ((⟨x', by
                rw [Polynomial.mem_rootSet_of_ne (W.Ψ₃_ne_zero (by norm_num))]
                exact (three_nsmul_some_eq_zero_iff W hxy').mp hQ⟩,
                decide (y' ≤ W.negY x' y')) : W.Ψ₃.rootSet ℚ × Bool) := by
            simpa only [threeTorsionRootMap, Option.some.injEq] using hmap
          have hx : x = x' :=
            congrArg (fun z : W.Ψ₃.rootSet ℚ × Bool ↦ z.1.1) hpair
          have hbool :
              decide (y ≤ W.negY x y) =
                decide (y' ≤ W.negY x' y') :=
            congrArg (fun z : W.Ψ₃.rootSet ℚ × Bool ↦ z.2) hpair
          subst x'
          have hxrep :
              (WeierstrassCurve.Affine.Point.some x y hxy).xRep =
                (WeierstrassCurve.Affine.Point.some x y' hxy').xRep := by
            simp
          rcases
              WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
            with heq | heq
          · exact heq
          · have hy : y = W.negY x y' :=
              (WeierstrassCurve.Affine.Point.some.inj heq).2
            have hy' : y' = W.negY x y := by
              rw [hy, WeierstrassCurve.Affine.negY_negY]
            have hbool' : (y ≤ y') ↔ (y' ≤ y) := by
              rw [hy'.symm, hy.symm] at hbool
              exact decide_eq_decide.mp hbool
            have hyy : y = y' := by
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · exact (not_le_of_gt hlt) (hbool'.mp (le_of_lt hlt))
              · exact (not_le_of_gt hgt) (hbool'.mpr (le_of_lt hgt))
            simp only [WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨trivial, hyy⟩

/-- The rational three-torsion of a Weierstrass curve has at most nine
points. -/
theorem ncard_three_torsion_le_nine
    (W : WeierstrassCurve.Affine ℚ) :
    Set.ncard {P : W.Point | (3 : ℕ) • P = 0} ≤ 9 := by
  rw [← Nat.card_coe_set_eq]
  calc
    Nat.card {P : W.Point // (3 : ℕ) • P = 0}
        ≤ Nat.card (Option (W.Ψ₃.rootSet ℚ × Bool)) :=
      Nat.card_le_card_of_injective (threeTorsionRootMap W)
        (threeTorsionRootMap_injective W)
    _ = Nat.card (W.Ψ₃.rootSet ℚ) * Nat.card Bool + 1 := by
      rw [Finite.card_option, Nat.card_prod]
    _ ≤ 4 * 2 + 1 := by
      gcongr
      · rw [Nat.card_coe_set_eq]
        exact (W.Ψ₃.ncard_rootSet_le ℚ).trans_eq
          (W.natDegree_Ψ₃ (by norm_num))
      · norm_num
    _ = 9 := by norm_num

lemma quartic_coefficients_of_four_distinct_roots
    {b₂ b₄ b₆ b₈ r₁ r₂ r₃ r₄ : ℚ}
    (hne₁₂ : r₁ ≠ r₂) (hne₁₃ : r₁ ≠ r₃) (hne₁₄ : r₁ ≠ r₄)
    (hne₂₃ : r₂ ≠ r₃) (hne₂₄ : r₂ ≠ r₄) (hne₃₄ : r₃ ≠ r₄)
    (h₁ : 3 * r₁ ^ 4 + b₂ * r₁ ^ 3 + 3 * b₄ * r₁ ^ 2 +
      3 * b₆ * r₁ + b₈ = 0)
    (h₂ : 3 * r₂ ^ 4 + b₂ * r₂ ^ 3 + 3 * b₄ * r₂ ^ 2 +
      3 * b₆ * r₂ + b₈ = 0)
    (h₃ : 3 * r₃ ^ 4 + b₂ * r₃ ^ 3 + 3 * b₄ * r₃ ^ 2 +
      3 * b₆ * r₃ + b₈ = 0)
    (h₄ : 3 * r₄ ^ 4 + b₂ * r₄ ^ 3 + 3 * b₄ * r₄ ^ 2 +
      3 * b₆ * r₄ + b₈ = 0) :
    b₂ = -3 * (r₁ + r₂ + r₃ + r₄) ∧
      b₄ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
        r₂ * r₃ + r₂ * r₄ + r₃ * r₄ ∧
      b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
        r₁ * r₃ * r₄ + r₂ * r₃ * r₄) ∧
      b₈ = 3 * (r₁ * r₂ * r₃ * r₄) := by
  have g₁₂ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₂ + r₁ * r₂ ^ 2 + r₂ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) +
        3 * b₄ * (r₁ + r₂) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₂) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₂ + r₁ * r₂ ^ 2 + r₂ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) +
          3 * b₄ * (r₁ + r₂) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₂
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₂)
  have g₁₃ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₃ + r₁ * r₃ ^ 2 + r₃ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) +
        3 * b₄ * (r₁ + r₃) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₃) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₃ + r₁ * r₃ ^ 2 + r₃ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) +
          3 * b₄ * (r₁ + r₃) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₃
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₃)
  have g₁₄ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₄ + r₁ * r₄ ^ 2 + r₄ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₄ + r₄ ^ 2) +
        3 * b₄ * (r₁ + r₄) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₄) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₄ + r₁ * r₄ ^ 2 + r₄ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₄ + r₄ ^ 2) +
          3 * b₄ * (r₁ + r₄) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₄
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₄)
  have q₁₂₃ :
      3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ +
        r₂ ^ 2 + r₂ * r₃ + r₃ ^ 2) +
        b₂ * (r₁ + r₂ + r₃) + 3 * b₄ = 0 := by
    have hfactor : (r₂ - r₃) * (
        3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ +
          r₂ ^ 2 + r₂ * r₃ + r₃ ^ 2) +
          b₂ * (r₁ + r₂ + r₃) + 3 * b₄) = 0 := by
      linear_combination g₁₂ - g₁₃
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₂₃)
  have q₁₂₄ :
      3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₄ +
        r₂ ^ 2 + r₂ * r₄ + r₄ ^ 2) +
        b₂ * (r₁ + r₂ + r₄) + 3 * b₄ = 0 := by
    have hfactor : (r₂ - r₄) * (
        3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₄ +
          r₂ ^ 2 + r₂ * r₄ + r₄ ^ 2) +
          b₂ * (r₁ + r₂ + r₄) + 3 * b₄) = 0 := by
      linear_combination g₁₂ - g₁₄
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₂₄)
  have hb₂ : b₂ = -3 * (r₁ + r₂ + r₃ + r₄) := by
    have hfactor : (r₃ - r₄) *
        (3 * (r₁ + r₂ + r₃ + r₄) + b₂) = 0 := by
      linear_combination q₁₂₃ - q₁₂₄
    have := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₃₄)
    linarith
  have hb₄ : b₄ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
      r₂ * r₃ + r₂ * r₄ + r₃ * r₄ := by
    have h := q₁₂₃
    rw [hb₂] at h
    linear_combination (1 : ℚ) / 3 * h
  have hb₆ : b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
      r₁ * r₃ * r₄ + r₂ * r₃ * r₄) := by
    have h := g₁₂
    rw [hb₂, hb₄] at h
    linear_combination (1 : ℚ) / 3 * h
  have hb₈ : b₈ = 3 * (r₁ * r₂ * r₃ * r₄) := by
    have h := h₁
    rw [hb₂, hb₄, hb₆] at h
    linear_combination h
  exact ⟨hb₂, hb₄, hb₆, hb₈⟩

lemma four_distinct_roots_invariant_impossible
    {b₂ b₄ b₆ b₈ r₁ r₂ r₃ r₄ : ℚ}
    (hne₁₂ : r₁ ≠ r₂) (hne₃₄ : r₃ ≠ r₄)
    (hb₂ : b₂ = -3 * (r₁ + r₂ + r₃ + r₄))
    (hb₄ : b₄ =
      r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄)
    (hb₆ : b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
      r₁ * r₃ * r₄ + r₂ * r₃ * r₄))
    (hb₈ : b₈ = 3 * (r₁ * r₂ * r₃ * r₄))
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) :
    False := by
  subst b₂
  subst b₄
  subst b₆
  subst b₈
  have hid :
      2 * (12 * (r₁ * r₂ * r₃ * r₄) -
          (-3 * (r₁ + r₂ + r₃ + r₄)) *
            (-(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
              r₁ * r₃ * r₄ + r₂ * r₃ * r₄)) +
          (r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
            r₂ * r₃ + r₂ * r₄ + r₃ * r₄) ^ 2) =
        ((r₁ - r₂) * (r₃ - r₄)) ^ 2 +
          ((r₁ - r₃) * (r₂ - r₄)) ^ 2 +
          ((r₁ - r₄) * (r₂ - r₃)) ^ 2 := by
    ring
  have hpair : (r₁ - r₂) * (r₃ - r₄) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hne₁₂) (sub_ne_zero.mpr hne₃₄)
  have hpos : 0 < ((r₁ - r₂) * (r₃ - r₄)) ^ 2 :=
    sq_pos_of_ne_zero hpair
  have hnonneg₁ : 0 ≤ ((r₁ - r₃) * (r₂ - r₄)) ^ 2 := sq_nonneg _
  have hnonneg₂ : 0 ≤ ((r₁ - r₄) * (r₂ - r₃)) ^ 2 := sq_nonneg _
  nlinarith

private lemma abscissa_ne_of_independent_images
    (W : WeierstrassCurve.Affine ℚ)
    (φ : (ZMod 3 × ZMod 3) →+ W.Point) (hφ : Function.Injective φ)
    {z w : ZMod 3 × ZMod 3} (hzw : z ≠ w) (hznegw : z ≠ -w)
    {xz yz xw yw : ℚ}
    {hz : W.Nonsingular xz yz} {hw : W.Nonsingular xw yw}
    (hPz : φ z = .some xz yz hz) (hPw : φ w = .some xw yw hw) :
    xz ≠ xw := by
  intro hx
  have hxrep :
      (WeierstrassCurve.Affine.Point.some xz yz hz).xRep =
        (WeierstrassCurve.Affine.Point.some xw yw hw).xRep := by
    simp [hx]
  rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
    with heq | heq
  · apply hzw
    exact hφ (hPz.trans (heq.trans hPw.symm))
  · apply hznegw
    apply hφ
    calc
      φ z = WeierstrassCurve.Affine.Point.some xz yz hz := hPz
      _ = -WeierstrassCurve.Affine.Point.some xw yw hw := heq
      _ = -φ w := congrArg Neg.neg hPw.symm
      _ = φ (-w) := (map_neg φ w).symm

/-- There is no full rational three-torsion subgroup on a Weierstrass curve
over `ℚ`. -/
theorem not_injective_zmod_three_square
    (E : WeierstrassCurve ℚ)
    (φ : (ZMod 3 × ZMod 3) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  let z₁ : ZMod 3 × ZMod 3 := (1, 0)
  let z₂ : ZMod 3 × ZMod 3 := (0, 1)
  let z₃ : ZMod 3 × ZMod 3 := (1, 1)
  let z₄ : ZMod 3 × ZMod 3 := (1, 2)
  let P₁ : (E⁄ℚ).Point := φ z₁
  let P₂ : (E⁄ℚ).Point := φ z₂
  let P₃ : (E⁄ℚ).Point := φ z₃
  let P₄ : (E⁄ℚ).Point := φ z₄
  have hthree (z : ZMod 3 × ZMod 3) : (3 : ℕ) • φ z = 0 := by
    have hz : (3 : ℕ) • z = 0 := by
      rcases z with ⟨a, b⟩
      apply Prod.ext
      · change (3 : ℕ) • a = 0
        rw [nsmul_eq_mul]
        rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
      · change (3 : ℕ) • b = 0
        rw [nsmul_eq_mul]
        rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
    rw [← map_nsmul, hz, map_zero]
  have hn₁ : P₁ ≠ 0 := by
    intro h
    exact (by decide : z₁ ≠ 0) (hφ (by simpa [P₁] using h))
  have hn₂ : P₂ ≠ 0 := by
    intro h
    exact (by decide : z₂ ≠ 0) (hφ (by simpa [P₂] using h))
  have hn₃ : P₃ ≠ 0 := by
    intro h
    exact (by decide : z₃ ≠ 0) (hφ (by simpa [P₃] using h))
  have hn₄ : P₄ ≠ 0 := by
    intro h
    exact (by decide : z₄ ≠ 0) (hφ (by simpa [P₄] using h))
  obtain ⟨r₁, y₁, hP₁, hP₁eq, hr₁⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₁ (hthree z₁) hn₁
  obtain ⟨r₂, y₂, hP₂, hP₂eq, hr₂⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₂ (hthree z₂) hn₂
  obtain ⟨r₃, y₃, hP₃, hP₃eq, hr₃⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₃ (hthree z₃) hn₃
  obtain ⟨r₄, y₄, hP₄, hP₄eq, hr₄⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₄ (hthree z₄) hn₄
  have hrepr₁ : φ z₁ = .some r₁ y₁ hP₁ := by simpa [P₁] using hP₁eq
  have hrepr₂ : φ z₂ = .some r₂ y₂ hP₂ := by simpa [P₂] using hP₂eq
  have hrepr₃ : φ z₃ = .some r₃ y₃ hP₃ := by simpa [P₃] using hP₃eq
  have hrepr₄ : φ z₄ = .some r₄ y₄ hP₄ := by simpa [P₄] using hP₄eq
  have hr₁₂ : r₁ ≠ r₂ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₂
  have hr₁₃ : r₁ ≠ r₃ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₃
  have hr₁₄ : r₁ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₄
  have hr₂₃ : r₂ ≠ r₃ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₂ hrepr₃
  have hr₂₄ : r₂ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₂ hrepr₄
  have hr₃₄ : r₃ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₃ hrepr₄
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat] at hr₁ hr₂ hr₃ hr₄
  obtain ⟨hb₂, hb₄, hb₆, hb₈⟩ :=
    quartic_coefficients_of_four_distinct_roots
      hr₁₂ hr₁₃ hr₁₄ hr₂₃ hr₂₄ hr₃₄ hr₁ hr₂ hr₃ hr₄
  exact four_distinct_roots_invariant_impossible hr₁₂ hr₃₄
    hb₂ hb₄ hb₆ hb₈ (E⁄ℚ).b_relation

end MazurTorsion.ThreeTorsion

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Discriminant obstructions to full odd-prime torsion

For an odd integer `n`, the nonzero `n`-torsion points modulo sign are the roots of the
univariate division polynomial `preΨ' n`. If all of those points are rational, that polynomial
splits over `ℚ`, so its discriminant is a rational square. For `n = 5` and `n = 7`, the classical
division-polynomial discriminant formula has respectively the shapes

* `5 ^ 11 * Δ ^ 22`, and
* `-(7 ^ 23 * Δ ^ 92)`.

Neither is a square when the curve discriminant `Δ` is nonzero. This file establishes the
polynomial and rational-arithmetic part of that argument. The two missing geometric identities
(the torsion/root equivalence and the division-polynomial discriminant formula) are intentionally
not postulated here.
-/

namespace MazurTorsion.OddPrimeFullTorsion

open Polynomial
open scoped WeierstrassCurve.Affine

private def derivativePairProduct (s : Multiset ℚ) : ℚ :=
  (s.map fun x ↦ ((s.erase x).map fun y ↦ x - y).prod).prod

private lemma derivativePairProduct_cons {a : ℚ} {s : Multiset ℚ} (ha : a ∉ s) :
    derivativePairProduct (a ::ₘ s) =
      (-1) ^ s.card * ((s.map fun x ↦ a - x).prod) ^ 2 *
        derivativePairProduct s := by
  have htail :
      (s.map fun x ↦ (((a ::ₘ s).erase x).map fun y ↦ x - y).prod).prod =
        (s.map fun x ↦ x - a).prod * derivativePairProduct s := by
    rw [derivativePairProduct, ← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    have hax : a ≠ x := by
      intro h
      apply ha
      simpa [h] using hx
    rw [Multiset.erase_cons_tail s hax]
    simp only [Multiset.map_cons, Multiset.prod_cons]
  have hreverse :
      (s.map fun x ↦ x - a).prod =
        (-1) ^ s.card * (s.map fun x ↦ a - x).prod := by
    calc
      (s.map fun x ↦ x - a).prod =
          ((s.map fun x ↦ a - x).map fun x ↦ -x).prod := by
            congr 1
            simp only [Multiset.map_map, Function.comp_apply]
            apply Multiset.map_congr rfl
            intro x _
            ring
      _ = (-1) ^ (s.map fun x ↦ a - x).card *
          (s.map fun x ↦ a - x).prod := Multiset.prod_map_neg _
      _ = (-1) ^ s.card * (s.map fun x ↦ a - x).prod := by simp
  rw [derivativePairProduct]
  simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.erase_cons_head]
  rw [htail, hreverse]
  ring

private lemma derivativePairProduct_isSquare (s : Multiset ℚ) :
    IsSquare
      ((-1) ^ (s.card * (s.card - 1) / 2) * derivativePairProduct s) := by
  induction s using Multiset.induction_on with
  | empty => simp [derivativePairProduct]
  | @cons a s ih =>
      by_cases ha : a ∈ s
      · have hzero : derivativePairProduct (a ::ₘ s) = 0 := by
          rw [derivativePairProduct]
          apply Multiset.prod_eq_zero
          apply Multiset.mem_map.mpr
          refine ⟨a, by simp, ?_⟩
          apply Multiset.prod_eq_zero
          apply Multiset.mem_map.mpr
          exact ⟨a, by simpa using ha, sub_self a⟩
        simp [hzero]
      · rw [derivativePairProduct_cons ha]
        rcases ih with ⟨z, hz⟩
        refine ⟨(s.map fun x ↦ a - x).prod * z, ?_⟩
        simp only [Multiset.card_cons]
        have hexponent : (s.card + 1) * (s.card + 1 - 1) / 2 =
            s.card + s.card * (s.card - 1) / 2 := by
          rw [← Nat.choose_two_right, ← Nat.choose_two_right]
          simp [Nat.choose_succ_succ]
        rw [hexponent, pow_add]
        have hsign : ((-1 : ℚ) ^ s.card) * (-1) ^ s.card = 1 := by
          rw [← pow_add]
          simp [← two_mul]
        calc
          (-1 : ℚ) ^ s.card * (-1) ^ (s.card * (s.card - 1) / 2) *
                ((-1) ^ s.card * (s.map fun x ↦ a - x).prod ^ 2 *
                  derivativePairProduct s) =
              ((-1 : ℚ) ^ s.card * (-1) ^ s.card) *
                ((s.map fun x ↦ a - x).prod ^ 2 *
                  ((-1) ^ (s.card * (s.card - 1) / 2) *
                    derivativePairProduct s)) := by ring
          _ = (s.map fun x ↦ a - x).prod ^ 2 *
                ((-1) ^ (s.card * (s.card - 1) / 2) *
                  derivativePairProduct s) := by
                    rw [hsign, one_mul]
          _ = (s.map fun x ↦ a - x).prod ^ 2 * (z * z) := by rw [hz]
          _ = (s.map fun x ↦ a - x).prod * z *
              ((s.map fun x ↦ a - x).prod * z) := by ring

private theorem isSquare_discr_of_splits_of_monic {f : ℚ[X]}
    (hf : f.Splits) (hm : f.Monic) :
    IsSquare f.discr := by
  by_cases hdegree : f.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hm hdegree]
    change IsSquare (Polynomial.discr (Polynomial.C (1 : ℚ)))
    rw [Polynomial.discr_C]
    exact IsSquare.one
  have hdegree_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hdegree
  have hresultant_discr :=
    Polynomial.resultant_deriv
      (Polynomial.natDegree_pos_iff_degree_pos.mp hdegree_pos)
  have hresultant_roots :=
    Polynomial.resultant_eq_prod_eval f f.derivative (f.natDegree - 1)
      f.natDegree_derivative_le hf
  simp only [hm.leadingCoeff, mul_one] at hresultant_discr
  simp only [hm.leadingCoeff, one_pow, one_mul] at hresultant_roots
  have hroot_product :
      (f.roots.map fun x ↦ Polynomial.eval x f.derivative).prod =
        derivativePairProduct f.roots := by
    rw [derivativePairProduct]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    exact hf.eval_root_derivative hm hx
  rw [hroot_product] at hresultant_roots
  have hpair :
      derivativePairProduct f.roots =
        (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr :=
    hresultant_roots.symm.trans hresultant_discr
  have hsquare := derivativePairProduct_isSquare f.roots
  rw [← hf.natDegree_eq_card_roots, hpair] at hsquare
  let k := f.natDegree * (f.natDegree - 1) / 2
  have hsign : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  have hcancel :
      (-1 : ℚ) ^ k * ((-1) ^ k * f.discr) = f.discr := by
    calc
      (-1 : ℚ) ^ k * ((-1) ^ k * f.discr) =
          ((-1) ^ k * (-1) ^ k) * f.discr := by ring
      _ = f.discr := by rw [hsign, one_mul]
  change IsSquare ((-1 : ℚ) ^ k * ((-1) ^ k * f.discr)) at hsquare
  rwa [hcancel] at hsquare

private lemma discr_C_mul {c : ℚ} (hc : c ≠ 0) {f : ℚ[X]}
    (hdegree : 0 < f.natDegree) :
    (Polynomial.C c * f).discr =
      c ^ (2 * f.natDegree - 2) * f.discr := by
  have hdegree' : 0 < f.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hdegree
  have hscaled_degree :
      (Polynomial.C c * f).natDegree = f.natDegree :=
    Polynomial.natDegree_C_mul hc
  have hscaled_degree' : 0 < (Polynomial.C c * f).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hscaled_degree]
    exact hdegree
  have hresultant := Polynomial.resultant_deriv hdegree'
  have hscaled_resultant := Polynomial.resultant_deriv hscaled_degree'
  rw [hscaled_degree, Polynomial.derivative_C_mul,
    Polynomial.resultant_C_mul_left, Polynomial.resultant_C_mul_right] at hscaled_resultant
  have hleading :
      (Polynomial.C c * f).leadingCoeff = c * f.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hscaled_degree, Polynomial.coeff_C_mul]
    rfl
  rw [hresultant, hleading] at hscaled_resultant
  have hpow :
      c ^ (f.natDegree - 1) * c ^ f.natDegree =
        c * c ^ (2 * f.natDegree - 2) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  let sign : ℚ := (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)
  have hcommon :
      sign * c * f.leadingCoeff *
          (c ^ (2 * f.natDegree - 2) * f.discr) =
        sign * c * f.leadingCoeff * (Polynomial.C c * f).discr := by
    dsimp [sign]
    calc
      (-1 : ℚ) ^ (f.natDegree * (f.natDegree - 1) / 2) * c *
            f.leadingCoeff * (c ^ (2 * f.natDegree - 2) * f.discr) =
          (c ^ (f.natDegree - 1) * c ^ f.natDegree) *
            ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
              f.leadingCoeff * f.discr) := by rw [hpow]; ring
      _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (c * f.leadingCoeff) * (Polynomial.C c * f).discr := by
            simpa only [mul_assoc] using hscaled_resultant
      _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * c *
          f.leadingCoeff * (Polynomial.C c * f).discr := by ring
  have hcommon_ne : sign * c * f.leadingCoeff ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc)
      (Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt hdegree))
  exact (mul_left_cancel₀ hcommon_ne hcommon).symm

/-- A polynomial over `ℚ` which splits completely has square discriminant.

This includes the repeated-root case, when the discriminant is zero. The result is the elementary
polynomial bridge used by the fixed-prime torsion obstruction below. -/
theorem isSquare_discr_of_splits {f : ℚ[X]} (hf : f.Splits) :
    IsSquare f.discr := by
  by_cases hdegree : f.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegree
    rw [← hc, Polynomial.discr_C]
    exact IsSquare.one
  have hdegree_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hdegree
  have hf_ne : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hdegree_pos
  have hlc : f.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hf_ne
  let g : ℚ[X] := Polynomial.C f.leadingCoeff⁻¹ * f
  have hg_monic : g.Monic := by
    simpa only [g, mul_comm] using Polynomial.monic_mul_leadingCoeff_inv hf_ne
  have hg_splits : g.Splits := hf.C_mul _
  have hg_square : IsSquare g.discr :=
    isSquare_discr_of_splits_of_monic hg_splits hg_monic
  have hg_degree : 0 < g.natDegree := by
    dsimp [g]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc)]
    exact hdegree_pos
  have hrecover : Polynomial.C f.leadingCoeff * g = f := by
    dsimp [g]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc,
      Polynomial.C_1, one_mul]
  have hscale := discr_C_mul hlc hg_degree
  rw [hrecover] at hscale
  have hscale_square :
      IsSquare (f.leadingCoeff ^ (2 * g.natDegree - 2)) := by
    refine ⟨f.leadingCoeff ^ (g.natDegree - 1), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  rw [hscale]
  exact hscale_square.mul hg_square

private theorem divisionPolynomial_splits_of_full_torsion
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {n d : ℕ} (hd : 0 < d)
    (representative : Fin d → ZMod n × ZMod n)
    (hrepresentative_ne : ∀ i, representative i ≠ 0)
    (hrepresentative_unique :
      ∀ i j, representative i = representative j ∨
        representative i = -representative j → i = j)
    (hrepresentative_torsion : ∀ i, n • representative i = 0)
    (hdegree : (W.preΨ' n).natDegree = d)
    (hroot :
      ∀ {x y : ℚ} (hP : W.toAffine.Nonsingular x y),
        n • WeierstrassCurve.Affine.Point.some x y hP = 0 →
          Polynomial.eval x (W.preΨ' n) = 0)
    (φ : (ZMod n × ZMod n) →+ W.toAffine.Point)
    (hφ : Function.Injective φ) :
    (W.preΨ' n).Splits := by
  have hpolynomial : W.preΨ' n ≠ 0 :=
    Polynomial.ne_zero_of_natDegree_gt (hdegree.symm ▸ hd)
  have himage_ne (i : Fin d) : φ (representative i) ≠ 0 := by
    intro hi
    apply hrepresentative_ne i
    apply hφ
    simpa using hi
  have haffine (i : Fin d) :
      ∃ x y : ℚ, ∃ hP : W.toAffine.Nonsingular x y,
        φ (representative i) =
          WeierstrassCurve.Affine.Point.some x y hP := by
    generalize hi : φ (representative i) = P
    cases P with
    | zero => exact (himage_ne i hi).elim
    | some x y hP => exact ⟨x, y, hP, rfl⟩
  choose x y hP hpoint using haffine
  have htorsion (i : Fin d) : n • φ (representative i) = 0 := by
    rw [← map_nsmul, hrepresentative_torsion i, map_zero]
  let rootMap : Fin d → {r // r ∈ (W.preΨ' n).rootSet ℚ} :=
    fun i ↦ ⟨x i, by
      rw [Polynomial.mem_rootSet_of_ne hpolynomial]
      simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      apply hroot (hP i)
      rw [← hpoint i]
      exact htorsion i⟩
  have hrootMap_injective : Function.Injective rootMap := by
    intro i j hij
    apply hrepresentative_unique
    have hx : x i = x j :=
      congrArg (fun r : {r // r ∈ (W.preΨ' n).rootSet ℚ} ↦ r.1) hij
    have hxrep :
        (φ (representative i)).xRep = (φ (representative j)).xRep := by
      rw [hpoint i, hpoint j]
      simp [hx]
    rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
      with heq | heq
    · exact Or.inl (hφ heq)
    · apply Or.inr
      apply hφ
      calc
        φ (representative i) = -φ (representative j) := heq
        _ = φ (-representative j) := (map_neg φ _).symm
  have hrootSet_lower :
      d ≤ Set.ncard ((W.preΨ' n).rootSet ℚ) := by
    have hcard :
        Nat.card (Fin d) ≤
          Nat.card {r // r ∈ (W.preΨ' n).rootSet ℚ} :=
      Nat.card_le_card_of_injective rootMap hrootMap_injective
    simpa only [Nat.card_fin, Nat.card_coe_set_eq] using hcard
  have hrootSet_roots :
      Set.ncard ((W.preΨ' n).rootSet ℚ) ≤ (W.preΨ' n).roots.card := by
    classical
    rw [Polynomial.rootSet_def, Set.ncard_coe_finset]
    simpa only [Polynomial.aroots_def, Algebra.algebraMap_self,
      Polynomial.map_id] using
        Multiset.toFinset_card_le (W.preΨ' n).roots
  rw [Polynomial.splits_iff_card_roots]
  apply le_antisymm
  · exact (W.preΨ' n).card_roots'
  · rw [hdegree]
    exact hrootSet_lower.trans hrootSet_roots

/-- The forward division-polynomial root criterion needed by the discriminant argument.

Mathlib currently defines the division polynomials but does not yet connect their evaluation to
scalar multiplication of affine points. -/
def HasDivisionPolynomialRootCriterion
    (W : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
  ∀ {x y : ℚ} (hP : W.toAffine.Nonsingular x y),
    n • WeierstrassCurve.Affine.Point.some x y hP = 0 →
      Polynomial.eval x (W.preΨ' n) = 0

private def fiveRepresentatives : Fin 12 → ZMod 5 × ZMod 5 :=
  ![(0, 1), (0, 2),
    (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]

private def sevenRepresentatives : Fin 24 → ZMod 7 × ZMod 7 :=
  ![(0, 1), (0, 2), (0, 3),
    (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6)]

/-- Full rational `5`-torsion makes the fifth division polynomial split, assuming only the
forward torsion/root criterion. -/
theorem fifth_division_polynomial_splits_of_full_torsion
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hroot : HasDivisionPolynomialRootCriterion W 5)
    (φ : (ZMod 5 × ZMod 5) →+ W.toAffine.Point)
    (hφ : Function.Injective φ) :
    (W.preΨ' 5).Splits := by
  have hdegree : (W.preΨ' 5).natDegree = 12 := by
    rw [W.natDegree_preΨ' (n := 5) (by norm_num)]
    norm_num [show ¬Even 5 by decide]
  exact divisionPolynomial_splits_of_full_torsion W
    (d := 12) (by norm_num) fiveRepresentatives
    (by decide) (by decide) (by decide) hdegree hroot φ hφ

/-- Full rational `7`-torsion makes the seventh division polynomial split, assuming only the
forward torsion/root criterion. -/
theorem seventh_division_polynomial_splits_of_full_torsion
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hroot : HasDivisionPolynomialRootCriterion W 7)
    (φ : (ZMod 7 × ZMod 7) →+ W.toAffine.Point)
    (hφ : Function.Injective φ) :
    (W.preΨ' 7).Splits := by
  have hdegree : (W.preΨ' 7).natDegree = 24 := by
    rw [W.natDegree_preΨ' (n := 7) (by norm_num)]
    norm_num [show ¬Even 7 by decide]
  exact divisionPolynomial_splits_of_full_torsion W
    (d := 24) (by norm_num) sevenRepresentatives
    (by decide) (by decide) (by decide) hdegree hroot φ hφ

private lemma nonsquare_mul_sq {a t : ℚ} (ha : ¬ IsSquare a) (ht : t ≠ 0) :
    ¬ IsSquare (a * t ^ 2) := by
  rintro ⟨q, hq⟩
  apply ha
  refine ⟨q / t, ?_⟩
  field_simp [ht]
  nlinarith [hq]

/-- The square class occurring in the discriminant of the fifth division polynomial is
nontrivial over `ℚ`. -/
theorem not_isSquare_five_discriminant_shape {Δ : ℚ} (hΔ : Δ ≠ 0) :
    ¬ IsSquare ((5 : ℚ) ^ 11 * Δ ^ 22) := by
  have hfive : ¬ IsSquare (5 : ℚ) := by
    intro h
    exact (by decide : Nat.Prime 5).not_isSquare
      (Rat.isSquare_natCast_iff.mp h)
  have ht : (5 : ℚ) ^ 5 * Δ ^ 11 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 5 (by norm_num)) (pow_ne_zero 11 hΔ)
  rw [show (5 : ℚ) ^ 11 * Δ ^ 22 = 5 * ((5 : ℚ) ^ 5 * Δ ^ 11) ^ 2 by ring]
  exact nonsquare_mul_sq hfive ht

/-- The square class occurring in the discriminant of the seventh division polynomial is
nontrivial over `ℚ`. -/
theorem not_isSquare_seven_discriminant_shape {Δ : ℚ} (hΔ : Δ ≠ 0) :
    ¬ IsSquare (-((7 : ℚ) ^ 23 * Δ ^ 92)) := by
  have hnegseven : ¬ IsSquare (-7 : ℚ) := by norm_num
  have ht : (7 : ℚ) ^ 11 * Δ ^ 46 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 11 (by norm_num)) (pow_ne_zero 46 hΔ)
  rw [show -((7 : ℚ) ^ 23 * Δ ^ 92) =
    -7 * ((7 : ℚ) ^ 11 * Δ ^ 46) ^ 2 by ring]
  exact nonsquare_mul_sq hnegseven ht

/-- A rational polynomial with the fifth-division discriminant shape cannot split over `ℚ`. -/
theorem not_splits_of_discr_eq_five_shape {f : ℚ[X]} {Δ : ℚ}
    (hΔ : Δ ≠ 0)
    (hdiscr : f.discr = (5 : ℚ) ^ 11 * Δ ^ 22) :
    ¬ f.Splits := by
  intro hsplits
  apply not_isSquare_five_discriminant_shape hΔ
  rw [← hdiscr]
  exact isSquare_discr_of_splits hsplits

/-- A rational polynomial with the seventh-division discriminant shape cannot split over `ℚ`. -/
theorem not_splits_of_discr_eq_seven_shape {f : ℚ[X]} {Δ : ℚ}
    (hΔ : Δ ≠ 0)
    (hdiscr : f.discr = -((7 : ℚ) ^ 23 * Δ ^ 92)) :
    ¬ f.Splits := by
  intro hsplits
  apply not_isSquare_seven_discriminant_shape hΔ
  rw [← hdiscr]
  exact isSquare_discr_of_splits hsplits

/-- The fifth division polynomial cannot split once its classical discriminant identity is
available. This isolates that identity as the only missing polynomial calculation. -/
theorem fifth_division_polynomial_not_splits_of_discr
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hdiscr :
      (W.preΨ' 5).discr = (5 : ℚ) ^ 11 * W.Δ ^ 22) :
    ¬ (W.preΨ' 5).Splits :=
  not_splits_of_discr_eq_five_shape W.isUnit_Δ.ne_zero hdiscr

/-- The seventh division polynomial cannot split once its classical discriminant identity is
available. This isolates that identity as the only missing polynomial calculation. -/
theorem seventh_division_polynomial_not_splits_of_discr
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hdiscr :
      (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92)) :
    ¬ (W.preΨ' 7).Splits :=
  not_splits_of_discr_eq_seven_shape W.isUnit_Δ.ne_zero hdiscr

/-- The exact full-rational-`5`-torsion obstruction obtained from the two missing
division-polynomial inputs. -/
theorem not_injective_zmod_five_square_of_division_inputs
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hroot : HasDivisionPolynomialRootCriterion W 5)
    (hdiscr :
      (W.preΨ' 5).discr = (5 : ℚ) ^ 11 * W.Δ ^ 22)
    (φ : (ZMod 5 × ZMod 5) →+ W.toAffine.Point) :
    ¬ Function.Injective φ := by
  intro hφ
  exact fifth_division_polynomial_not_splits_of_discr W hdiscr
    (fifth_division_polynomial_splits_of_full_torsion W hroot φ hφ)

/-- The exact full-rational-`7`-torsion obstruction obtained from the two missing
division-polynomial inputs. -/
theorem not_injective_zmod_seven_square_of_division_inputs
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hroot : HasDivisionPolynomialRootCriterion W 7)
    (hdiscr :
      (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92))
    (φ : (ZMod 7 × ZMod 7) →+ W.toAffine.Point) :
    ¬ Function.Injective φ := by
  intro hφ
  exact seventh_division_polynomial_not_splits_of_discr W hdiscr
    (seventh_division_polynomial_splits_of_full_torsion W hroot φ hφ)

end MazurTorsion.OddPrimeFullTorsion

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Division-polynomial roots from scalar multiplication

This file proves the forward division-polynomial root criterion at `5` and `7`. The proof uses
only the affine group law and the first few univariate division polynomials.
-/

namespace MazurTorsion.DivisionPolynomialRootCriterion

open Polynomial
open scoped WeierstrassCurve.Affine

private lemma exists_coordinates_of_ne_zero
    (W : WeierstrassCurve ℚ) (P : W.toAffine.Point)
    (hP : P ≠ 0) :
    ∃ x y, ∃ h : W.toAffine.Nonsingular x y,
      P = WeierstrassCurve.Affine.Point.some x y h := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h => exact ⟨x, y, h, rfl⟩

private lemma double_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) :
    Polynomial.eval x (W.Φ 2) =
      x₂ * Polynomial.eval x (W.ΨSq 2) := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP₂ hdouble.symm
  let slope := W.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
  have hx₂ : W.toAffine.addX x x slope = x₂ := by
    have hsum :
        WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP =
          WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
      simpa [two_nsmul] using hdouble
    exact (WeierstrassCurve.Affine.Point.some.inj
      (hadd.symm.trans hsum)).1
  have hden : y - W.toAffine.negY x y =
      2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hden_ne : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [← hden]
    exact sub_ne_zero.mpr hy
  have hslope :
      slope =
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
          (2 * y + W.a₁ * x + W.a₃) := by
    dsimp [slope]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hden]
  have hslope_mul :
      slope * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hslope, div_mul_cancel₀ _ hden_ne]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hD :
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        Polynomial.eval x (W.ΨSq 2) := by
    simp only [WeierstrassCurve.ΨSq_two, WeierstrassCurve.Ψ₂Sq,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hcurve
  have hψ₃ :=
    ThreeTorsion.three_division_tangent_identity hcurve hslope_mul
  have hx₂' : slope ^ 2 + W.a₁ * slope - W.a₂ - 2 * x = x₂ := by
    simp only [WeierstrassCurve.Affine.addX] at hx₂
    linear_combination hx₂
  have hψ₃eval :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) := by
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination hψ₃
  have hΦ :
      Polynomial.eval x (W.Φ 2) =
        x * Polynomial.eval x (W.ΨSq 2) -
          Polynomial.eval x W.Ψ₃ := by
    simp only [WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  calc
    Polynomial.eval x (W.Φ 2) =
        x * Polynomial.eval x (W.ΨSq 2) -
          Polynomial.eval x W.Ψ₃ := hΦ
    _ = x * Polynomial.eval x (W.ΨSq 2) +
        (2 * y + W.a₁ * x + W.a₃) ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) := by
            rw [hψ₃eval]
            ring
    _ = x * Polynomial.eval x (W.ΨSq 2) +
        Polynomial.eval x (W.ΨSq 2) * (x₂ - x) := by
            rw [hD]
            linear_combination
              Polynomial.eval x (W.ΨSq 2) * hx₂'
    _ = x₂ * Polynomial.eval x (W.ΨSq 2) := by ring

private lemma preΨ_four_double_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) :
    Polynomial.eval x W.preΨ₄ =
      (2 * y + W.a₁ * x + W.a₃) ^ 3 *
        (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP₂ hdouble.symm
  let slope := W.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
  have hsum :
      WeierstrassCurve.Affine.Point.some x y hP +
          WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    simpa [two_nsmul] using hdouble
  have hcoords :=
    WeierstrassCurve.Affine.Point.some.inj (hadd.symm.trans hsum)
  have hx₂ : slope ^ 2 + W.a₁ * slope - W.a₂ - 2 * x = x₂ := by
    have hx := hcoords.1
    simp only [WeierstrassCurve.Affine.addX] at hx
    linear_combination hx
  have hy₂ :
      y₂ = -(slope * (x₂ - x) + y) - W.a₁ * x₂ - W.a₃ := by
    have hycoord := hcoords.2
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY] at hycoord
    rw [hcoords.1] at hycoord
    change
      -(slope * (x₂ - x) + y) - W.a₁ * x₂ - W.a₃ = y₂
      at hycoord
    exact hycoord.symm
  have hden : y - W.toAffine.negY x y =
      2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hslope_mul :
      slope * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    dsimp [slope]
    rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
      div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hψ :=
    ThreeTorsion.three_division_tangent_identity hcurve hslope_mul
  have hψeval :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 * (x₂ - x) := by
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination hψ -
      (2 * y + W.a₁ * x + W.a₃) ^ 2 * hx₂
  have hvertical :
      2 * y₂ + W.a₁ * x₂ + W.a₃ =
        -(2 * slope + W.a₁) * (x₂ - x) -
          (2 * y + W.a₁ * x + W.a₃) := by
    linear_combination 2 * hy₂
  have hpre :
      Polynomial.eval x W.preΨ₄ =
        (2 * y + W.a₁ * x + W.a₃) *
            (2 * slope + W.a₁) * Polynomial.eval x W.Ψ₃ -
          (2 * y + W.a₁ * x + W.a₃) ^ 4 := by
    simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃,
      Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination
      -2 * (3 * x ^ 4 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 3 +
        3 * (W.a₁ * W.a₃ + 2 * W.a₄) * x ^ 2 +
        3 * (W.a₃ ^ 2 + 4 * W.a₆) * x +
        (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ -
          W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 -
          W.a₄ ^ 2)) * hslope_mul +
      8 * ((2 * y + W.a₁ * x + W.a₃) ^ 2 -
        2 * (y ^ 2 + W.a₁ * x * y + W.a₃ * y -
          (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))) * hcurve
  calc
    Polynomial.eval x W.preΨ₄ =
        (2 * y + W.a₁ * x + W.a₃) *
            (2 * slope + W.a₁) * Polynomial.eval x W.Ψ₃ -
          (2 * y + W.a₁ * x + W.a₃) ^ 4 := hpre
    _ = (2 * y + W.a₁ * x + W.a₃) ^ 3 *
        (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
          rw [hψeval, hvertical]
          ring

private lemma two_cross_identity
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    Polynomial.eval x (W.Φ 2) =
      x * Polynomial.eval x (W.ΨSq 2) -
        Polynomial.eval x W.Ψ₃ := by
  simp only [WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private lemma triple_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ x₃ y₃ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₃ : W.toAffine.Nonsingular x₃ y₃)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂)
    (htriple :
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃) :
    Polynomial.eval x (W.Φ 3) =
      x₃ * Polynomial.eval x (W.ΨSq 3) := by
  let P := WeierstrassCurve.Affine.Point.some x y hP
  let P₂ := WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have hx : x ≠ x₂ := by
    intro hx
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hx with heq | heq
    · apply hP_ne
      have htwice : (2 : ℕ) • P = P :=
        hdouble.trans heq.symm
      rw [two_nsmul] at htwice
      have hcancel : P + P = P + 0 := by
        exact htwice.trans (add_zero P).symm
      exact add_left_cancel hcancel
    · have hneg : P = -((2 : ℕ) • P) := by
        rw [hdouble]
        exact heq
      have hzero : (3 : ℕ) • P = 0 := by
        have hsum : P + (2 : ℕ) • P = 0 :=
          (add_eq_zero_iff_eq_neg).2 hneg
        rw [show (3 : ℕ) = 1 + 2 by norm_num,
          add_nsmul, one_nsmul]
        exact hsum
      change (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ at htriple
      rw [hzero] at htriple
      exact WeierstrassCurve.Affine.Point.some_ne_zero hP₃
        htriple.symm
  have hadd :
      P + P₂ = WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ := by
    change
      WeierstrassCurve.Affine.Point.some x y hP +
          WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃
    rw [← hdouble]
    rw [← htriple]
    rw [show (3 : ℕ) = 1 + 2 by norm_num,
      add_nsmul, one_nsmul]
  have hadd_formula :=
    WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := W.toAffine) (h₁ := hP) (h₂ := hP₂) hx
  have hx_add :
      W.toAffine.addX x x₂ (W.toAffine.slope x x₂ y y₂) = x₃ :=
    (WeierstrassCurve.Affine.Point.some.inj
      (hadd_formula.symm.trans hadd)).1
  have hsub :
      P + (-P₂) = -P := by
    change
      WeierstrassCurve.Affine.Point.some x y hP +
          (-WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) =
        -WeierstrassCurve.Affine.Point.some x y hP
    rw [← hdouble]
    rw [two_nsmul]
    abel
  have hP₂neg :
      W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) :=
    (W.toAffine.nonsingular_neg x₂ y₂).mpr hP₂
  have hsub_formula :=
    WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := W.toAffine) (h₁ := hP) (h₂ := hP₂neg) hx
  have hx_sub :
      W.toAffine.addX x x₂
          (W.toAffine.slope x x₂ y (W.toAffine.negY x₂ y₂)) = x := by
    have heq := hsub_formula.symm.trans hsub
    exact (WeierstrassCurve.Affine.Point.some.inj heq).1
  have haddX :=
    W.toAffine.addX_eq_addX_negY_sub y y₂ hx
  rw [hx_add, hx_sub] at haddX
  have hvertical :
      y - W.toAffine.negY x y =
        2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hvertical₂ :
      y₂ - W.toAffine.negY x₂ y₂ =
        2 * y₂ + W.a₁ * x₂ + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  rw [hvertical, hvertical₂] at haddX
  have hden_ne : x₂ - x ≠ 0 :=
    sub_ne_zero.mpr hx.symm
  have hsecant :
      (x₂ - x) ^ 2 * (x - x₃) =
        (2 * y + W.a₁ * x + W.a₃) *
          (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
    field_simp [hden_ne] at haddX
    linear_combination -haddX
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hD :
      Polynomial.eval x (W.ΨSq 2) =
        (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    simp only [WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination -4 * hcurve
  have hA :=
    double_abscissa_formula W hP hP₂ hdouble
  have htwo := two_cross_identity W x
  have hψ :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 * (x₂ - x) := by
    linear_combination htwo - hA -
      (x₂ - x) * hD
  have hpre :=
    preΨ_four_double_formula W hP hP₂ hdouble
  have hD₂ :
      Polynomial.eval x W.Ψ₂Sq =
        (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    simpa only [WeierstrassCurve.ΨSq_two] using hD
  simp only [WeierstrassCurve.Φ_three,
    WeierstrassCurve.ΨSq_three, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hpre, hD₂, hψ]
  linear_combination
    (2 * y + W.a₁ * x + W.a₃) ^ 4 * hsecant

private lemma four_Φ_composition
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    let A := Polynomial.eval x (W.Φ 2)
    let D := Polynomial.eval x (W.ΨSq 2)
    Polynomial.eval x (W.Φ 4) =
      A ^ 4 - W.b₄ * A ^ 2 * D ^ 2 -
        2 * W.b₆ * A * D ^ 3 - W.b₈ * D ^ 4 := by
  dsimp
  simp only [WeierstrassCurve.Φ_four, WeierstrassCurve.Φ_two,
    WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private lemma four_ΨSq_composition
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    let A := Polynomial.eval x (W.Φ 2)
    let D := Polynomial.eval x (W.ΨSq 2)
    Polynomial.eval x (W.ΨSq 4) =
      4 * A ^ 3 * D + W.b₂ * A ^ 2 * D ^ 2 +
        2 * W.b₄ * A * D ^ 3 + W.b₆ * D ^ 4 := by
  dsimp
  simp only [WeierstrassCurve.ΨSq_four,
    WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.preΨ₄,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private lemma quadruple_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ x₄ y₄ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₄ : W.toAffine.Nonsingular x₄ y₄)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂)
    (hdouble₂ :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄) :
    Polynomial.eval x (W.Φ 4) =
      x₄ * Polynomial.eval x (W.ΨSq 4) := by
  have hA :=
    double_abscissa_formula W hP hP₂ hdouble
  have hA₂ :=
    double_abscissa_formula W hP₂ hP₄ hdouble₂
  have hΦ :
      Polynomial.eval x (W.Φ 4) =
        Polynomial.eval x (W.ΨSq 2) ^ 4 *
          Polynomial.eval x₂ (W.Φ 2) := by
    rw [four_Φ_composition]
    rw [hA]
    simp only [WeierstrassCurve.Φ_two, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  have hΨ :
      Polynomial.eval x (W.ΨSq 4) =
        Polynomial.eval x (W.ΨSq 2) ^ 4 *
          Polynomial.eval x₂ (W.ΨSq 2) := by
    rw [four_ΨSq_composition]
    rw [hA]
    simp only [WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [hΦ, hA₂, hΨ]
  ring

private lemma five_cross_identity
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    Polynomial.eval x (W.Φ 4) =
      x * Polynomial.eval x (W.ΨSq 4) -
        Polynomial.eval x W.Ψ₃ *
          Polynomial.eval x (W.preΨ' 5) := by
  have hpre :
      W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
      W.preΨ'_odd 0]
    norm_num
  rw [hpre]
  simp only [WeierstrassCurve.Φ_four,
    WeierstrassCurve.ΨSq_four, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  ring

private lemma seven_cross_identity
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    Polynomial.eval x (W.Φ 4) *
          Polynomial.eval x (W.ΨSq 3) -
        Polynomial.eval x (W.Φ 3) *
          Polynomial.eval x (W.ΨSq 4) =
      -Polynomial.eval x (W.preΨ' 7) := by
  have hfive :
      W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
      W.preΨ'_odd 0]
    norm_num
  have hseven :
      W.preΨ' 7 =
        (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) * W.Ψ₃ ^ 3 -
          W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2 := by
    rw [show (7 : ℕ) = 2 * (1 + 2) + 1 by norm_num,
      W.preΨ'_odd 1]
    norm_num [hfive]
  rw [hseven]
  simp only [WeierstrassCurve.Φ_four,
    WeierstrassCurve.Φ_three, WeierstrassCurve.ΨSq_four,
    WeierstrassCurve.ΨSq_three, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- The forward fifth-division-polynomial root criterion over `ℚ`. -/
theorem hasDivisionPolynomialRootCriterion_five
    (W : WeierstrassCurve ℚ) :
    OddPrimeFullTorsion.HasDivisionPolynomialRootCriterion W 5 := by
  intro x y hP hfive
  let P := WeierstrassCurve.Affine.Point.some x y hP
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have htwo_ne : (2 : ℕ) • P ≠ 0 := by
    intro htwo
    apply hP_ne
    have hsplit :
        (5 : ℕ) • P = (2 : ℕ) • P + (2 : ℕ) • P + P := by
      rw [show (5 : ℕ) = 2 + 2 + 1 by norm_num,
        add_nsmul, add_nsmul, one_nsmul]
    change (5 : ℕ) • P = 0 at hfive
    rw [hsplit, htwo, zero_add, zero_add] at hfive
    exact hfive
  have hfour_ne : (4 : ℕ) • P ≠ 0 := by
    intro hfour
    apply hP_ne
    have hsplit : (5 : ℕ) • P = (4 : ℕ) • P + P := by
      rw [show (5 : ℕ) = 4 + 1 by norm_num,
        add_nsmul, one_nsmul]
    change (5 : ℕ) • P = 0 at hfive
    rw [hsplit, hfour, zero_add] at hfive
    exact hfive
  obtain ⟨x₂, y₂, hP₂, hdouble⟩ :=
    exists_coordinates_of_ne_zero W ((2 : ℕ) • P) htwo_ne
  obtain ⟨x₄, y₄, hP₄, hfour⟩ :=
    exists_coordinates_of_ne_zero W ((4 : ℕ) • P) hfour_ne
  have hdouble₂ :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ := by
    rw [← hdouble, ← hfour, ← mul_nsmul]
  have hfour_neg : (4 : ℕ) • P = -P := by
    apply (add_eq_zero_iff_eq_neg).mp
    have hsplit : (5 : ℕ) • P = (4 : ℕ) • P + P := by
      rw [show (5 : ℕ) = 4 + 1 by norm_num,
        add_nsmul, one_nsmul]
    rw [← hsplit]
    exact hfive
  have hx₄ : x₄ = x := by
    have heq :
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ = -P :=
      hfour.symm.trans hfour_neg
    exact (WeierstrassCurve.Affine.Point.some.inj heq).1
  have hcoordinate :=
    quadruple_abscissa_formula W hP hP₂ hP₄ hdouble hdouble₂
  rw [hx₄] at hcoordinate
  have hψ₃_ne : Polynomial.eval x W.Ψ₃ ≠ 0 := by
    intro hψ₃
    have hthree :
        (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 :=
      (ThreeTorsion.three_nsmul_some_eq_zero_iff W hP).2 hψ₃
    apply htwo_ne
    have hsplit :
        (5 : ℕ) • P = (3 : ℕ) • P + (2 : ℕ) • P := by
      rw [show (5 : ℕ) = 3 + 2 by norm_num, add_nsmul]
    change (3 : ℕ) • P = 0 at hthree
    change (5 : ℕ) • P = 0 at hfive
    rw [hsplit, hthree, zero_add] at hfive
    exact hfive
  have hcross := five_cross_identity W x
  have hproduct :
      Polynomial.eval x W.Ψ₃ *
        Polynomial.eval x (W.preΨ' 5) = 0 := by
    linear_combination hcross - hcoordinate
  exact (mul_eq_zero.mp hproduct).resolve_left hψ₃_ne

/-- The forward seventh-division-polynomial root criterion over `ℚ`. -/
theorem hasDivisionPolynomialRootCriterion_seven
    (W : WeierstrassCurve ℚ) :
    OddPrimeFullTorsion.HasDivisionPolynomialRootCriterion W 7 := by
  intro x y hP hseven
  let P := WeierstrassCurve.Affine.Point.some x y hP
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have htwo_ne : (2 : ℕ) • P ≠ 0 := by
    intro htwo
    apply hP_ne
    have hsplit :
        (7 : ℕ) • P =
          (2 : ℕ) • P + (2 : ℕ) • P + (2 : ℕ) • P + P := by
      rw [show (7 : ℕ) = 2 + 2 + 2 + 1 by norm_num,
        add_nsmul, add_nsmul, add_nsmul, one_nsmul]
    change (7 : ℕ) • P = 0 at hseven
    rw [hsplit, htwo, zero_add, zero_add, zero_add] at hseven
    exact hseven
  have hthree_ne : (3 : ℕ) • P ≠ 0 := by
    intro hthree
    apply hP_ne
    have hsplit :
        (7 : ℕ) • P = (3 : ℕ) • P + (3 : ℕ) • P + P := by
      rw [show (7 : ℕ) = 3 + 3 + 1 by norm_num,
        add_nsmul, add_nsmul, one_nsmul]
    change (7 : ℕ) • P = 0 at hseven
    rw [hsplit, hthree, zero_add, zero_add] at hseven
    exact hseven
  have hfour_ne : (4 : ℕ) • P ≠ 0 := by
    intro hfour
    apply hP_ne
    have hsplitSeven :
        (7 : ℕ) • P = (4 : ℕ) • P + (3 : ℕ) • P := by
      rw [show (7 : ℕ) = 4 + 3 by norm_num, add_nsmul]
    have hthree : (3 : ℕ) • P = 0 := by
      change (7 : ℕ) • P = 0 at hseven
      rw [hsplitSeven, hfour, zero_add] at hseven
      exact hseven
    have hsplitFour :
        (4 : ℕ) • P = (3 : ℕ) • P + P := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num,
        add_nsmul, one_nsmul]
    rw [hsplitFour, hthree, zero_add] at hfour
    exact hfour
  obtain ⟨x₂, y₂, hP₂, hdouble⟩ :=
    exists_coordinates_of_ne_zero W ((2 : ℕ) • P) htwo_ne
  obtain ⟨x₃, y₃, hP₃, htriple⟩ :=
    exists_coordinates_of_ne_zero W ((3 : ℕ) • P) hthree_ne
  obtain ⟨x₄, y₄, hP₄, hfour⟩ :=
    exists_coordinates_of_ne_zero W ((4 : ℕ) • P) hfour_ne
  have hdouble₂ :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ := by
    rw [← hdouble, ← hfour, ← mul_nsmul]
  have hfour_neg_three :
      (4 : ℕ) • P = -((3 : ℕ) • P) := by
    apply (add_eq_zero_iff_eq_neg).mp
    have hsplit :
        (7 : ℕ) • P = (4 : ℕ) • P + (3 : ℕ) • P := by
      rw [show (7 : ℕ) = 4 + 3 by norm_num, add_nsmul]
    rw [← hsplit]
    exact hseven
  have hx₄₃ : x₄ = x₃ := by
    have heq :
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ =
          -WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ := by
      rw [← hfour, ← htriple]
      exact hfour_neg_three
    exact (WeierstrassCurve.Affine.Point.some.inj heq).1
  have hcoordinate₃ :=
    triple_abscissa_formula W hP hP₂ hP₃ hdouble htriple
  have hcoordinate₄ :=
    quadruple_abscissa_formula W hP hP₂ hP₄ hdouble hdouble₂
  have hleft :
      Polynomial.eval x (W.Φ 4) *
            Polynomial.eval x (W.ΨSq 3) -
          Polynomial.eval x (W.Φ 3) *
            Polynomial.eval x (W.ΨSq 4) = 0 := by
    rw [hcoordinate₄, hcoordinate₃, hx₄₃]
    ring
  have hcross := seven_cross_identity W x
  linear_combination hcross - hleft

end MazurTorsion.DivisionPolynomialRootCriterion

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Discriminant of the seventh division polynomial

This file computes the discriminant of the universal seventh division polynomial over
`ℚ`. A sparse degree-twenty auxiliary polynomial reduces all high-degree resultants to
two low-degree resultants. A translation then removes the `b₂ = 0` normalization.
-/

open Polynomial

namespace MazurTorsion.DivisionPolynomialDiscriminantSeven

private noncomputable def D (a b : ℚ) : ℚ[X] :=
  4 * X ^ 3 + 4 * C a * X + 4 * C b

private noncomputable def S (a : ℚ) : ℚ[X] :=
  6 * X ^ 2 + 2 * C a

private noncomputable def q (a b : ℚ) : ℚ[X] :=
  3 * X ^ 4 + 6 * C a * X ^ 2 + 12 * C b * X - C a ^ 2

private noncomputable def r (a b : ℚ) : ℚ[X] :=
  2 * X ^ 6 + 10 * C a * X ^ 4 + 40 * C b * X ^ 3 -
    10 * C a ^ 2 * X ^ 2 - 8 * C a * C b * X -
    (2 * C a ^ 3 + 16 * C b ^ 2)

private noncomputable def p (u v : ℚ) : ℚ[X] :=
  r u v * D u v ^ 2 - q u v ^ 3

private noncomputable def s (u v : ℚ) : ℚ[X] :=
  p u v * q u v ^ 3 - r u v ^ 3 * D u v ^ 2

private noncomputable def h (u v : ℚ) : ℚ[X] :=
  D u v * (r u v).derivative - 5 * q u v ^ 2

private noncomputable def J (u v : ℚ) : ℚ[X] :=
  (2 * p u v - 5 * r u v ^ 2) * q u v ^ 2 +
    r u v ^ 2 * (D u v * (r u v).derivative - r u v * (D u v).derivative)

private def delta (a b : ℚ) : ℚ := 16 * (4 * a ^ 3 + 27 * b ^ 2)

private lemma natDegree_D (u v : ℚ) : (D u v).natDegree = 3 := by
  unfold D
  compute_degree!

private lemma natDegree_S (u : ℚ) : (S u).natDegree = 2 := by
  unfold S
  compute_degree!

private lemma natDegree_q (u v : ℚ) : (q u v).natDegree = 4 := by
  unfold q
  compute_degree!

private lemma natDegree_r (u v : ℚ) : (r u v).natDegree = 6 := by
  unfold r
  compute_degree!

private lemma leadingCoeff_D (u v : ℚ) : (D u v).leadingCoeff = 4 := by
  rw [leadingCoeff, natDegree_D]
  simp [D]

private lemma leadingCoeff_q (u v : ℚ) : (q u v).leadingCoeff = 3 := by
  rw [leadingCoeff, natDegree_q]
  unfold q
  compute_degree!

private lemma leadingCoeff_r (u v : ℚ) : (r u v).leadingCoeff = 2 := by
  rw [leadingCoeff, natDegree_r]
  unfold r
  compute_degree!

private lemma natDegree_p (u v : ℚ) : (p u v).natDegree = 12 := by
  have hr : r u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r u v).natDegree by rw [natDegree_r]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have hq : q u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q u v).natDegree by rw [natDegree_q]; norm_num)
  have h₁ : (r u v * D u v ^ 2).natDegree = 12 := by
    rw [natDegree_mul hr (pow_ne_zero 2 hD), natDegree_pow, natDegree_r, natDegree_D]
  have h₂ : (q u v ^ 3).natDegree = 12 := by
    rw [natDegree_pow, natDegree_q]
  rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)]
  rw [p, sub_eq_add_neg, degree_add_eq_of_leadingCoeff_add_ne_zero]
  · rw [degree_neg, (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₁,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₂]
    simp
  · rw [leadingCoeff_neg, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow,
      leadingCoeff_r, leadingCoeff_D, leadingCoeff_q]
    norm_num

private lemma leadingCoeff_p (u v : ℚ) : (p u v).leadingCoeff = 5 := by
  have hr : r u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r u v).natDegree by rw [natDegree_r]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have hq : q u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q u v).natDegree by rw [natDegree_q]; norm_num)
  have hdeg :
      (r u v * D u v ^ 2).degree = (q u v ^ 3).degree := by
    rw [degree_mul, degree_pow, degree_pow,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 6)).mpr (natDegree_r u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)).mpr (natDegree_D u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 4)).mpr (natDegree_q u v)]
    norm_num
  rw [p, leadingCoeff_sub_of_degree_eq hdeg]
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow,
      leadingCoeff_r, leadingCoeff_D, leadingCoeff_q]
    norm_num
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow,
      leadingCoeff_r, leadingCoeff_D, leadingCoeff_q]
    norm_num

private lemma natDegree_s (u v : ℚ) : (s u v).natDegree = 24 := by
  have hp : p u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (p u v).natDegree by rw [natDegree_p]; norm_num)
  have hq : q u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q u v).natDegree by rw [natDegree_q]; norm_num)
  have hr : r u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r u v).natDegree by rw [natDegree_r]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have h₁ : (p u v * q u v ^ 3).natDegree = 24 := by
    rw [natDegree_mul hp (pow_ne_zero 3 hq), natDegree_pow, natDegree_p, natDegree_q]
  have h₂ : (r u v ^ 3 * D u v ^ 2).natDegree = 24 := by
    rw [natDegree_mul (pow_ne_zero 3 hr) (pow_ne_zero 2 hD),
      natDegree_pow, natDegree_pow, natDegree_r, natDegree_D]
  rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 24)]
  rw [s, sub_eq_add_neg, degree_add_eq_of_leadingCoeff_add_ne_zero]
  · rw [degree_neg, (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 24)).mpr h₁,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 24)).mpr h₂]
    simp
  · rw [leadingCoeff_neg, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_pow, leadingCoeff_p, leadingCoeff_q,
      leadingCoeff_r, leadingCoeff_D]
    norm_num

private lemma leadingCoeff_s (u v : ℚ) : (s u v).leadingCoeff = 7 := by
  have hp : p u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (p u v).natDegree by rw [natDegree_p]; norm_num)
  have hq : q u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q u v).natDegree by rw [natDegree_q]; norm_num)
  have hr : r u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r u v).natDegree by rw [natDegree_r]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have hdeg :
      (p u v * q u v ^ 3).degree = (r u v ^ 3 * D u v ^ 2).degree := by
    rw [degree_mul, degree_mul,
      degree_pow, degree_pow, degree_pow,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr (natDegree_p u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 4)).mpr (natDegree_q u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 6)).mpr (natDegree_r u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)).mpr (natDegree_D u v)]
    norm_num
  rw [s, leadingCoeff_sub_of_degree_eq hdeg]
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_pow, leadingCoeff_p, leadingCoeff_q, leadingCoeff_r, leadingCoeff_D]
    norm_num
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_pow, leadingCoeff_p, leadingCoeff_q, leadingCoeff_r, leadingCoeff_D]
    norm_num

private lemma natDegree_p_sub_r_sq (a b : ℚ) :
    (p a b - r a b ^ 2).natDegree = 12 := by
  have hp : p a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (p a b).natDegree by rw [natDegree_p]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have h₁ : (p a b).natDegree = 12 := natDegree_p a b
  have h₂ : (r a b ^ 2).natDegree = 12 := by
    rw [natDegree_pow, natDegree_r]
  rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)]
  rw [sub_eq_add_neg, degree_add_eq_of_leadingCoeff_add_ne_zero]
  · rw [degree_neg, (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₁,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₂]
    simp
  · rw [leadingCoeff_neg, leadingCoeff_pow, leadingCoeff_p, leadingCoeff_r]
    norm_num

private lemma derivative_D (u v : ℚ) : (D u v).derivative = 2 * S u := by
  simp [D, S, derivative_add, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma derivative_q (u v : ℚ) : (q u v).derivative = 3 * D u v := by
  simp [q, D, derivative_add, derivative_sub, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma q_identity (u v : ℚ) :
    4 * q u v = 12 * X * D u v - S u ^ 2 := by
  simp [q, D, S]
  ring

private lemma r_identity (u v : ℚ) :
    r u v + D u v ^ 2 = q u v * S u := by
  simp [r, D, q, S]
  ring

private lemma h_identity (u v : ℚ) :
    h u v = r u v * S u - q u v ^ 2 := by
  simp [h, r, D, q, S, derivative_add, derivative_sub, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma p_h_identity (u v : ℚ) :
    p u v + r u v ^ 2 = h u v * q u v := by
  rw [p, h_identity]
  calc
    (r u v * D u v ^ 2 - q u v ^ 3) + r u v ^ 2 =
        r u v * (r u v + D u v ^ 2) - q u v ^ 3 := by ring
    _ = r u v * (q u v * S u) - q u v ^ 3 := by rw [r_identity]
    _ = (r u v * S u - q u v ^ 2) * q u v := by ring

private lemma h_derivative_identity (u v : ℚ) :
    D u v * (r u v).derivative = h u v + 5 * q u v ^ 2 := by
  simp [h]

private lemma J_simple_identity (u v : ℚ) :
    J u v = 2 * p u v * q u v ^ 2 -
      r u v ^ 3 * S u - r u v ^ 2 * q u v ^ 2 := by
  rw [J, derivative_D, h_derivative_identity, h_identity]
  ring

private lemma derivative_p (u v : ℚ) :
    (p u v).derivative = 5 * D u v * h u v := by
  rw [p, derivative_sub, derivative_mul, derivative_pow, derivative_pow,
    derivative_D, derivative_q]
  calc
    (r u v).derivative * D u v ^ 2 +
        r u v * (2 * D u v ^ 1 * (2 * S u)) -
        3 * q u v ^ 2 * (3 * D u v) =
      D u v * (D u v * (r u v).derivative +
        4 * r u v * S u - 9 * q u v ^ 2) := by ring
    _ = 5 * D u v * h u v := by
      rw [h_derivative_identity, h_identity]
      ring

private lemma derivative_s (u v : ℚ) :
    (s u v).derivative = 7 * D u v * J u v := by
  rw [s, derivative_sub, derivative_mul, derivative_pow, derivative_mul,
    derivative_pow, derivative_pow, derivative_p, derivative_q, derivative_D,
    J_simple_identity]
  calc
    5 * D u v * h u v * q u v ^ 3 +
        p u v * (3 * q u v ^ 2 * (3 * D u v)) -
        (3 * r u v ^ 2 * (r u v).derivative * D u v ^ 2 +
          r u v ^ 3 * (2 * D u v ^ 1 * (2 * S u))) =
      D u v * (5 * h u v * q u v ^ 3 + 9 * p u v * q u v ^ 2 -
        3 * r u v ^ 2 * (D u v * (r u v).derivative) -
        4 * r u v ^ 3 * S u) := by ring
    _ = D u v * (5 * (h u v * q u v) * q u v ^ 2 +
        9 * p u v * q u v ^ 2 -
        3 * r u v ^ 2 * (h u v + 5 * q u v ^ 2) -
        4 * r u v ^ 3 * S u) := by
      rw [h_derivative_identity]
      ring
    _ = D u v * (5 * (p u v + r u v ^ 2) * q u v ^ 2 +
        9 * p u v * q u v ^ 2 -
        3 * r u v ^ 2 * (h u v + 5 * q u v ^ 2) -
        4 * r u v ^ 3 * S u) := by rw [p_h_identity]
    _ = 7 * D u v *
        (2 * p u v * q u v ^ 2 -
          r u v ^ 3 * S u - r u v ^ 2 * q u v ^ 2) := by
      rw [h_identity]
      ring

private lemma natDegree_J (u v : ℚ) : (J u v).natDegree = 20 := by
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have hJ : J u v ≠ 0 := by
    intro hzero
    have hsderivZero : (s u v).derivative = 0 := by
      rw [derivative_s, hzero]
      ring
    have hsderivNonzero : (s u v).derivative ≠ 0 :=
      ne_zero_of_natDegree_gt
        (show 0 < (s u v).derivative.natDegree by
          rw [natDegree_derivative, natDegree_s]
          norm_num)
    exact hsderivNonzero hsderivZero
  have hsderivdeg : (s u v).derivative.natDegree = 23 := by
    rw [natDegree_derivative, natDegree_s]
  rw [derivative_s, natDegree_mul (mul_ne_zero (by norm_num) hD) hJ,
    natDegree_mul (by norm_num) hD, natDegree_D] at hsderivdeg
  norm_num at hsderivdeg
  omega

private lemma q_mul_J (u v : ℚ) :
    q u v * J u v =
      2 * s u v + r u v ^ 2 * (p u v - r u v ^ 2) := by
  rw [J_simple_identity, s]
  calc
    q u v *
        (2 * p u v * q u v ^ 2 -
          r u v ^ 3 * S u - r u v ^ 2 * q u v ^ 2) =
      2 * p u v * q u v ^ 3 - r u v ^ 3 * (q u v * S u) -
        r u v ^ 2 * q u v ^ 3 := by ring
    _ = 2 * p u v * q u v ^ 3 - r u v ^ 3 * (r u v + D u v ^ 2) -
        r u v ^ 2 * q u v ^ 3 := by rw [← r_identity]
    _ = 2 * (p u v * q u v ^ 3 - r u v ^ 3 * D u v ^ 2) +
        r u v ^ 2 * ((r u v * D u v ^ 2 - q u v ^ 3) - r u v ^ 2) := by ring
    _ = 2 * (p u v * q u v ^ 3 - r u v ^ 3 * D u v ^ 2) +
        r u v ^ 2 * (p u v - r u v ^ 2) := by rw [← p]

private lemma discr_D (a b : ℚ) :
    (D a b).discr = -16 * delta a b := by
  have hdegree : (D a b).degree = 3 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr (natDegree_D a b)
  rw [discr_of_degree_eq_three hdegree]
  simp [D, delta]
  ring

private lemma resultant_D_derivative (a b : ℚ) :
    (D a b).resultant (D a b).derivative = 64 * delta a b := by
  have hdegree : (D a b).degree = 3 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr (natDegree_D a b)
  calc
    (D a b).resultant (D a b).derivative =
        (-1) ^ ((D a b).natDegree * ((D a b).natDegree - 1) / 2) *
          (D a b).leadingCoeff * (D a b).discr := by
      simpa using resultant_deriv
        (show 0 < (D a b).degree by rw [hdegree]; norm_num)
    _ = 64 * delta a b := by
      rw [natDegree_D, leadingCoeff_D, discr_D]
      norm_num
      ring

private lemma resultant_D_S (a b : ℚ) :
    (D a b).resultant (S a) = 8 * delta a b := by
  have hderivativeDegree : (D a b).derivative.natDegree = 2 := by
    rw [natDegree_derivative, natDegree_D]
  have hscale :
      (D a b).resultant (D a b).derivative 3 2 =
        2 ^ 3 * (D a b).resultant (S a) 3 2 := by
    rw [derivative_D]
    change
      (D a b).resultant (C (2 : ℚ) * S a) 3 2 =
        2 ^ 3 * (D a b).resultant (S a) 3 2
    exact resultant_C_mul_right (D a b) (S a) 3 2 (2 : ℚ)
  have hcubic := resultant_D_derivative a b
  rw [natDegree_D, hderivativeDegree] at hcubic
  rw [natDegree_D, natDegree_S]
  norm_num at hscale
  linarith

private lemma resultant_D_four_q (a b : ℚ) :
    (D a b).resultant (4 * q a b) 3 4 = -64 * delta a b ^ 2 := by
  have hqform :
      4 * q a b = -(S a ^ 2) + D a b * (12 * X) := by
    rw [q_identity]
    ring
  have hmultiplier : (12 * X : ℚ[X]).natDegree ≤ 1 := by
    compute_degree!
  have hadd :
      (D a b).resultant (-(S a ^ 2) + D a b * (12 * X)) 3 4 =
        (D a b).resultant (-(S a ^ 2)) 3 4 :=
    resultant_add_mul_right (D a b) (-(S a ^ 2)) (12 * X) 3 4
      (by omega) (by rw [natDegree_D])
  have hscale :
      (D a b).resultant (-(S a ^ 2)) 3 4 =
        -(D a b).resultant (S a ^ 2) 3 4 := by
    have h := resultant_C_mul_right (D a b) (S a ^ 2) 3 4 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at h
    norm_num at h
    exact h
  have hmul :
      (D a b).resultant (S a ^ 2) 3 4 =
        (D a b).resultant (S a) 3 2 ^ 2 := by
    rw [pow_two, pow_two]
    simpa [natDegree_S] using
      resultant_mul_right (D a b) (S a) (S a) 3 (by rw [natDegree_D])
  have hDS := resultant_D_S a b
  rw [natDegree_D, natDegree_S] at hDS
  rw [hqform, hadd, hscale, hmul, hDS]
  ring

private lemma resultant_D_q (a b : ℚ) :
    (D a b).resultant (q a b) = -delta a b ^ 2 := by
  have hscale :
      (D a b).resultant (4 * q a b) 3 4 =
        4 ^ 3 * (D a b).resultant (q a b) 3 4 := by
    change
      (D a b).resultant (C (4 : ℚ) * q a b) 3 4 =
        4 ^ 3 * (D a b).resultant (q a b) 3 4
    exact resultant_C_mul_right (D a b) (q a b) 3 4 (4 : ℚ)
  have hfour := resultant_D_four_q a b
  rw [natDegree_D, natDegree_q]
  rw [hfour] at hscale
  norm_num at hscale
  linarith

private lemma resultant_r_q (a b : ℚ) :
    (r a b).resultant (q a b) = delta a b ^ 4 := by
  have hrform :
      r a b = -(D a b ^ 2) + q a b * S a := by
    rw [← r_identity]
    ring
  have hadd :
      (-(D a b ^ 2) + q a b * S a).resultant (q a b) 6 4 =
        (-(D a b ^ 2)).resultant (q a b) 6 4 :=
    resultant_add_mul_left (-(D a b ^ 2)) (q a b) (S a) 6 4
      (by rw [natDegree_S]) (by rw [natDegree_q])
  have hscale :
      (-(D a b ^ 2)).resultant (q a b) 6 4 =
        (D a b ^ 2).resultant (q a b) 6 4 := by
    have h := resultant_C_mul_left (D a b ^ 2) (q a b) 6 4 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at h
    norm_num at h
    exact h
  have hmul :
      (D a b ^ 2).resultant (q a b) 6 4 =
        (D a b).resultant (q a b) 3 4 ^ 2 := by
    rw [pow_two, pow_two]
    simpa [natDegree_D] using
      resultant_mul_left (D a b) (D a b) (q a b) 4 (by rw [natDegree_q])
  have hDq := resultant_D_q a b
  rw [natDegree_D, natDegree_q] at hDq
  rw [natDegree_r, natDegree_q, hrform, hadd, hscale, hmul, hDq]
  ring

private lemma resultant_s_q (a b : ℚ) :
    (s a b).resultant (q a b) = delta a b ^ 16 := by
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hD : D a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D a b).natDegree by rw [natDegree_D]; norm_num)
  have hsform :
      s a b = -(r a b ^ 3 * D a b ^ 2) + q a b * (p a b * q a b ^ 2) := by
    rw [s]
    ring
  have hmultiplier : (p a b * q a b ^ 2).natDegree ≤ 20 := by
    rw [natDegree_mul
      (ne_zero_of_natDegree_gt
        (show 0 < (p a b).natDegree by rw [natDegree_p]; norm_num))
      (pow_ne_zero 2 hq), natDegree_pow, natDegree_p, natDegree_q]
  have hadd :
      (-(r a b ^ 3 * D a b ^ 2) + q a b * (p a b * q a b ^ 2)).resultant
          (q a b) 24 4 =
        (-(r a b ^ 3 * D a b ^ 2)).resultant (q a b) 24 4 :=
    resultant_add_mul_left (-(r a b ^ 3 * D a b ^ 2)) (q a b)
      (p a b * q a b ^ 2) 24 4 (by omega) (by rw [natDegree_q])
  have hscale :
      (-(r a b ^ 3 * D a b ^ 2)).resultant (q a b) 24 4 =
        (r a b ^ 3 * D a b ^ 2).resultant (q a b) 24 4 := by
    have hh := resultant_C_mul_left (r a b ^ 3 * D a b ^ 2) (q a b) 24 4 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hmul :
      (r a b ^ 3 * D a b ^ 2).resultant (q a b) 24 4 =
        (r a b ^ 3).resultant (q a b) 18 4 *
          (D a b ^ 2).resultant (q a b) 6 4 := by
    have hr3deg : (r a b ^ 3).natDegree = 18 := by
      rw [natDegree_pow, natDegree_r]
    have hD2deg : (D a b ^ 2).natDegree = 6 := by
      rw [natDegree_pow, natDegree_D]
    have hh := resultant_mul_left (r a b ^ 3) (D a b ^ 2) (q a b) 4
      (by rw [natDegree_q])
    rw [hr3deg, hD2deg] at hh
    norm_num at hh
    exact hh
  have hrpow :
      (r a b ^ 3).resultant (q a b) 18 4 =
        (r a b).resultant (q a b) 6 4 ^ 3 := by
    have hr3deg : (r a b ^ 3).natDegree = 18 := by
      rw [natDegree_pow, natDegree_r]
    have hh := resultant_pow_left (r a b) (q a b) 3 4
      (by rw [leadingCoeff_r]; norm_num) (by rw [natDegree_q])
    rw [hr3deg, natDegree_r] at hh
    exact hh
  have hDpow :
      (D a b ^ 2).resultant (q a b) 6 4 =
        (D a b).resultant (q a b) 3 4 ^ 2 := by
    have hD2deg : (D a b ^ 2).natDegree = 6 := by
      rw [natDegree_pow, natDegree_D]
    have hh := resultant_pow_left (D a b) (q a b) 2 4
      (by rw [leadingCoeff_D]; norm_num) (by rw [natDegree_q])
    rw [hD2deg, natDegree_D] at hh
    exact hh
  have hrq := resultant_r_q a b
  rw [natDegree_r, natDegree_q] at hrq
  have hDq := resultant_D_q a b
  rw [natDegree_D, natDegree_q] at hDq
  rw [natDegree_s, natDegree_q, hsform, hadd, hscale, hmul, hrpow, hDpow, hrq, hDq]
  ring

private lemma resultant_s_r (a b : ℚ) :
    (s a b).resultant (r a b) = delta a b ^ 24 := by
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hD : D a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D a b).natDegree by rw [natDegree_D]; norm_num)
  let T : ℚ[X] := D a b ^ 2 * q a b ^ 3 - r a b ^ 2 * D a b ^ 2
  have hsform :
      s a b = -(q a b ^ 6) + r a b * T := by
    dsimp only [T]
    rw [s, p]
    ring
  have hTdeg : T.natDegree ≤ 18 := by
    dsimp only [T]
    calc
      (D a b ^ 2 * q a b ^ 3 - r a b ^ 2 * D a b ^ 2).natDegree ≤
          max (D a b ^ 2 * q a b ^ 3).natDegree
            (r a b ^ 2 * D a b ^ 2).natDegree := natDegree_sub_le _ _
      _ = 18 := by
        rw [natDegree_mul (pow_ne_zero 2 hD) (pow_ne_zero 3 hq),
          natDegree_mul (pow_ne_zero 2 hr) (pow_ne_zero 2 hD),
          natDegree_pow, natDegree_D]
        rw [natDegree_pow, natDegree_q]
        rw [natDegree_pow, natDegree_r]
        norm_num
  have hadd :
      (-(q a b ^ 6) + r a b * T).resultant (r a b) 24 6 =
        (-(q a b ^ 6)).resultant (r a b) 24 6 :=
    resultant_add_mul_left (-(q a b ^ 6)) (r a b) T 24 6
      (by omega) (by rw [natDegree_r])
  have hscale :
      (-(q a b ^ 6)).resultant (r a b) 24 6 =
        (q a b ^ 6).resultant (r a b) 24 6 := by
    have hh := resultant_C_mul_left (q a b ^ 6) (r a b) 24 6 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hqpow :
      (q a b ^ 6).resultant (r a b) 24 6 =
        (q a b).resultant (r a b) 4 6 ^ 6 := by
    have hq6deg : (q a b ^ 6).natDegree = 24 := by
      rw [natDegree_pow, natDegree_q]
    have hh := resultant_pow_left (q a b) (r a b) 6 6
      (by rw [leadingCoeff_q]; norm_num) (by rw [natDegree_r])
    rw [hq6deg, natDegree_q] at hh
    exact hh
  have hcomm := resultant_comm (q a b) (r a b) 4 6
  norm_num at hcomm
  have hrq := resultant_r_q a b
  rw [natDegree_r, natDegree_q] at hrq
  have hqr :
      (q a b).resultant (r a b) 4 6 = delta a b ^ 4 := by
    rw [hcomm, hrq]
  rw [natDegree_s, natDegree_r, hsform, hadd, hscale, hqpow, hqr]
  ring

private lemma resultant_r_p_sub_r_sq (a b : ℚ) :
    (r a b).resultant (p a b - r a b ^ 2) = delta a b ^ 12 := by
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hform :
      p a b - r a b ^ 2 =
        -(q a b ^ 3) + r a b * (D a b ^ 2 - r a b) := by
    rw [p]
    ring
  have hmultiplier : (D a b ^ 2 - r a b).natDegree ≤ 6 := by
    calc
      (D a b ^ 2 - r a b).natDegree ≤
          max (D a b ^ 2).natDegree (r a b).natDegree := natDegree_sub_le _ _
      _ = 6 := by
        rw [natDegree_pow, natDegree_D, natDegree_r]
        norm_num
  have hadd :
      (r a b).resultant (-(q a b ^ 3) + r a b * (D a b ^ 2 - r a b)) 6 12 =
        (r a b).resultant (-(q a b ^ 3)) 6 12 :=
    resultant_add_mul_right (r a b) (-(q a b ^ 3)) (D a b ^ 2 - r a b) 6 12
      (by omega) (by rw [natDegree_r])
  have hscale :
      (r a b).resultant (-(q a b ^ 3)) 6 12 =
        (r a b).resultant (q a b ^ 3) 6 12 := by
    have hh := resultant_C_mul_right (r a b) (q a b ^ 3) 6 12 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hqpow :
      (r a b).resultant (q a b ^ 3) 6 12 =
        (r a b).resultant (q a b) 6 4 ^ 3 := by
    have hq3deg : (q a b ^ 3).natDegree = 12 := by
      rw [natDegree_pow, natDegree_q]
    have hh := resultant_pow_right (r a b) (q a b) 6 3
      (by rw [natDegree_r]) (by rw [leadingCoeff_q]; norm_num)
    rw [hq3deg, natDegree_q] at hh
    exact hh
  have hrq := resultant_r_q a b
  rw [natDegree_r, natDegree_q] at hrq
  rw [natDegree_r, natDegree_p_sub_r_sq, hform, hadd, hscale, hqpow, hrq]
  ring

private lemma resultant_s_p_sub_r_sq (a b : ℚ) :
    (s a b).resultant (p a b - r a b ^ 2) = delta a b ^ 48 := by
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hsform :
      s a b = -(r a b ^ 4) +
        (p a b - r a b ^ 2) * (q a b ^ 3 - r a b ^ 2) := by
    rw [s, p]
    ring
  have hmultiplier : (q a b ^ 3 - r a b ^ 2).natDegree ≤ 12 := by
    calc
      (q a b ^ 3 - r a b ^ 2).natDegree ≤
          max (q a b ^ 3).natDegree (r a b ^ 2).natDegree := natDegree_sub_le _ _
      _ = 12 := by
        rw [natDegree_pow, natDegree_q]
        rw [natDegree_pow, natDegree_r]
        norm_num
  have hadd :
      (-(r a b ^ 4) +
          (p a b - r a b ^ 2) * (q a b ^ 3 - r a b ^ 2)).resultant
            (p a b - r a b ^ 2) 24 12 =
        (-(r a b ^ 4)).resultant (p a b - r a b ^ 2) 24 12 :=
    resultant_add_mul_left (-(r a b ^ 4)) (p a b - r a b ^ 2)
      (q a b ^ 3 - r a b ^ 2) 24 12
      (by omega) (by rw [natDegree_p_sub_r_sq])
  have hscale :
      (-(r a b ^ 4)).resultant (p a b - r a b ^ 2) 24 12 =
        (r a b ^ 4).resultant (p a b - r a b ^ 2) 24 12 := by
    have hh := resultant_C_mul_left (r a b ^ 4) (p a b - r a b ^ 2) 24 12 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hrpow :
      (r a b ^ 4).resultant (p a b - r a b ^ 2) 24 12 =
        (r a b).resultant (p a b - r a b ^ 2) 6 12 ^ 4 := by
    have hr4deg : (r a b ^ 4).natDegree = 24 := by
      rw [natDegree_pow, natDegree_r]
    have hh := resultant_pow_left (r a b) (p a b - r a b ^ 2) 4 12
      (by rw [leadingCoeff_r]; norm_num) (by rw [natDegree_p_sub_r_sq])
    rw [hr4deg, natDegree_r] at hh
    exact hh
  have hrh := resultant_r_p_sub_r_sq a b
  rw [natDegree_r, natDegree_p_sub_r_sq] at hrh
  rw [natDegree_s, natDegree_p_sub_r_sq, hsform, hadd, hscale, hrpow, hrh]
  ring

private lemma resultant_s_J (a b : ℚ) (hdelta : delta a b ≠ 0) :
    (s a b).resultant (J a b) = delta a b ^ 80 := by
  have hs : s a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (s a b).natDegree by rw [natDegree_s]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hform :
      q a b * J a b =
        r a b ^ 2 * (p a b - r a b ^ 2) + s a b * 2 := by
    rw [q_mul_J]
    ring
  have hadd :
      (s a b).resultant
          (r a b ^ 2 * (p a b - r a b ^ 2) + s a b * 2) 24 24 =
        (s a b).resultant (r a b ^ 2 * (p a b - r a b ^ 2)) 24 24 := by
    have htwo : (2 : ℚ[X]).natDegree ≤ 0 := by compute_degree!
    exact resultant_add_mul_right (s a b)
      (r a b ^ 2 * (p a b - r a b ^ 2)) 2 24 24
      (by omega) (by rw [natDegree_s])
  have hleft :
      (s a b).resultant (q a b * J a b) 24 24 =
        (s a b).resultant (q a b) 24 4 *
          (s a b).resultant (J a b) 24 20 := by
    simpa [natDegree_q, natDegree_J] using
      resultant_mul_right (s a b) (q a b) (J a b) 24
        (by rw [natDegree_s])
  have hright :
      (s a b).resultant (r a b ^ 2 * (p a b - r a b ^ 2)) 24 24 =
        (s a b).resultant (r a b ^ 2) 24 12 *
          (s a b).resultant (p a b - r a b ^ 2) 24 12 := by
    have hr2deg : (r a b ^ 2).natDegree = 12 := by
      rw [natDegree_pow, natDegree_r]
    have hh := resultant_mul_right (s a b) (r a b ^ 2)
      (p a b - r a b ^ 2) 24 (by rw [natDegree_s])
    rw [hr2deg, natDegree_p_sub_r_sq] at hh
    exact hh
  have hrpow :
      (s a b).resultant (r a b ^ 2) 24 12 =
        (s a b).resultant (r a b) 24 6 ^ 2 := by
    have hr2deg : (r a b ^ 2).natDegree = 12 := by
      rw [natDegree_pow, natDegree_r]
    have hh := resultant_pow_right (s a b) (r a b) 24 2
      (by rw [natDegree_s]) (by rw [leadingCoeff_r]; norm_num)
    rw [hr2deg, natDegree_r] at hh
    exact hh
  have hmaster :
      (s a b).resultant (q a b) 24 4 *
          (s a b).resultant (J a b) 24 20 =
        (s a b).resultant (r a b) 24 6 ^ 2 *
          (s a b).resultant (p a b - r a b ^ 2) 24 12 := by
    calc
      _ = (s a b).resultant (q a b * J a b) 24 24 := hleft.symm
      _ = (s a b).resultant
          (r a b ^ 2 * (p a b - r a b ^ 2) + s a b * 2) 24 24 := by rw [hform]
      _ = (s a b).resultant (r a b ^ 2 * (p a b - r a b ^ 2)) 24 24 := hadd
      _ = _ := by rw [hright, hrpow]
  have hsq := resultant_s_q a b
  rw [natDegree_s, natDegree_q] at hsq
  have hsr := resultant_s_r a b
  rw [natDegree_s, natDegree_r] at hsr
  have hsh := resultant_s_p_sub_r_sq a b
  rw [natDegree_s, natDegree_p_sub_r_sq] at hsh
  rw [hsq, hsr, hsh] at hmaster
  have hpow : delta a b ^ 16 ≠ 0 := pow_ne_zero 16 hdelta
  rw [natDegree_s, natDegree_J]
  apply mul_left_cancel₀ hpow
  calc
    delta a b ^ 16 * (s a b).resultant (J a b) 24 20 =
        (delta a b ^ 24) ^ 2 * delta a b ^ 48 := hmaster
    _ = delta a b ^ 16 * delta a b ^ 80 := by ring

private lemma resultant_s_D (a b : ℚ) :
    (s a b).resultant (D a b) = -delta a b ^ 12 := by
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hD : D a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D a b).natDegree by rw [natDegree_D]; norm_num)
  let T : ℚ[X] := D a b * (r a b * q a b ^ 3 - r a b ^ 3)
  have hsform :
      s a b = -(q a b ^ 6) + D a b * T := by
    dsimp only [T]
    rw [s, p]
    ring
  have hTdeg : T.natDegree ≤ 21 := by
    dsimp only [T]
    calc
      (D a b * (r a b * q a b ^ 3 - r a b ^ 3)).natDegree ≤
          (D a b).natDegree +
            (r a b * q a b ^ 3 - r a b ^ 3).natDegree := natDegree_mul_le
      _ ≤ (D a b).natDegree +
          max (r a b * q a b ^ 3).natDegree (r a b ^ 3).natDegree := by
            gcongr
            exact natDegree_sub_le _ _
      _ = 21 := by
        rw [natDegree_D, natDegree_mul hr (pow_ne_zero 3 hq),
          natDegree_pow, natDegree_r]
        rw [natDegree_pow, natDegree_q]
        rw [natDegree_r]
        norm_num
  have hadd :
      (-(q a b ^ 6) + D a b * T).resultant (D a b) 24 3 =
        (-(q a b ^ 6)).resultant (D a b) 24 3 :=
    resultant_add_mul_left (-(q a b ^ 6)) (D a b) T 24 3
      (by omega) (by rw [natDegree_D])
  have hscale :
      (-(q a b ^ 6)).resultant (D a b) 24 3 =
        -(q a b ^ 6).resultant (D a b) 24 3 := by
    have hh := resultant_C_mul_left (q a b ^ 6) (D a b) 24 3 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hqpow :
      (q a b ^ 6).resultant (D a b) 24 3 =
        (q a b).resultant (D a b) 4 3 ^ 6 := by
    have hq6deg : (q a b ^ 6).natDegree = 24 := by
      rw [natDegree_pow, natDegree_q]
    have hh := resultant_pow_left (q a b) (D a b) 6 3
      (by rw [leadingCoeff_q]; norm_num) (by rw [natDegree_D])
    rw [hq6deg, natDegree_q] at hh
    exact hh
  have hcomm := resultant_comm (q a b) (D a b) 4 3
  norm_num at hcomm
  have hDq := resultant_D_q a b
  rw [natDegree_D, natDegree_q] at hDq
  have hqD :
      (q a b).resultant (D a b) 4 3 = -delta a b ^ 2 := by
    rw [hcomm, hDq]
  rw [natDegree_s, natDegree_D, hsform, hadd, hscale, hqpow, hqD]
  ring

private lemma resultant_s_derivative (a b : ℚ) :
    (s a b).resultant (s a b).derivative =
      -(7 ^ 24 * delta a b ^ 92) := by
  have hderivativeDegree : (s a b).derivative.natDegree = 23 := by
    rw [natDegree_derivative, natDegree_s]
  have hderivativeForm :
      (s a b).derivative = C (7 : ℚ) * (D a b * J a b) := by
    rw [derivative_s]
    simp only [map_ofNat]
    ring
  have hscale :
      (s a b).resultant (s a b).derivative 24 23 =
        7 ^ 24 * (s a b).resultant (D a b * J a b) 24 23 := by
    rw [hderivativeForm]
    exact resultant_C_mul_right (s a b) (D a b * J a b) 24 23 (7 : ℚ)
  have hmul :
      (s a b).resultant (D a b * J a b) 24 23 =
        (s a b).resultant (D a b) 24 3 *
          (s a b).resultant (J a b) 24 20 := by
    simpa [natDegree_D, natDegree_J] using
      resultant_mul_right (s a b) (D a b) (J a b) 24 (by rw [natDegree_s])
  have hsD := resultant_s_D a b
  rw [natDegree_s, natDegree_D] at hsD
  by_cases hdelta : delta a b = 0
  · rw [natDegree_s, hderivativeDegree, hscale, hmul, hsD, hdelta]
    norm_num
  · have hsJ := resultant_s_J a b hdelta
    rw [natDegree_s, natDegree_J] at hsJ
    rw [natDegree_s, hderivativeDegree, hscale, hmul, hsD, hsJ]
    ring

private theorem discr_s (a b : ℚ) :
    (s a b).discr = -(7 ^ 23 * delta a b ^ 92) := by
  have hdegree : (s a b).degree = 24 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr (natDegree_s a b)
  have hresultant :
      (s a b).resultant (s a b).derivative =
        (7 : ℚ) * (s a b).discr := by
    calc
      (s a b).resultant (s a b).derivative =
          (-1) ^ ((s a b).natDegree * ((s a b).natDegree - 1) / 2) *
            (s a b).leadingCoeff * (s a b).discr := by
        simpa using resultant_deriv
          (show 0 < (s a b).degree by rw [hdegree]; norm_num)
      _ = (7 : ℚ) * (s a b).discr := by
        rw [natDegree_s, leadingCoeff_s]
        norm_num
  have hcomputed := resultant_s_derivative a b
  rw [hresultant] at hcomputed
  linarith

private lemma normal_D (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    D (W.b₄ / 2) (W.b₆ / 4) = W.Ψ₂Sq := by
  have hb₄ : 2 * (W.b₄ / 2) = W.b₄ := by ring
  have hb₆ : 4 * (W.b₆ / 4) = W.b₆ := by ring
  have hCb₄ :
      (2 : ℚ[X]) * C (W.b₄ / 2) = C W.b₄ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₄
  have hCb₆ :
      (4 : ℚ[X]) * C (W.b₆ / 4) = C W.b₆ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₆
  simp [D, WeierstrassCurve.Ψ₂Sq, hb₂]
  simp only [map_ofNat]
  linear_combination 2 * X * hCb₄ + hCb₆

private lemma normal_q (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    q (W.b₄ / 2) (W.b₆ / 4) = W.Ψ₃ := by
  have hb₄ : 2 * (W.b₄ / 2) = W.b₄ := by ring
  have hb₆ : 4 * (W.b₆ / 4) = W.b₆ := by ring
  have hCb₄ :
      (2 : ℚ[X]) * C (W.b₄ / 2) = C W.b₄ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₄
  have hCb₆ :
      (4 : ℚ[X]) * C (W.b₆ / 4) = C W.b₆ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₆
  have hb₈ : 4 * W.b₈ = -W.b₄ ^ 2 := by
    rw [W.b_relation, hb₂]
    ring
  have hCb₈ :
      (4 : ℚ[X]) * C W.b₈ = -(C W.b₄ ^ 2) := by
    simpa only [map_ofNat, C_mul, C_neg, C_pow] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₈
  have ha₂ :
      C (W.b₄ / 2) ^ 2 = -C W.b₈ := by
    apply mul_left_cancel₀ (show (4 : ℚ[X]) ≠ 0 by norm_num)
    linear_combination
      hCb₈ + (2 * C (W.b₄ / 2) + C W.b₄) * hCb₄
  simp [q, WeierstrassCurve.Ψ₃, hb₂]
  linear_combination
    3 * X ^ 2 * hCb₄ + 3 * X * hCb₆ - ha₂

private lemma normal_r (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    r (W.b₄ / 2) (W.b₆ / 4) = W.preΨ₄ := by
  have hb₄ : 2 * (W.b₄ / 2) = W.b₄ := by ring
  have hCb₄ :
      (2 : ℚ[X]) * C (W.b₄ / 2) = C W.b₄ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₄
  have hS :
      S (W.b₄ / 2) = 6 * X ^ 2 + C W.b₄ := by
    simp [S]
    linear_combination hCb₄
  have hb₈ : 4 * W.b₈ = -W.b₄ ^ 2 := by
    rw [W.b_relation, hb₂]
    ring
  have hCb₈ :
      (4 : ℚ[X]) * C W.b₈ = -(C W.b₄ ^ 2) := by
    simpa only [map_ofNat, C_mul, C_neg, C_pow] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₈
  have hW :
      W.preΨ₄ + W.Ψ₂Sq ^ 2 =
        W.Ψ₃ * (6 * X ^ 2 + C W.b₄) := by
    simp [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq,
      WeierstrassCurve.Ψ₃, hb₂]
    simp only [map_ofNat]
    linear_combination X ^ 2 * hCb₈
  have hshort := r_identity (W.b₄ / 2) (W.b₆ / 4)
  rw [normal_D W hb₂, normal_q W hb₂, hS] at hshort
  linear_combination hshort - hW

private lemma preΨ_five (W : WeierstrassCurve ℚ) :
    W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num, W.preΨ'_odd 0]
  norm_num

private lemma preΨ_seven (W : WeierstrassCurve ℚ) :
    W.preΨ' 7 =
      W.preΨ' 5 * W.Ψ₃ ^ 3 - W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2 := by
  rw [show (7 : ℕ) = 2 * (1 + 2) + 1 by norm_num, W.preΨ'_odd 1]
  norm_num

private lemma normal_p (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    p (W.b₄ / 2) (W.b₆ / 4) = W.preΨ' 5 := by
  rw [p, normal_r W hb₂, normal_D W hb₂, normal_q W hb₂, preΨ_five]

private lemma normal_s (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    s (W.b₄ / 2) (W.b₆ / 4) = W.preΨ' 7 := by
  rw [s, normal_p W hb₂, normal_q W hb₂, normal_r W hb₂,
    normal_D W hb₂, preΨ_seven]

private lemma normal_delta (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    delta (W.b₄ / 2) (W.b₆ / 4) = -W.Δ := by
  simp [delta, WeierstrassCurve.Δ, hb₂]
  ring

private lemma normal_discr_seven
    (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92) := by
  have h := discr_s (W.b₄ / 2) (W.b₆ / 4)
  rw [normal_s W hb₂, normal_delta W hb₂] at h
  rw [(show Even 92 by decide).neg_pow] at h
  norm_num at h ⊢
  exact h

private def translation (r : ℚ) : WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := r
  s := 0
  t := 0

private lemma taylor_two (r : ℚ) :
    Polynomial.taylor r (2 : ℚ[X]) = (2 : ℚ[X]) :=
  map_ofNat (Polynomial.taylorAlgHom r) 2

private lemma taylor_three (r : ℚ) :
    Polynomial.taylor r (3 : ℚ[X]) = (3 : ℚ[X]) :=
  map_ofNat (Polynomial.taylorAlgHom r) 3

private lemma taylor_five (r : ℚ) :
    Polynomial.taylor r (5 : ℚ[X]) = (5 : ℚ[X]) :=
  map_ofNat (Polynomial.taylorAlgHom r) 5

private lemma taylor_ten (r : ℚ) :
    Polynomial.taylor r (10 : ℚ[X]) = (10 : ℚ[X]) :=
  map_ofNat (Polynomial.taylorAlgHom r) 10

private lemma translation_Ψ₂Sq (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).Ψ₂Sq = W.Ψ₂Sq.taylor r := by
  simp [translation, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.variableChange_b₂,
    WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆]
  simp only [map_ofNat]
  ring

private lemma translation_Ψ₃ (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).Ψ₃ = W.Ψ₃.taylor r := by
  simp [translation, WeierstrassCurve.Ψ₃, WeierstrassCurve.variableChange_b₂,
    WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆,
    WeierstrassCurve.variableChange_b₈]
  simp only [taylor_three]
  simp only [map_ofNat]
  ring

private lemma translation_preΨ₄ (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).preΨ₄ = W.preΨ₄.taylor r := by
  have hC :
      (4 : ℚ[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
    simpa only [map_ofNat, C_mul, C_sub, C_pow] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) W.b_relation
  simp [translation, WeierstrassCurve.preΨ₄, WeierstrassCurve.variableChange_b₂,
    WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆,
    WeierstrassCurve.variableChange_b₈]
  simp only [taylor_two, taylor_five, taylor_ten]
  simp only [map_ofNat]
  linear_combination -(2 * C r * X + C r ^ 2) * hC

private lemma translation_preΨ_five (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).preΨ' 5 = (W.preΨ' 5).taylor r := by
  rw [preΨ_five, preΨ_five]
  rw [translation_preΨ₄, translation_Ψ₂Sq, translation_Ψ₃]
  simp

private lemma translation_preΨ_seven (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).preΨ' 7 = (W.preΨ' 7).taylor r := by
  rw [preΨ_seven, preΨ_seven]
  rw [translation_preΨ_five, translation_Ψ₃, translation_preΨ₄,
    translation_Ψ₂Sq]
  simp

private lemma discr_taylor (f : ℚ[X]) (r : ℚ) :
    (f.taylor r).discr = f.discr := by
  by_cases hfDegree : f.natDegree = 0
  · obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp hfDegree
    simp
  have hfDegreePos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    omega
  have htaylorDegreePos : 0 < (f.taylor r).degree := by
    simpa using hfDegreePos
  have hderivative :
      (f.taylor r).derivative = f.derivative.taylor r := by
    simp [Polynomial.taylor_apply, derivative_comp]
  have hderivativeDegree :
      f.derivative.natDegree = f.natDegree - 1 := by
    rw [natDegree_derivative]
  have hresultantTaylor := resultant_taylor f f.derivative r
  rw [natDegree_taylor, natDegree_taylor, hderivativeDegree] at hresultantTaylor
  have hresultant := resultant_deriv hfDegreePos
  have hresultantTranslated := resultant_deriv htaylorDegreePos
  rw [hderivative, natDegree_taylor, leadingCoeff_taylor] at hresultantTranslated
  rw [hresultantTaylor, hresultant] at hresultantTranslated
  have hf : f ≠ 0 := by
    intro hf
    rw [hf, natDegree_zero] at hfDegree
    exact hfDegree rfl
  have hfactor :
      (-1 : ℚ) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hf)
  exact (mul_left_cancel₀ hfactor hresultantTranslated).symm

/-- The discriminant of the universal seventh division polynomial over `ℚ`. -/
theorem discr_preΨ_seven (W : WeierstrassCurve ℚ) :
    (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92) := by
  let r : ℚ := -W.b₂ / 12
  let W₀ : WeierstrassCurve ℚ := translation r • W
  have hb₂ : W₀.b₂ = 0 := by
    simp [W₀, translation, r, WeierstrassCurve.variableChange_b₂]
    ring
  have hnormal := normal_discr_seven W₀ hb₂
  have hpolynomial := translation_preΨ_seven W r
  have hΔ : W₀.Δ = W.Δ := by
    simp [W₀, translation, WeierstrassCurve.variableChange_Δ]
  calc
    (W.preΨ' 7).discr = ((W.preΨ' 7).taylor r).discr :=
      (discr_taylor (W.preΨ' 7) r).symm
    _ = (W₀.preΨ' 7).discr := by rw [← hpolynomial]
    _ = -((7 : ℚ) ^ 23 * W₀.Δ ^ 92) := hnormal
    _ = -((7 : ℚ) ^ 23 * W.Δ ^ 92) := by rw [hΔ]

end MazurTorsion.DivisionPolynomialDiscriminantSeven
/- Platform rational-torsion adapter: Vasily Ilin, 2026. -/
open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 7 × ZMod 7) (MazurCampaign.RationalTorsion E) := by
  intro φ hφ
  exact MazurTorsion.OddPrimeFullTorsion.not_injective_zmod_seven_square_of_division_inputs E
    (MazurTorsion.DivisionPolynomialRootCriterion.hasDivisionPolynomialRootCriterion_seven E)
    (MazurTorsion.DivisionPolynomialDiscriminantSeven.discr_preΨ_seven E)
    ((AddCommGroup.torsion (E⁄ℚ).Point).subtype.comp φ)
    ((AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective.comp hφ)

#print axioms solution
