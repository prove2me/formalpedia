-- Prove2me | solution 1 for MazurCampaign.no_two_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T08:49:56.799964+00:00
-- url     : https://prove2.me/submissions/add1ce2f-b465-4e71-9c56-c1f22b3f58ac

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_exceptional_cubic_x_coordinates


/- Source module: MazurTorsion.Foundations.FullFourTorsion. Original headers retained. -/
section
/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/



/-!
# The full rational four-torsion obstruction

This file proves that the rational points of an elliptic curve over `ℚ` cannot
contain a subgroup isomorphic to `ZMod 4 × ZMod 4`. The proof extracts the
three nonzero two-torsion points and uses the duplication formulas to force an
impossible product of rational squares.
-/

namespace MazurTorsion

open scoped WeierstrassCurve.Affine

namespace FullFour

/-- Coefficients of a cubic with known distinct roots. This is the
coefficient-comparison step for the two-division polynomial. -/
lemma cubic_coefficients_of_three_roots
    {b c d r₁ r₂ r₃ : ℚ}
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hr₁ : 4 * r₁ ^ 3 + b * r₁ ^ 2 + c * r₁ + d = 0)
    (hr₂ : 4 * r₂ ^ 3 + b * r₂ ^ 2 + c * r₂ + d = 0)
    (hr₃ : 4 * r₃ ^ 3 + b * r₃ ^ 2 + c * r₃ + d = 0) :
    b = -4 * (r₁ + r₂ + r₃) ∧
      c = 4 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ∧
      d = -4 * (r₁ * r₂ * r₃) := by
  have h₁₂' :
      4 * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) + b * (r₁ + r₂) + c = 0 := by
    have hfactor :
        (r₁ - r₂) *
          (4 * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) + b * (r₁ + r₂) + c) = 0 := by
      linear_combination hr₁ - hr₂
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr h₁₂)
  have h₁₃' :
      4 * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) + b * (r₁ + r₃) + c = 0 := by
    have hfactor :
        (r₁ - r₃) *
          (4 * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) + b * (r₁ + r₃) + c) = 0 := by
      linear_combination hr₁ - hr₃
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr h₁₃)
  have hb : b = -4 * (r₁ + r₂ + r₃) := by
    have hfactor : (r₂ - r₃) * (4 * (r₁ + r₂ + r₃) + b) = 0 := by
      linear_combination h₁₂' - h₁₃'
    have := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr h₂₃)
    linarith
  have hc : c = 4 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) := by
    linear_combination h₁₂' - (r₁ + r₂) * hb
  have hd : d = -4 * (r₁ * r₂ * r₃) := by
    linear_combination hr₁ - r₁ ^ 2 * hb - r₁ * hc
  exact ⟨hb, hc, hd⟩

/-- Algebraic halving identity for a nonzero two-torsion point. The hypotheses
are precisely the curve equation, the coefficients of the split two-division
cubic, and the tangent-doubling equations. -/
lemma halving_forces_square
    {a₁ a₂ a₃ a₄ a₆ x y slope r₁ r₂ r₃ : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hb : a₁ ^ 2 + 4 * a₂ = -4 * (r₁ + r₂ + r₃))
    (hc : 2 * a₁ * a₃ + 4 * a₄ =
      4 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃))
    (hd : a₃ ^ 2 + 4 * a₆ = -4 * (r₁ * r₂ * r₃))
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : slope ^ 2 + a₁ * slope - a₂ - x - x = r₁) :
    (r₁ - r₂) * (r₁ - r₃) = (x - r₁) ^ 2 := by
  have hcurve_split :
      (2 * y + a₁ * x + a₃) ^ 2 =
        4 * ((x - r₁) * (x - r₂) * (x - r₃)) := by
    linear_combination 4 * hcurve + x ^ 2 * hb + x * hc + hd
  have htangent :
      (slope + a₁ / 2) * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 - 2 * (r₁ + r₂ + r₃) * x +
          (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) := by
    linear_combination hslope + x / 2 * hb + (1 : ℚ) / 4 * hc
  have hslope_sq :
      (slope + a₁ / 2) ^ 2 = 2 * x + r₁ - (r₁ + r₂ + r₃) := by
    linear_combination hx + (1 : ℚ) / 4 * hb
  have hdefect :
      ((x - r₁) ^ 2 - (r₁ - r₂) * (r₁ - r₃)) ^ 2 = 0 := by
    linear_combination
      (-(3 * x ^ 2 - 2 * (r₁ + r₂ + r₃) * x +
          (r₁ * r₂ + r₁ * r₃ + r₂ * r₃)) -
        (slope + a₁ / 2) * (2 * y + a₁ * x + a₃)) * htangent +
      (2 * y + a₁ * x + a₃) ^ 2 * hslope_sq +
      (2 * x + r₁ - (r₁ + r₂ + r₃)) * hcurve_split
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hdefect) |>.symm

/-- Extract affine coordinates and the tangent equations from a point whose
double is a nonzero point killed by two. -/
lemma exists_halving_data
    {W : WeierstrassCurve.Affine ℚ}
    (P T : W.Point) (hdouble : (2 : ℕ) • P = T)
    (htwo : (2 : ℕ) • T = 0) (hne : T ≠ 0) :
    ∃ r u x y slope : ℚ,
      (∃ hT : W.Nonsingular r u, T = .some r u hT) ∧
      W.Equation r u ∧ u = W.negY r u ∧
      W.Equation x y ∧
      slope * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      slope ^ 2 + W.a₁ * slope - W.a₂ - x - x = r := by
  have hP : P ≠ 0 := by
    intro hP0
    rw [hP0] at hdouble
    exact hne (by simpa using hdouble.symm)
  cases T with
  | zero => exact (hne rfl).elim
  | some r u hT =>
      have hu : u = W.negY r u := by
        have hself :
            WeierstrassCurve.Affine.Point.some r u hT =
              -WeierstrassCurve.Affine.Point.some r u hT := by
          rw [← add_eq_zero_iff_eq_neg]
          simpa [two_nsmul] using htwo
        simpa only [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq, true_and] using hself
      cases P with
      | zero => exact (hP rfl).elim
      | some x y hPxy =>
          have hy : y ≠ W.negY x y := by
            intro hy
            have hz :
                (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hPxy = 0 := by
              rw [two_nsmul,
                WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
            exact hne (hdouble ▸ hz)
          let slope := W.slope x x y y
          have hadd :=
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne
              (h₁ := hPxy) hy
          have hxcoord :
              W.addX x x slope = r := by
            have hsum :
                WeierstrassCurve.Affine.Point.some x y hPxy +
                    WeierstrassCurve.Affine.Point.some x y hPxy =
                  WeierstrassCurve.Affine.Point.some r u hT := by
              simpa [two_nsmul] using hdouble
            exact (WeierstrassCurve.Affine.Point.some.inj
              (hadd.symm.trans hsum)).1
          have hslope :
              slope * (2 * y + W.a₁ * x + W.a₃) =
                3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
            have hden :
                y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
              simp only [WeierstrassCurve.Affine.negY]
              ring
            dsimp [slope]
            rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
              div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
          have hxformula :
              slope ^ 2 + W.a₁ * slope - W.a₂ - x - x = r := by
            simpa only [WeierstrassCurve.Affine.addX] using hxcoord
          exact ⟨r, u, x, y, slope, ⟨hT, rfl⟩, hT.1, hu, hPxy.1,
            hslope, hxformula⟩







end FullFour

end MazurTorsion

end


/- Source module: MazurTorsion.Foundations.ThreeTorsion. Original headers retained. -/
section
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

















end MazurTorsion.ThreeTorsion

end


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

private lemma normalized_discriminant
    {t S D : ℚ}
    (hSD : S ^ 2 - D ^ 2 = 4)
    (hnorm : 3 * t ^ 4 + 4 * S * t ^ 3 + 6 * t ^ 2 - 1 = 0) :
    (4 * t ^ 3 * D) ^ 2 =
      (t ^ 2 - 1) ^ 3 * (9 * t ^ 2 - 1) := by
  have hmain : 4 * S * t ^ 3 = 1 - 6 * t ^ 2 - 3 * t ^ 4 := by
    linarith
  have hmain_sq := congrArg (fun q : ℚ => q ^ 2) hmain
  linear_combination (-16 * t ^ 6) * hSD + hmain_sq

/-- Translate the three-division equation after writing the split two-division cubic in terms of
its three roots and moving the first root to zero. -/
lemma split_three_division_translate
    {b₂ b₄ b₆ b₈ x r₁ r₂ r₃ : ℚ}
    (hb₂ : b₂ = -4 * (r₁ + r₂ + r₃))
    (hb₄ : b₄ = 2 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃))
    (hb₆ : b₆ = -4 * (r₁ * r₂ * r₃))
    (hb₈ : 4 * b₈ = b₂ * b₆ - b₄ ^ 2)
    (hψ : 3 * x ^ 4 + b₂ * x ^ 3 + 3 * b₄ * x ^ 2 +
      3 * b₆ * x + b₈ = 0) :
    3 * (x - r₁) ^ 4 +
      4 * ((r₁ - r₂) + (r₁ - r₃)) * (x - r₁) ^ 3 +
      6 * ((r₁ - r₂) * (r₁ - r₃)) * (x - r₁) ^ 2 -
      ((r₁ - r₂) * (r₁ - r₃)) ^ 2 = 0 := by
  rw [hb₂, hb₄, hb₆] at hψ hb₈
  linear_combination hψ - (1 / 4 : ℚ) * hb₈

/-- A square halving product and a root of the normalized three-division equation produce a
nondegenerate point on the exceptional quartic. -/
lemma exceptional_quartic_certificate
    {A B ξ z : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (hsq : A * B = z ^ 2)
    (hdiv : 3 * ξ ^ 4 + 4 * (A + B) * ξ ^ 3 +
      6 * (A * B) * ξ ^ 2 - (A * B) ^ 2 = 0) :
    ∃ t w : ℚ, t ≠ 0 ∧ t ^ 2 ≠ 1 ∧ 9 * t ^ 2 ≠ 1 ∧ w ≠ 0 ∧
      w ^ 2 = (t ^ 2 - 1) * (9 * t ^ 2 - 1) := by
  have hz : z ≠ 0 := by
    intro hz
    have : A * B = 0 := by rw [hsq, hz]; norm_num
    exact (mul_ne_zero hA hB) this
  have hξ : ξ ≠ 0 := by
    intro hξ
    rw [hξ] at hdiv
    norm_num at hdiv
    exact hdiv.elim hA hB
  let t := ξ / z
  let S := (A + B) / z
  let D := (A - B) / z
  have ht : t ≠ 0 := div_ne_zero hξ hz
  have hSD : S ^ 2 - D ^ 2 = 4 := by
    dsimp [S, D]
    field_simp [hz]
    nlinarith [hsq]
  have hnorm : 3 * t ^ 4 + 4 * S * t ^ 3 + 6 * t ^ 2 - 1 = 0 := by
    dsimp [t, S]
    field_simp [hz]
    nlinarith [hsq]
  have hid :
      (4 * t ^ 3 * D) ^ 2 =
        (t ^ 2 - 1) ^ 3 * (9 * t ^ 2 - 1) := by
    exact normalized_discriminant hSD hnorm
  have hD : D ≠ 0 := by
    dsimp [D]
    exact div_ne_zero (sub_ne_zero.mpr hAB) hz
  have htone : t ^ 2 ≠ 1 := by
    intro hone
    rw [hone] at hid
    norm_num at hid
    exact hid.elim ht hD
  have htnine : 9 * t ^ 2 ≠ 1 := by
    intro hnine
    rw [hnine] at hid
    norm_num at hid
    exact hid.elim ht hD
  let w := (4 * t ^ 3 * D) / (t ^ 2 - 1)
  have hw : w ≠ 0 :=
    div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 ht)) hD)
      (sub_ne_zero.mpr htone)
  refine ⟨t, w, ht, htone, htnine, hw, ?_⟩
  dsimp [w]
  field_simp [sub_ne_zero.mpr htone]
  nlinarith [hid]

open scoped WeierstrassCurve.Affine

private lemma exists_two_torsion_data
    {W : WeierstrassCurve.Affine ℚ}
    (T : W.Point) (htwo : (2 : ℕ) • T = 0) (hne : T ≠ 0) :
    ∃ r u : ℚ, ∃ hT : W.Nonsingular r u,
      T = .some r u hT ∧ W.Equation r u ∧ u = W.negY r u := by
  cases T with
  | zero => exact (hne rfl).elim
  | some r u hT =>
      have hself :
          WeierstrassCurve.Affine.Point.some r u hT =
            -WeierstrassCurve.Affine.Point.some r u hT := by
        rw [← add_eq_zero_iff_eq_neg]
        simpa [two_nsmul] using htwo
      have hu : u = W.negY r u := by
        simpa only [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq, true_and] using hself
      exact ⟨r, u, hT, rfl, hT.1, hu⟩

/-- Full rational two-torsion, a half of one nonzero two-torsion point, and a nonzero
three-torsion point produce a nondegenerate point on the exceptional quartic. -/
theorem exceptional_quartic_of_point_data
    (E : WeierstrassCurve ℚ)
    (P Q T₁ T₂ T₃ : (E⁄ℚ).Point)
    (hdouble : (2 : ℕ) • P = T₁)
    (hQthree : (3 : ℕ) • Q = 0)
    (hT₁two : (2 : ℕ) • T₁ = 0)
    (hT₂two : (2 : ℕ) • T₂ = 0)
    (hT₃two : (2 : ℕ) • T₃ = 0)
    (hQne : Q ≠ 0)
    (hT₁ne : T₁ ≠ 0) (hT₂ne : T₂ ≠ 0) (hT₃ne : T₃ ≠ 0)
    (hT₁T₂ : T₁ ≠ T₂) (hT₁T₃ : T₁ ≠ T₃) (hT₂T₃ : T₂ ≠ T₃) :
    ∃ t w : ℚ, t ≠ 0 ∧ t ^ 2 ≠ 1 ∧ 9 * t ^ 2 ≠ 1 ∧ w ≠ 0 ∧
      w ^ 2 = (t ^ 2 - 1) * (9 * t ^ 2 - 1) := by
  obtain ⟨r₁, u₁, x₁, y₁, slope, ⟨hT₁, hT₁eq⟩,
      hEr₁, hu₁, hEx₁, hslope, hx₁⟩ :=
    FullFour.exists_halving_data P T₁ hdouble hT₁two hT₁ne
  obtain ⟨r₂, u₂, hT₂, hT₂eq, hEr₂, hu₂⟩ :=
    exists_two_torsion_data T₂ hT₂two hT₂ne
  obtain ⟨r₃, u₃, hT₃, hT₃eq, hEr₃, hu₃⟩ :=
    exists_two_torsion_data T₃ hT₃two hT₃ne
  have roots_ne :
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₂ ≠ r₃ := by
    have coord_ne :
        ∀ {r u r' u' : ℚ}
          {h : (E⁄ℚ).Nonsingular r u} {h' : (E⁄ℚ).Nonsingular r' u'},
          u = (E⁄ℚ).negY r u → u' = (E⁄ℚ).negY r' u' →
          WeierstrassCurve.Affine.Point.some r u h ≠
            WeierstrassCurve.Affine.Point.some r' u' h' → r ≠ r' := by
      intro r u r' u' h h' hu hu' hpoints hr
      apply hpoints
      have huu : u = u' := by
        simp only [WeierstrassCurve.Affine.negY] at hu hu'
        rw [hr] at hu
        linarith
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hr, huu⟩
    refine ⟨coord_ne (h := hT₁) (h' := hT₂) hu₁ hu₂ ?_,
      coord_ne (h := hT₁) (h' := hT₃) hu₁ hu₃ ?_,
      coord_ne (h := hT₂) (h' := hT₃) hu₂ hu₃ ?_⟩
    · intro heq
      apply hT₁T₂
      rw [hT₁eq, hT₂eq]
      exact heq
    · intro heq
      apply hT₁T₃
      rw [hT₁eq, hT₃eq]
      exact heq
    · intro heq
      apply hT₂T₃
      rw [hT₂eq, hT₃eq]
      exact heq
  simp only [WeierstrassCurve.Affine.negY] at hu₁ hu₂ hu₃
  rw [WeierstrassCurve.Affine.equation_iff] at hEr₁ hEr₂ hEr₃ hEx₁
  have root_equation :
      ∀ {r u : ℚ},
        u ^ 2 + (E⁄ℚ).a₁ * r * u + (E⁄ℚ).a₃ * u =
          r ^ 3 + (E⁄ℚ).a₂ * r ^ 2 + (E⁄ℚ).a₄ * r + (E⁄ℚ).a₆ →
        2 * u + (E⁄ℚ).a₁ * r + (E⁄ℚ).a₃ = 0 →
        4 * r ^ 3 + (E⁄ℚ).b₂ * r ^ 2 +
          2 * (E⁄ℚ).b₄ * r + (E⁄ℚ).b₆ = 0 := by
    intro r u hcurve hneg
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    linear_combination
      -4 * hcurve + (2 * u + (E⁄ℚ).a₁ * r + (E⁄ℚ).a₃) * hneg
  have hr₁ := root_equation hEr₁ (by linarith [hu₁])
  have hr₂ := root_equation hEr₂ (by linarith [hu₂])
  have hr₃ := root_equation hEr₃ (by linarith [hu₃])
  obtain ⟨hb₂, hb₄two, hb₆⟩ :=
    FullFour.cubic_coefficients_of_three_roots
      roots_ne.1 roots_ne.2.1 roots_ne.2.2 hr₁ hr₂ hr₃
  have hb₄ :
      (E⁄ℚ).b₄ = 2 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) := by
    linarith
  have hsquare :
      (r₁ - r₂) * (r₁ - r₃) = (x₁ - r₁) ^ 2 := by
    apply FullFour.halving_forces_square hEx₁
    · simpa only [WeierstrassCurve.b₂] using hb₂
    · simp only [WeierstrassCurve.b₄] at hb₄two ⊢
      linear_combination hb₄two
    · simpa only [WeierstrassCurve.b₆] using hb₆
    · exact hslope
    · exact hx₁
  obtain ⟨xQ, yQ, hQ, hQeq, hψeval⟩ :=
    ThreeTorsion.nonzero_three_torsion_abscissa (E⁄ℚ) Q hQthree hQne
  have hψ :
      3 * xQ ^ 4 + (E⁄ℚ).b₂ * xQ ^ 3 +
        3 * (E⁄ℚ).b₄ * xQ ^ 2 + 3 * (E⁄ℚ).b₆ * xQ + (E⁄ℚ).b₈ = 0 := by
    simpa only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat] using hψeval
  have htranslated :=
    split_three_division_translate hb₂ hb₄ hb₆ (E⁄ℚ).b_relation hψ
  apply exceptional_quartic_certificate
    (A := r₁ - r₂) (B := r₁ - r₃) (ξ := xQ - r₁) (z := x₁ - r₁)
  · exact sub_ne_zero.mpr roots_ne.1
  · exact sub_ne_zero.mpr roots_ne.2.1
  · intro h
    apply roots_ne.2.2
    linarith
  · exact hsquare
  · exact htranslated

/-- The statement that every rational point on the exceptional quartic is one of its evident
degenerate points. This is the remaining Diophantine leaf of the `C₂ × C₁₂` obstruction. -/
def ExceptionalQuarticIsTrivial : Prop :=
  ∀ t w : ℚ, w ^ 2 = (t ^ 2 - 1) * (9 * t ^ 2 - 1) →
    t = 0 ∨ t ^ 2 = 1 ∨ 9 * t ^ 2 = 1 ∨ w = 0

private lemma cubic_of_relation
    {t X : ℚ} (ht : t ≠ 0)
    (hrel : t ^ 2 * (X ^ 2 - 36) = 4 * (X - 10)) :
    (2 * (X - 10) / t) ^ 2 = (X - 10) * (X - 6) * (X + 6) := by
  rw [div_pow, div_eq_iff (pow_ne_zero 2 ht)]
  linear_combination -(X - 10) * hrel

/-- Explicitly map a nonzero rational point on the exceptional quartic to the cubic
`Y² = (X - 10)(X - 6)(X + 6)`. -/
lemma exceptional_quartic_to_cubic
    {t w : ℚ} (ht : t ≠ 0)
    (heq : w ^ 2 = (t ^ 2 - 1) * (9 * t ^ 2 - 1)) :
    ∃ X Y : ℚ, X = 2 * (w + 1) / t ^ 2 ∧
      Y = 2 * (X - 10) / t ∧
      t ^ 2 * (X ^ 2 - 36) = 4 * (X - 10) ∧
      Y ^ 2 = (X - 10) * (X - 6) * (X + 6) := by
  let X := 2 * (w + 1) / t ^ 2
  let Y := 2 * (X - 10) / t
  have hwexpanded :
      (w + 1) ^ 2 = 9 * t ^ 4 - 10 * t ^ 2 + 2 * (w + 1) := by
    nlinarith [heq]
  have hrel : t ^ 2 * (X ^ 2 - 36) = 4 * (X - 10) := by
    dsimp [X]
    field_simp [ht]
    nlinarith [hwexpanded]
  refine ⟨X, Y, rfl, rfl, hrel, ?_⟩
  rw [show Y = 2 * (X - 10) / t by rfl, div_pow]
  simpa only [div_pow] using cubic_of_relation ht hrel

/-- The statement that the cubic birational to the exceptional quartic has only its seven
evident affine rational points. -/
def ExceptionalCubicIsTrivial : Prop :=
  ∀ X Y : ℚ, Y ^ 2 = (X - 10) * (X - 6) * (X + 6) →
    X = -6 ∨ X = 2 ∨ X = 6 ∨ X = 10 ∨ X = 18

/-- Classification of rational points on the associated cubic implies classification of rational
points on the exceptional quartic. -/
theorem exceptionalQuarticIsTrivial_of_cubic
    (hcubic : ExceptionalCubicIsTrivial) :
    ExceptionalQuarticIsTrivial := by
  intro t w heq
  by_cases ht : t = 0
  · exact Or.inl ht
  obtain ⟨X, Y, hX, hY, hrel, hcubicPoint⟩ :=
    exceptional_quartic_to_cubic ht heq
  rcases hcubic X Y hcubicPoint with h | h | h | h | h
  · rw [h] at hrel
    norm_num at hrel
  · right
    left
    rw [h] at hrel
    norm_num at hrel
    rcases hrel with hrel | hrel <;> simp [hrel]
  · rw [h] at hrel
    norm_num at hrel
  · rw [h] at hrel
    norm_num at hrel
    exact (ht hrel).elim
  · right
    right
    left
    rw [h] at hrel
    norm_num at hrel ⊢
    linarith

/-- An injective `ZMod 2 × ZMod 12` subgroup of rational points would produce a nondegenerate
rational point on the exceptional quartic. -/
theorem exceptional_quartic_of_injective_zmod_two_twelve
    (E : WeierstrassCurve ℚ)
    (φ : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point)
    (hφ : Function.Injective φ) :
    ∃ t w : ℚ, t ≠ 0 ∧ t ^ 2 ≠ 1 ∧ 9 * t ^ 2 ≠ 1 ∧ w ≠ 0 ∧
      w ^ 2 = (t ^ 2 - 1) * (9 * t ^ 2 - 1) := by
  let P : (E⁄ℚ).Point := φ (0, 3)
  let Q : (E⁄ℚ).Point := φ (0, 4)
  let T₁ : (E⁄ℚ).Point := φ (0, 6)
  let T₂ : (E⁄ℚ).Point := φ (1, 0)
  let T₃ : (E⁄ℚ).Point := φ (1, 6)
  have hdouble : (2 : ℕ) • P = T₁ := by
    dsimp [P, T₁]
    rw [← map_nsmul]
    congr 1
  have hQthree : (3 : ℕ) • Q = 0 := by
    dsimp [Q]
    rw [← map_nsmul,
      show (3 : ℕ) • ((0 : ZMod 2), (4 : ZMod 12)) = 0 by decide, map_zero]
  have hT₁two : (2 : ℕ) • T₁ = 0 := by
    dsimp [T₁]
    rw [← map_nsmul,
      show (2 : ℕ) • ((0 : ZMod 2), (6 : ZMod 12)) = 0 by decide, map_zero]
  have hT₂two : (2 : ℕ) • T₂ = 0 := by
    dsimp [T₂]
    rw [← map_nsmul,
      show (2 : ℕ) • ((1 : ZMod 2), (0 : ZMod 12)) = 0 by decide, map_zero]
  have hT₃two : (2 : ℕ) • T₃ = 0 := by
    dsimp [T₃]
    rw [← map_nsmul,
      show (2 : ℕ) • ((1 : ZMod 2), (6 : ZMod 12)) = 0 by decide, map_zero]
  have hQne : Q ≠ 0 := by
    intro h
    exact (by decide : ((0 : ZMod 2), (4 : ZMod 12)) ≠ 0)
      (hφ (by simpa [Q] using h))
  have hT₁ne : T₁ ≠ 0 := by
    intro h
    exact (by decide : ((0 : ZMod 2), (6 : ZMod 12)) ≠ 0)
      (hφ (by simpa [T₁] using h))
  have hT₂ne : T₂ ≠ 0 := by
    intro h
    exact (by decide : ((1 : ZMod 2), (0 : ZMod 12)) ≠ 0)
      (hφ (by simpa [T₂] using h))
  have hT₃ne : T₃ ≠ 0 := by
    intro h
    exact (by decide : ((1 : ZMod 2), (6 : ZMod 12)) ≠ 0)
      (hφ (by simpa [T₃] using h))
  have hT₁T₂ : T₁ ≠ T₂ := by
    intro h
    exact (by decide :
      ((0 : ZMod 2), (6 : ZMod 12)) ≠ ((1 : ZMod 2), (0 : ZMod 12)))
      (hφ (by simpa [T₁, T₂] using h))
  have hT₁T₃ : T₁ ≠ T₃ := by
    intro h
    exact (by decide :
      ((0 : ZMod 2), (6 : ZMod 12)) ≠ ((1 : ZMod 2), (6 : ZMod 12)))
      (hφ (by simpa [T₁, T₃] using h))
  have hT₂T₃ : T₂ ≠ T₃ := by
    intro h
    exact (by decide :
      ((1 : ZMod 2), (0 : ZMod 12)) ≠ ((1 : ZMod 2), (6 : ZMod 12)))
      (hφ (by simpa [T₂, T₃] using h))
  exact exceptional_quartic_of_point_data E P Q T₁ T₂ T₃
    hdouble hQthree hT₁two hT₂two hT₃two hQne hT₁ne hT₂ne hT₃ne
    hT₁T₂ hT₁T₃ hT₂T₃

/-- The exceptional quartic classification rules out an injective
`ZMod 2 × ZMod 12` subgroup of rational elliptic-curve points. -/
theorem not_injective_zmod_two_twelve_of_quartic
    (hquartic : ExceptionalQuarticIsTrivial)
    (E : WeierstrassCurve ℚ)
    (φ : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  obtain ⟨t, w, ht, htone, htnine, hw, heq⟩ :=
    exceptional_quartic_of_injective_zmod_two_twelve E φ hφ
  rcases hquartic t w heq with h | h | h | h
  · exact ht h
  · exact htone h
  · exact htnine h
  · exact hw h

/-- The rational-point classification of the associated cubic directly rules out an injective
`ZMod 2 × ZMod 12` subgroup. -/
theorem not_injective_zmod_two_twelve_of_cubic
    (hcubic : ExceptionalCubicIsTrivial)
    (E : WeierstrassCurve ℚ)
    (φ : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ :=
  not_injective_zmod_two_twelve_of_quartic
    (exceptionalQuarticIsTrivial_of_cubic hcubic) E φ

end MazurTorsion

end

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 2 × ZMod 12) (MazurCampaign.RationalTorsion E) := by
  intro φ hφ
  exact MazurTorsion.not_injective_zmod_two_twelve_of_cubic
    MazurCampaign.exceptional_cubic_x_coordinates E
    ((AddCommGroup.torsion (E⁄ℚ).Point).subtype.comp φ)
    ((AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective.comp hφ)
#print axioms solution
