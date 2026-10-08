-- Prove2me | solution 1 for MazurCampaign.no_two_ten
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T07:18:34.664859+00:00
-- url     : https://prove2.me/submissions/8e8a128a-46a1-415d-b056-e58636d24b68

import Definitions.Def_MazurCampaign_group_constraints
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples

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

private lemma three_square_products_impossible
    {r₁ r₂ r₃ z₁ z₂ z₃ : ℚ}
    (hr₁₂ : r₁ ≠ r₂) (hr₁₃ : r₁ ≠ r₃) (hr₂₃ : r₂ ≠ r₃)
    (hk₁ : (r₁ - r₂) * (r₁ - r₃) = z₁ ^ 2)
    (hk₂ : (r₂ - r₁) * (r₂ - r₃) = z₂ ^ 2)
    (hk₃ : (r₃ - r₁) * (r₃ - r₂) = z₃ ^ 2) :
    False := by
  have hvandermonde :
      (r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hr₁₂)
      (sub_ne_zero.mpr hr₁₃)) (sub_ne_zero.mpr hr₂₃)
  have hnegative :
      (z₁ * z₂ * z₃) ^ 2 =
        -(((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2) := by
    linear_combination
      (-z₂ ^ 2 * z₃ ^ 2) * hk₁ -
      ((r₁ - r₂) * (r₁ - r₃) * z₃ ^ 2) * hk₂ -
      ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₁) * (r₂ - r₃)) * hk₃
  have hpositive :
      (0 : ℚ) <
        ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 :=
    sq_pos_of_ne_zero hvandermonde
  nlinarith [sq_nonneg (z₁ * z₂ * z₃)]

private theorem three_halvable_two_torsion_points_impossible
    (E : WeierstrassCurve ℚ)
    (P₁ P₂ P₃ T₁ T₂ T₃ : (E⁄ℚ).Point)
    (hd₁ : (2 : ℕ) • P₁ = T₁) (hd₂ : (2 : ℕ) • P₂ = T₂)
    (hd₃ : (2 : ℕ) • P₃ = T₃)
    (ht₁ : (2 : ℕ) • T₁ = 0) (ht₂ : (2 : ℕ) • T₂ = 0)
    (ht₃ : (2 : ℕ) • T₃ = 0)
    (hn₁ : T₁ ≠ 0) (hn₂ : T₂ ≠ 0) (hn₃ : T₃ ≠ 0)
    (hn₁₂ : T₁ ≠ T₂) (hn₁₃ : T₁ ≠ T₃) (hn₂₃ : T₂ ≠ T₃) :
    False := by
  obtain ⟨r₁, u₁, x₁, y₁, s₁, ⟨hT₁, hT₁eq⟩,
      hEr₁, hu₁, hEx₁, hs₁, hx₁⟩ :=
    exists_halving_data P₁ T₁ hd₁ ht₁ hn₁
  obtain ⟨r₂, u₂, x₂, y₂, s₂, ⟨hT₂, hT₂eq⟩,
      hEr₂, hu₂, hEx₂, hs₂, hx₂⟩ :=
    exists_halving_data P₂ T₂ hd₂ ht₂ hn₂
  obtain ⟨r₃, u₃, x₃, y₃, s₃, ⟨hT₃, hT₃eq⟩,
      hEr₃, hu₃, hEx₃, hs₃, hx₃⟩ :=
    exists_halving_data P₃ T₃ hd₃ ht₃ hn₃
  have hr₁₂ : r₁ ≠ r₂ := by
    intro h
    have hu : u₁ = u₂ := by
      simp only [WeierstrassCurve.Affine.negY] at hu₁ hu₂
      rw [h] at hu₁
      linarith
    apply hn₁₂
    calc
      T₁ = WeierstrassCurve.Affine.Point.some r₁ u₁ hT₁ := hT₁eq
      _ = WeierstrassCurve.Affine.Point.some r₂ u₂ hT₂ := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨h, hu⟩
      _ = T₂ := hT₂eq.symm
  have hr₁₃ : r₁ ≠ r₃ := by
    intro h
    have hu : u₁ = u₃ := by
      simp only [WeierstrassCurve.Affine.negY] at hu₁ hu₃
      rw [h] at hu₁
      linarith
    apply hn₁₃
    calc
      T₁ = WeierstrassCurve.Affine.Point.some r₁ u₁ hT₁ := hT₁eq
      _ = WeierstrassCurve.Affine.Point.some r₃ u₃ hT₃ := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨h, hu⟩
      _ = T₃ := hT₃eq.symm
  have hr₂₃ : r₂ ≠ r₃ := by
    intro h
    have hu : u₂ = u₃ := by
      simp only [WeierstrassCurve.Affine.negY] at hu₂ hu₃
      rw [h] at hu₂
      linarith
    apply hn₂₃
    calc
      T₂ = WeierstrassCurve.Affine.Point.some r₂ u₂ hT₂ := hT₂eq
      _ = WeierstrassCurve.Affine.Point.some r₃ u₃ hT₃ := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨h, hu⟩
      _ = T₃ := hT₃eq.symm
  simp only [WeierstrassCurve.Affine.negY] at hu₁ hu₂ hu₃
  rw [WeierstrassCurve.Affine.equation_iff] at hEr₁ hEr₂ hEr₃ hEx₁ hEx₂ hEx₃
  have hroot₁ :
      4 * r₁ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * r₁ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * r₁ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * u₁ + (E⁄ℚ).a₁ * r₁ + (E⁄ℚ).a₃) * hu₁ - 4 * hEr₁
  have hroot₂ :
      4 * r₂ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * r₂ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * r₂ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * u₂ + (E⁄ℚ).a₁ * r₂ + (E⁄ℚ).a₃) * hu₂ - 4 * hEr₂
  have hroot₃ :
      4 * r₃ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * r₃ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * r₃ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * u₃ + (E⁄ℚ).a₁ * r₃ + (E⁄ℚ).a₃) * hu₃ - 4 * hEr₃
  obtain ⟨hb, hc, hd⟩ :=
    cubic_coefficients_of_three_roots hr₁₂ hr₁₃ hr₂₃
      hroot₁ hroot₂ hroot₃
  have hk₁ : (r₁ - r₂) * (r₁ - r₃) = (x₁ - r₁) ^ 2 :=
    halving_forces_square hEx₁ hb hc hd hs₁ hx₁
  have hb₂ :
      (E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂ = -4 * (r₂ + r₁ + r₃) := by
    linear_combination hb
  have hc₂ :
      2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄ =
        4 * (r₂ * r₁ + r₂ * r₃ + r₁ * r₃) := by
    linear_combination hc
  have hd₂ :
      (E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆ = -4 * (r₂ * r₁ * r₃) := by
    linear_combination hd
  have hk₂ : (r₂ - r₁) * (r₂ - r₃) = (x₂ - r₂) ^ 2 :=
    halving_forces_square hEx₂ hb₂ hc₂ hd₂ hs₂ hx₂
  have hb₃ :
      (E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂ = -4 * (r₃ + r₁ + r₂) := by
    linear_combination hb
  have hc₃ :
      2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄ =
        4 * (r₃ * r₁ + r₃ * r₂ + r₁ * r₂) := by
    linear_combination hc
  have hd₃ :
      (E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆ = -4 * (r₃ * r₁ * r₂) := by
    linear_combination hd
  have hk₃ : (r₃ - r₁) * (r₃ - r₂) = (x₃ - r₃) ^ 2 :=
    halving_forces_square hEx₃ hb₃ hc₃ hd₃ hs₃ hx₃
  exact three_square_products_impossible hr₁₂ hr₁₃ hr₂₃ hk₁ hk₂ hk₃

/-- An elliptic curve over `ℚ` cannot have full rational `4`-torsion. -/
theorem not_injective_zmod_four_square
    (E : WeierstrassCurve ℚ)
    (φ : (ZMod 4 × ZMod 4) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  let P₁ : (E⁄ℚ).Point := φ (1, 0)
  let P₂ : (E⁄ℚ).Point := φ (0, 1)
  let P₃ : (E⁄ℚ).Point := φ (1, 1)
  let T₁ : (E⁄ℚ).Point := φ (2, 0)
  let T₂ : (E⁄ℚ).Point := φ (0, 2)
  let T₃ : (E⁄ℚ).Point := φ (2, 2)
  have hd₁ : (2 : ℕ) • P₁ = T₁ := by
    dsimp [P₁, T₁]
    rw [← map_nsmul]
    congr 1
  have hd₂ : (2 : ℕ) • P₂ = T₂ := by
    dsimp [P₂, T₂]
    rw [← map_nsmul]
    congr 1
  have hd₃ : (2 : ℕ) • P₃ = T₃ := by
    dsimp [P₃, T₃]
    rw [← map_nsmul]
    congr 1
  have ht₁ : (2 : ℕ) • T₁ = 0 := by
    dsimp [T₁]
    rw [← map_nsmul, show (2 : ℕ) • ((2 : ZMod 4), (0 : ZMod 4)) = 0 by decide,
      map_zero]
  have ht₂ : (2 : ℕ) • T₂ = 0 := by
    dsimp [T₂]
    rw [← map_nsmul, show (2 : ℕ) • ((0 : ZMod 4), (2 : ZMod 4)) = 0 by decide,
      map_zero]
  have ht₃ : (2 : ℕ) • T₃ = 0 := by
    dsimp [T₃]
    rw [← map_nsmul, show (2 : ℕ) • ((2 : ZMod 4), (2 : ZMod 4)) = 0 by decide,
      map_zero]
  have hn₁ : T₁ ≠ 0 := by
    intro h
    exact (by decide : ((2 : ZMod 4), (0 : ZMod 4)) ≠ 0)
      (hφ (by simpa [T₁] using h))
  have hn₂ : T₂ ≠ 0 := by
    intro h
    exact (by decide : ((0 : ZMod 4), (2 : ZMod 4)) ≠ 0)
      (hφ (by simpa [T₂] using h))
  have hn₃ : T₃ ≠ 0 := by
    intro h
    exact (by decide : ((2 : ZMod 4), (2 : ZMod 4)) ≠ 0)
      (hφ (by simpa [T₃] using h))
  have hn₁₂ : T₁ ≠ T₂ := by
    intro h
    exact (by decide :
      ((2 : ZMod 4), (0 : ZMod 4)) ≠ ((0 : ZMod 4), (2 : ZMod 4)))
      (hφ (by simpa [T₁, T₂] using h))
  have hn₁₃ : T₁ ≠ T₃ := by
    intro h
    exact (by decide :
      ((2 : ZMod 4), (0 : ZMod 4)) ≠ ((2 : ZMod 4), (2 : ZMod 4)))
      (hφ (by simpa [T₁, T₃] using h))
  have hn₂₃ : T₂ ≠ T₃ := by
    intro h
    exact (by decide :
      ((0 : ZMod 4), (2 : ZMod 4)) ≠ ((2 : ZMod 4), (2 : ZMod 4)))
      (hφ (by simpa [T₂, T₃] using h))
  exact three_halvable_two_torsion_points_impossible E
    P₁ P₂ P₃ T₁ T₂ T₃ hd₁ hd₂ hd₃ ht₁ ht₂ ht₃
    hn₁ hn₂ hn₃ hn₁₂ hn₁₃ hn₂₃

end FullFour

end MazurTorsion

/-
Copyright (c) 2026 Kevin Buzzard, Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude, Vasily Ilin
-/


/-!
# Isomorphism of point groups induced by a change of variables

This file is ported from Michael Stoll's Apache-2.0 `EllipticCurves` project at commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

The derivative-transport and singular-cubic nonsingular-locus equivalence are local extensions.
They generalize the ported point equivalence beyond elliptic equations while retaining the
original admissible change-of-variables formulas and attribution.

Mathlib's affine `Point` API provides the group homomorphism induced by a change of the base
field for a fixed Weierstrass curve, but not the isomorphism of Mordell--Weil groups induced by
an admissible change of variables between two different curves. For
`C : WeierstrassCurve.VariableChange F`, the admissible change

`(x, y) ↦ (u²x + r, u³y + u²sx + t)`

gives the group isomorphism
`WeierstrassCurve.Affine.Point.equivVariableChange : (C • W).Point ≃+ W.Point`.
Its inverse is the explicit change of variables `C⁻¹`.
-/


namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### Transformation of the group-law formulae under a change of variables -/

lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp [negY, variableChange_a₁, variableChange_a₃]
  field

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition only if the original pair does. -/
lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro ⟨hX, hY⟩
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp [addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp [negAddY, addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [variableChange_negY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`. -/
lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val, field]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

/-- The `Y`-derivative of a Weierstrass equation under an admissible change of variables.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialY (x y : F) :
    W.toAffine.polynomialY.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  simp only [Affine.evalEval_polynomialY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field

/-- The `X`-derivative of a Weierstrass equation under an admissible change of variables.
The correction term is the chain-rule contribution from the `sx` term in the new `Y` coordinate.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialX (x y : F) :
    W.toAffine.polynomialX.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 4 * (C • W).toAffine.polynomialX.evalEval x y -
        C.s * ((C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y) := by
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field

/-- An admissible change of variables identifies the nonsingular loci even when the common
Weierstrass cubic is singular. -/
lemma variableChange_nonsingular (x y : F) :
    W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) ↔
      (C • W).toAffine.Nonsingular x y := by
  rw [Affine.Nonsingular, Affine.Nonsingular, variableChange_equation W C,
    variableChange_polynomialX W C, variableChange_polynomialY W C]
  apply and_congr_right
  intro _
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  constructor
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        intro hX
        apply hx
        rw [hY, mul_zero, mul_zero, sub_zero, hX, mul_zero]
      · exact Or.inr hY
    · exact Or.inr fun hY ↦ hy (mul_eq_zero.mpr <| Or.inr hY)
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        rw [hY, mul_zero, mul_zero, sub_zero]
        exact mul_ne_zero (pow_ne_zero 4 hu) hx
      · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hY)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hy)

/-! ### The induced isomorphism of point groups -/

namespace Point

/-- The underlying point map of the change of variables, sending `0` to `0`. -/
def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ((variableChange_nonsingular W C x y).mpr h)

@[simp] lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h
  rfl

/-- The group homomorphism induced by the admissible change of variables. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := h₁.left
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := h₂.left
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]

/-- The point-group isomorphism induced by the admissible change of variables. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [equivOfEq_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      refine some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }

lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

end Point

end WeierstrassCurve.Affine


/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

/-!
# Tate normal form

Reusable foundations for the Tate normal form

`y² + (1-c)xy - by = x³ - bx²`

with marked point `P = (0,0)`. This file provides the normalization theorem retaining
the discriminant scale and kernel-checked low-multiple coordinate formulas. It does not
state an order classification theorem.
-/
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Tate normal form
`y² + (1-c)xy - by = x³ - bx²`, with marked point `(0,0)`. -/
def tateNormalCurve (b c : ℚ) : WeierstrassCurve ℚ :=
  ⟨1 - c, -b, -b, 0, 0⟩

@[simp] lemma tateNormalCurve_a₁ (b c : ℚ) : (tateNormalCurve b c).a₁ = 1 - c := rfl
@[simp] lemma tateNormalCurve_a₂ (b c : ℚ) : (tateNormalCurve b c).a₂ = -b := rfl
@[simp] lemma tateNormalCurve_a₃ (b c : ℚ) : (tateNormalCurve b c).a₃ = -b := rfl
@[simp] lemma tateNormalCurve_a₄ (b c : ℚ) : (tateNormalCurve b c).a₄ = 0 := rfl
@[simp] lemma tateNormalCurve_a₆ (b c : ℚ) : (tateNormalCurve b c).a₆ = 0 := rfl

/-- The vertical tangent denominator used to normalize a marked affine
point to Tate normal form. -/
def pointTateBeta (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  W.a₃ + x * W.a₁ + 2 * y

/-- The tangent slope used in the first translation-shear of explicit Tate
normalization. -/
def pointTateLambda (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  (W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) /
    pointTateBeta W x y

/-- The quadratic coefficient after translating a marked affine point to
the origin and making its tangent horizontal. -/
def pointTateAlpha (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  W.a₂ - W.a₁ * pointTateLambda W x y + 3 * x -
    pointTateLambda W x y ^ 2

/-- The first Tate parameter produced by explicit normalization at an
affine point. -/
def pointTateB (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  -pointTateAlpha W x y ^ 3 / pointTateBeta W x y ^ 2

/-- The second Tate parameter produced by explicit normalization at an
affine point. -/
def pointTateC (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  (pointTateBeta W x y - pointTateAlpha W x y *
      (W.a₁ + 2 * pointTateLambda W x y)) /
    pointTateBeta W x y

/-- The ratio `b / c` produced by explicit Tate normalization at an affine
point. -/
def pointTateParameter (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  -pointTateAlpha W x y ^ 3 /
    (pointTateBeta W x y *
      (pointTateBeta W x y - pointTateAlpha W x y *
        (W.a₁ + 2 * pointTateLambda W x y)))

/-- The marked origin is nonsingular whenever the Tate parameter `b` is nonzero. -/
lemma tateNormalCurve_nonsingular_origin (b c : ℚ) (hb : b ≠ 0) :
    (tateNormalCurve b c).toAffine.Nonsingular 0 0 := by
  apply WeierstrassCurve.Affine.nonsingular_zero.mpr
  refine ⟨rfl, Or.inl ?_⟩
  simpa [tateNormalCurve] using neg_ne_zero.mpr hb

/-- If the tangent at the origin has triple contact, then the origin is killed by three.
This is the small group-law fact used during Tate normalization. -/
lemma three_nsmul_origin_eq_zero
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ = 0) (ha₄ : W.a₄ = 0)
    (ha₃ : W.a₃ ≠ 0) (h00 : W.toAffine.Nonsingular 0 0) :
    WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 = 0 := by
  have hvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    simp only [WeierstrassCurve.Affine.negY]
    intro h
    apply ha₃
    linarith
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hvertical]
    simp only [WeierstrassCurve.Affine.negY, ha₂, ha₄]
    ring_nf
  have hdouble :
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        -WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne' hvertical]
    congr 1
    refine WeierstrassCurve.Affine.Point.some_eq_some W ?_ ?_
    · simp only [WeierstrassCurve.Affine.addX, hslope, ha₂]
      ring
    · simp only [WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.addX, hslope, ha₂]
      ring
  rw [hdouble, neg_add_cancel]

/-- Tate normalization retaining the discriminant and `c₄` scaling
parameters. -/
theorem exists_tateNormalCurve_scaled
    (W : WeierstrassCurve ℚ)
    (P : W.toAffine.Point) (hP2 : P + P ≠ 0) (hP3 : P + P + P ≠ 0) :
    ∃ (b c u : ℚ) (_ : u ≠ 0) (_ : b ≠ 0)
      (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
      (e : W.toAffine.Point ≃+ (tateNormalCurve b c).toAffine.Point),
      e P = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * W.Δ = (tateNormalCurve b c).Δ ∧
        u ^ 4 * W.c₄ = (tateNormalCurve b c).c₄ ∧
        u ^ 6 * W.c₆ = (tateNormalCurve b c).c₆ := by
  obtain ⟨X, Y, hns, hPxy⟩ :
      ∃ (X Y : ℚ) (h : W.toAffine.Nonsingular X Y),
        P = WeierstrassCurve.Affine.Point.some X Y h := by
    rcases hcase : P with _ | ⟨X, Y, h⟩
    · exfalso
      apply hP2
      rw [hcase]
      simp [← WeierstrassCurve.Affine.Point.zero_def]
    · exact ⟨X, Y, h, rfl⟩
  have hnotvertical : Y ≠ W.toAffine.negY X Y := fun h =>
    hP2 (by
      rw [hPxy]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq h)
  have htangentDenom : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    intro h
    apply hnotvertical
    rw [WeierstrassCurve.Affine.negY]
    linarith
  set s : ℚ :=
    (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) /
      (W.a₃ + X * W.a₁ + 2 * Y) with hs
  set C₁ : WeierstrassCurve.VariableChange ℚ := ⟨1, X, s, Y⟩ with hC₁
  have hC₁a₃ : (C₁ • W).a₃ = W.a₃ + X * W.a₁ + 2 * Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]
    simp
  have hC₁a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hs]
    field_simp
    ring
  have hC₁a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00₁ : (C₁ • W).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₁a₆, Or.inl (by rw [hC₁a₃]; exact htangentDenom)⟩
  have hmap₁ :
      WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some, hPxy]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [hC₁]) (by simp [hC₁])
  have hC₁a₂ : (C₁ • W).a₂ ≠ 0 := by
    intro hzero
    apply hP3
    have htriple :
        WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 :=
      three_nsmul_origin_eq_zero (C₁ • W) hzero hC₁a₄
        (by rw [hC₁a₃]; exact htangentDenom) h00₁
    have himage :=
      congrArg (WeierstrassCurve.Affine.Point.equivVariableChange W C₁) htriple
    rwa [map_add, map_add, map_zero, hmap₁] at himage
  set scale : ℚˣ :=
    Units.mk0 ((C₁ • W).a₃ / (C₁ • W).a₂)
      (div_ne_zero (by rw [hC₁a₃]; exact htangentDenom) hC₁a₂)
  set C₂ : WeierstrassCurve.VariableChange ℚ := ⟨scale, 0, 0, 0⟩ with hC₂
  have hscale : (scale : ℚ) = (C₁ • W).a₃ / (C₁ • W).a₂ := rfl
  have hscale0 : (scale : ℚ) ≠ 0 := scale.ne_zero
  set b : ℚ := -(C₂ • (C₁ • W)).a₂ with hb
  set c : ℚ := 1 - (C₂ • (C₁ • W)).a₁ with hc
  have hC₂a₄ : (C₂ • (C₁ • W)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₂]
    simp [hC₁a₄]
  have hC₂a₆ : (C₂ • (C₁ • W)).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆, hC₂]
    simp [hC₁a₆]
  have hC₂a₂a₃ : (C₂ • (C₁ • W)).a₃ = (C₂ • (C₁ • W)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₂, hC₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [hscale]
    rw [hscale]
    field_simp
    ring
  have hC₂a₂ :
      (C₂ • (C₁ • W)).a₂ = ((scale : ℚ))⁻¹ ^ 2 * (C₁ • W).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂, hC₂]
    simp
  have hC₂a₂ne : (C₂ • (C₁ • W)).a₂ ≠ 0 := by
    rw [hC₂a₂]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hscale0)) hC₁a₂
  have hb0 : b ≠ 0 := by
    rw [hb, neg_ne_zero]
    exact hC₂a₂ne
  have hcurve :
      C₂ • (C₁ • W) = tateNormalCurve b c := by
    ext <;> simp [tateNormalCurve, hb, hc, hC₂a₄, hC₂a₆, hC₂a₂a₃]
  have h00₂ : (C₂ • (C₁ • W)).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₂a₆, Or.inl (by rw [hC₂a₂a₃]; exact hC₂a₂ne)⟩
  have hdisc :
      ((scale : ℚ))⁻¹ ^ 12 * W.Δ = (C₂ • (C₁ • W)).Δ := by
    rw [WeierstrassCurve.variableChange_Δ,
      WeierstrassCurve.variableChange_Δ, hC₁, hC₂]
    simp
  refine ⟨b, c, ((scale : ℚ))⁻¹, inv_ne_zero hscale0, hb0,
    hcurve ▸ h00₂,
    (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      ((WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (WeierstrassCurve.Affine.Point.equivOfEq hcurve)), ?_, ?_, ?_, ?_⟩
  · have hfirst :
        (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm_apply_apply _
    have hsecond :
        WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂
            (WeierstrassCurve.Affine.Point.some 0 0 h00₂) =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact WeierstrassCurve.Affine.Point.some_eq_some _
        (by simp [hC₂]) (by simp [hC₂])
    simp only [AddEquiv.trans_apply, hfirst, ← hsecond,
      AddEquiv.symm_apply_apply, WeierstrassCurve.Affine.Point.equivOfEq_some]
  · rw [hdisc, hcurve]
  · have hc₄ :
        ((scale : ℚ))⁻¹ ^ 4 * W.c₄ = (C₂ • (C₁ • W)).c₄ := by
      rw [WeierstrassCurve.variableChange_c₄,
        WeierstrassCurve.variableChange_c₄, hC₁, hC₂]
      simp
    rw [hc₄, hcurve]
  · have hc₆ :
        ((scale : ℚ))⁻¹ ^ 6 * W.c₆ = (C₂ • (C₁ • W)).c₆ := by
      rw [WeierstrassCurve.variableChange_c₆,
        WeierstrassCurve.variableChange_c₆, hC₁, hC₂]
      simp
    rw [hc₆, hcurve]

/-- The marked point `P = (0,0)` doubles to `(b,bc)` on Tate normal form. -/
theorem two_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  let W := tateNormalCurve b c
  have hneg : W.toAffine.negY 0 0 = b := by
    simp [W, tateNormalCurve, WeierstrassCurve.Affine.negY]
  have hnotvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    rw [hneg]
    exact fun h => hb h.symm
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hnotvertical]
    simp [W, tateNormalCurve]
  have hx :
      W.toAffine.addX 0 0 (W.toAffine.slope 0 0 0 0) = b := by
    rw [hslope]
    simp [W, tateNormalCurve]
  have hy :
      W.toAffine.addY 0 0 0 (W.toAffine.slope 0 0 0 0) = b * c := by
    rw [hslope]
    simp [W, tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  have h₂ : W.toAffine.Nonsingular b (b * c) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h00 h00
        (fun hxy => hnotvertical hxy.right)
    rwa [hx, hy] at h
  refine ⟨h₂, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hnotvertical]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- The marked point `P = (0,0)` triples to `(c,b-c)` on Tate normal form. -/
theorem three_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  let W := tateNormalCurve b c
  obtain ⟨h₂, hdouble⟩ := two_mul_origin_coordinates b c hb h00
  have hslope : W.toAffine.slope b 0 (b * c) 0 = c := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    field_simp
    ring
  have hx :
      W.toAffine.addX b 0 (W.toAffine.slope b 0 (b * c) 0) = c := by
    rw [hslope]
    simp [W, tateNormalCurve]
    ring
  have hy :
      W.toAffine.addY b 0 (b * c) (W.toAffine.slope b 0 (b * c) 0) =
        b - c := by
    rw [hslope]
    simp [W, tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  have h₃ : W.toAffine.Nonsingular c (b - c) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h₂ h00
        (fun hxy => hb hxy.left)
    rwa [hx, hy] at h
  refine ⟨h₃, ?_⟩
  rw [hdouble]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hb]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- In scalar-multiplication notation, `2P = (b,bc)` for the marked Tate point. -/
theorem two_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  simpa [two_nsmul] using two_mul_origin_coordinates b c hb h00

/-- In scalar-multiplication notation, `3P = (c,b-c)` for the marked Tate point. -/
theorem three_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  obtain ⟨h₃, htriple⟩ := three_mul_origin_coordinates b c hb h00
  refine ⟨h₃, ?_⟩
  rw [show (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  exact htriple

/-- If also `c ≠ 0`, then `4P` has the displayed rational coordinates. -/
theorem four_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₄ : (tateNormalCurve b c).toAffine.Nonsingular
        (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
              WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
  let W := tateNormalCurve b c
  obtain ⟨h₃, htriple⟩ := three_mul_origin_coordinates b c hb h00
  have hslope : W.toAffine.slope c 0 (b - c) 0 = (b - c) / c := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hc]
    ring
  have hx :
      W.toAffine.addX c 0 (W.toAffine.slope c 0 (b - c) 0) =
        b * (b - c) / c ^ 2 := by
    rw [hslope]
    simp [W, tateNormalCurve]
    field_simp [hc]
    ring
  have hy :
      W.toAffine.addY c 0 (b - c) (W.toAffine.slope c 0 (b - c) 0) =
        b ^ 2 * (c ^ 2 + c - b) / c ^ 3 := by
    rw [hslope]
    simp [W, tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    field_simp [hc]
    ring
  have h₄ : W.toAffine.Nonsingular
      (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h₃ h00
        (fun hxy => hc hxy.left)
    rwa [hx, hy] at h
  refine ⟨h₄, ?_⟩
  rw [htriple]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hc]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hx hy


end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen

export MazurTorsion.Kubert
  (tateNormalCurve three_nsmul_origin_eq_zero exists_tateNormalCurve_scaled
    two_mul_origin_coordinates three_mul_origin_coordinates
    two_nsmul_origin_coordinates three_nsmul_origin_coordinates
    four_mul_origin_coordinates)

end MazurTorsion.ExceptionalTwoTen

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

/-!
# Further multiples on Tate normal form

This file extends the kernel-checked low-multiple calculations for the marked point
`P = (0, 0)` on

`y² + (1-c)xy - by = x³ - bx²`.

The central lemma is a small recurrence: if `Q = (x, y)` and `x ≠ 0`, it computes `Q + P`.
The formulas for `5P` and `6P` are then consequences of the already checked formula for `4P`.
Every denominator used below has a corresponding explicit nonvanishing hypothesis.
-/
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The `X`-coordinate obtained by adding the marked Tate point `(0, 0)` to `(x, y)`. -/
def tateNextX (b c x y : ℚ) : ℚ :=
  (y / x) ^ 2 + (1 - c) * (y / x) + b - x

/-- The `Y`-coordinate obtained by adding the marked Tate point `(0, 0)` to `(x, y)`. -/
def tateNextY (b c x y : ℚ) : ℚ :=
  -((y / x) * (tateNextX b c x y - x) + y) -
      (1 - c) * tateNextX b c x y + b

/-- Kernel-checked recurrence for adding the marked point to an affine Tate-normal-form point.
The sole denominator introduced by the secant formula is recorded as `hx`. -/
theorem add_origin_coordinates
    (b c x y : ℚ) (hx : x ≠ 0)
    (hxy : (tateNormalCurve b c).toAffine.Nonsingular x y)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ hnext : (tateNormalCurve b c).toAffine.Nonsingular
        (tateNextX b c x y) (tateNextY b c x y),
      WeierstrassCurve.Affine.Point.some x y hxy +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (tateNextX b c x y) (tateNextY b c x y) hnext := by
  let W := tateNormalCurve b c
  have hslope : W.toAffine.slope x 0 y 0 = y / x := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    ring
  have hxnext :
      W.toAffine.addX x 0 (W.toAffine.slope x 0 y 0) =
        tateNextX b c x y := by
    rw [hslope]
    simp [W, tateNormalCurve, tateNextX]
  have hynext :
      W.toAffine.addY x 0 y (W.toAffine.slope x 0 y 0) =
        tateNextY b c x y := by
    rw [hslope]
    simp [W, tateNormalCurve, tateNextX, tateNextY,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY]
  have hnext :
      W.toAffine.Nonsingular (tateNextX b c x y) (tateNextY b c x y) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add hxy h00
        (fun hpair => hx hpair.left)
    rwa [hxnext, hynext] at h
  refine ⟨hnext, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hxnext hynext

/-- Successive affine coordinates obtained by starting at `2P = (b, bc)` and
repeatedly adding the marked Tate point `P = (0, 0)`.  Index `n` is intended
to represent `(n + 2)P`; the accompanying theorem records exactly the
nonzero abscissas needed for this rational recurrence to agree with the group
law. -/
def tateSuccessiveCoordinates (b c : ℚ) : ℕ → ℚ × ℚ
  | 0 => (b, b * c)
  | n + 1 =>
      let Q := tateSuccessiveCoordinates b c n
      (tateNextX b c Q.1 Q.2, tateNextY b c Q.1 Q.2)

/-- The recurrence-defined abscissa of `(n + 2)P`. -/
def tateSuccessiveX (b c : ℚ) (n : ℕ) : ℚ :=
  (tateSuccessiveCoordinates b c n).1

/-- The recurrence-defined ordinate of `(n + 2)P`. -/
def tateSuccessiveY (b c : ℚ) (n : ℕ) : ℚ :=
  (tateSuccessiveCoordinates b c n).2

@[simp] lemma tateSuccessiveX_zero (b c : ℚ) :
    tateSuccessiveX b c 0 = b := rfl

@[simp] lemma tateSuccessiveY_zero (b c : ℚ) :
    tateSuccessiveY b c 0 = b * c := rfl

@[simp] lemma tateSuccessiveX_succ (b c : ℚ) (n : ℕ) :
    tateSuccessiveX b c (n + 1) =
      tateNextX b c (tateSuccessiveX b c n) (tateSuccessiveY b c n) := by
  rfl

@[simp] lemma tateSuccessiveY_succ (b c : ℚ) (n : ℕ) :
    tateSuccessiveY b c (n + 1) =
      tateNextY b c (tateSuccessiveX b c n) (tateSuccessiveY b c n) := by
  rfl

/-- The rational recurrence computes `(n + 2)P` whenever every earlier
abscissa used as a secant denominator is nonzero. -/
theorem nsmul_origin_eq_successiveCoordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (n : ℕ) (hx : ∀ k < n, tateSuccessiveX b c k ≠ 0) :
    ∃ h : (tateNormalCurve b c).toAffine.Nonsingular
        (tateSuccessiveX b c n) (tateSuccessiveY b c n),
      (n + 2) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (tateSuccessiveX b c n) (tateSuccessiveY b c n) h := by
  induction n with
  | zero =>
      simpa using two_nsmul_origin_coordinates b c hb h00
  | succ n ih =>
      have hx' : ∀ k < n, tateSuccessiveX b c k ≠ 0 := by
        intro k hk
        exact hx k (Nat.lt_succ_of_lt hk)
      obtain ⟨hn, hncoord⟩ := ih hx'
      obtain ⟨hsucc, hsucccoord⟩ :=
        add_origin_coordinates b c
          (tateSuccessiveX b c n) (tateSuccessiveY b c n)
          (hx n (Nat.lt_succ_self n)) hn h00
      refine ⟨?_, ?_⟩
      · simpa using hsucc
      · rw [show n + 1 + 2 = (n + 2) + 1 by omega, add_nsmul,
          one_nsmul, hncoord, hsucccoord]
        rfl

/-- Fraction-free numerator and denominator data for one pair of Tate
recurrence coordinates. -/
structure TateClearedCoordinateDatum where
  /-- Numerator of the x-coordinate. -/ xNum : ℚ
  /-- Denominator of the x-coordinate. -/ xDen : ℚ
  /-- Numerator of the y-coordinate. -/ yNum : ℚ
  /-- Denominator of the y-coordinate. -/ yDen : ℚ

/-- One fraction-free step of the Tate recurrence.  No division occurs in
this definition; its specification theorem records the nonzero inputs needed
to recover `tateNextX` and `tateNextY`. -/
def tateClearedNext (b c : ℚ)
    (Q : TateClearedCoordinateDatum) : TateClearedCoordinateDatum :=
  let rNum := Q.yNum * Q.xDen
  let rDen := Q.yDen * Q.xNum
  let nextXNum :=
    rNum ^ 2 * Q.xDen +
      (1 - c) * rNum * rDen * Q.xDen +
      b * rDen ^ 2 * Q.xDen - Q.xNum * rDen ^ 2
  let nextXDen := rDen ^ 2 * Q.xDen
  let nextYNum :=
    -rNum * (nextXNum * Q.xDen - Q.xNum * nextXDen) * Q.yDen -
      Q.yNum * rDen * nextXDen * Q.xDen -
      (1 - c) * nextXNum * rDen * Q.xDen * Q.yDen +
      b * rDen * nextXDen * Q.xDen * Q.yDen
  let nextYDen := rDen * nextXDen * Q.xDen * Q.yDen
  ⟨nextXNum, nextXDen, nextYNum, nextYDen⟩

/-- Fraction-free coordinates corresponding to `tateSuccessiveCoordinates`.
Index zero is the cleared presentation `(b/1, bc/1)` of `2P`. -/
def tateClearedCoordinates (b c : ℚ) : ℕ → TateClearedCoordinateDatum
  | 0 => ⟨b, 1, b * c, 1⟩
  | n + 1 => tateClearedNext b c (tateClearedCoordinates b c n)

private lemma tateClearedNext_spec
    (b c : ℚ) (Q : TateClearedCoordinateDatum)
    (hxNum : Q.xNum ≠ 0) (hxDen : Q.xDen ≠ 0)
    (hyDen : Q.yDen ≠ 0) :
    let next := tateClearedNext b c Q
    next.xDen ≠ 0 ∧ next.yDen ≠ 0 ∧
      tateNextX b c (Q.xNum / Q.xDen) (Q.yNum / Q.yDen) =
        next.xNum / next.xDen ∧
      tateNextY b c (Q.xNum / Q.xDen) (Q.yNum / Q.yDen) =
        next.yNum / next.yDen := by
  dsimp only [tateClearedNext]
  have hrDen : Q.yDen * Q.xNum ≠ 0 := mul_ne_zero hyDen hxNum
  constructor
  · exact mul_ne_zero (pow_ne_zero 2 hrDen) hxDen
  constructor
  · exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hrDen
          (mul_ne_zero (pow_ne_zero 2 hrDen) hxDen))
        hxDen)
      hyDen
  constructor
  · simp only [tateNextX]
    field_simp [hxNum, hxDen, hyDen]
  · simp only [tateNextY, tateNextX]
    field_simp [hxNum, hxDen, hyDen]
    ring

/-- The fraction-free recurrence represents the rational Tate recurrence,
and all its denominators are nonzero whenever the abscissas used as secants
are nonzero. -/
theorem tateClearedCoordinates_spec
    (b c : ℚ) (n : ℕ)
    (hx : ∀ k < n, tateSuccessiveX b c k ≠ 0) :
    let Q := tateClearedCoordinates b c n
    Q.xDen ≠ 0 ∧ Q.yDen ≠ 0 ∧
      tateSuccessiveX b c n = Q.xNum / Q.xDen ∧
      tateSuccessiveY b c n = Q.yNum / Q.yDen := by
  induction n with
  | zero =>
      simp [tateClearedCoordinates]
  | succ n ih =>
      have hx' : ∀ k < n, tateSuccessiveX b c k ≠ 0 := by
        intro k hk
        exact hx k (Nat.lt_succ_of_lt hk)
      obtain ⟨hxDen, hyDen, hxEq, hyEq⟩ := ih hx'
      let Q := tateClearedCoordinates b c n
      have hxNum : Q.xNum ≠ 0 := by
        intro hxNum
        apply hx n (Nat.lt_succ_self n)
        rw [hxEq, hxNum]
        simp
      obtain ⟨hnextXDen, hnextYDen, hnextX, hnextY⟩ :=
        tateClearedNext_spec b c Q hxNum hxDen hyDen
      refine ⟨hnextXDen, hnextYDen, ?_, ?_⟩
      · rw [tateSuccessiveX_succ, hxEq, hyEq]
        exact hnextX
      · rw [tateSuccessiveY_succ, hxEq, hyEq]
        exact hnextY

/-- The `X`-coordinate of `5P` in Tate normal form. -/
def tateFiveX (b c : ℚ) : ℚ :=
  b * c * (c ^ 2 + c - b) / (b - c) ^ 2

/-- The `Y`-coordinate of `5P` in Tate normal form. -/
def tateFiveY (b c : ℚ) : ℚ :=
  b * c ^ 2 * (b ^ 2 - b * c - c ^ 3) / (b - c) ^ 3

/-- Provided `b`, `c`, and `b-c` are nonzero, the marked point has the displayed fifth
multiple. These are exactly the denominators used in the calculation. -/
theorem five_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₅ : (tateNormalCurve b c).toAffine.Nonsingular
        (tateFiveX b c) (tateFiveY b c),
      (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some (tateFiveX b c) (tateFiveY b c) h₅ := by
  let x₄ : ℚ := b * (b - c) / c ^ 2
  let y₄ : ℚ := b ^ 2 * (c ^ 2 + c - b) / c ^ 3
  obtain ⟨h₄, hfour⟩ := four_mul_origin_coordinates b c hb hc h00
  have hx₄ : x₄ ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hb (sub_ne_zero.mpr hbc))
      (pow_ne_zero 2 hc)
  obtain ⟨h₅, hfive⟩ := add_origin_coordinates b c x₄ y₄ hx₄ h₄ h00
  have hx :
      tateNextX b c x₄ y₄ = tateFiveX b c := by
    simp only [x₄, y₄, tateNextX, tateFiveX]
    field_simp [hc, sub_ne_zero.mpr hbc]
    ring
  have hy :
      tateNextY b c x₄ y₄ = tateFiveY b c := by
    simp only [x₄, y₄, tateNextY, tateNextX, tateFiveY]
    field_simp [hc, sub_ne_zero.mpr hbc]
    ring
  refine ⟨hx ▸ hy ▸ h₅, ?_⟩
  rw [show (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      (WeierstrassCurve.Affine.Point.some 0 0 h00 +
              WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00) +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  rw [hfour, hfive]
  exact WeierstrassCurve.Affine.Point.some_eq_some _ hx hy

/-- The recurrence-defined `X`-coordinate of `6P`. Keeping the sixth multiple in recurrence
form avoids expanding a much larger rational expression and makes subsequent calculations
share the same checked addition interface. -/
def tateSixX (b c : ℚ) : ℚ :=
  tateNextX b c (tateFiveX b c) (tateFiveY b c)

/-- The recurrence-defined `Y`-coordinate of `6P`. -/
def tateSixY (b c : ℚ) : ℚ :=
  tateNextY b c (tateFiveX b c) (tateFiveY b c)

/-- If the additional fifth-multiple numerator `c²+c-b` is nonzero, the recurrence computes
`6P`. Together with `b ≠ 0`, `c ≠ 0`, and `b ≠ c`, this is precisely what proves that the
`X`-coordinate of `5P` is nonzero. -/
theorem six_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₆ : (tateNormalCurve b c).toAffine.Nonsingular
        (tateSixX b c) (tateSixY b c),
      (6 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some (tateSixX b c) (tateSixY b c) h₆ := by
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hx₅ : tateFiveX b c ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero hb hc) hfiveNumerator)
      (pow_ne_zero 2 (sub_ne_zero.mpr hbc))
  obtain ⟨h₆, hsix⟩ :=
    add_origin_coordinates b c (tateFiveX b c) (tateFiveY b c) hx₅ h₅ h00
  refine ⟨h₆, ?_⟩
  rw [show (6 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  rw [hfive, hsix]
  rfl

end MazurTorsion.Kubert

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The order-five Tate family

The marked point `(0, 0)` on Tate normal form has exact order five precisely
on the diagonal `b = c`.  This file records that elementary group-law
reduction and the resulting one-parameter family

`y² + (1-c)xy - cy = x³ - cx²`.

The interface is kept in the Kubert layer because it is consumed both by the
exceptional `ZMod 2 × ZMod 10` argument and by the order-twenty-five
five-division normalization.  It asserts no quotient or Fricke transport.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The diagonal Tate-normal-form family with marked point of order five. -/
def orderFiveCurve (c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalCurve c c

@[simp] lemma orderFiveCurve_a₁ (c : ℚ) : (orderFiveCurve c).a₁ = 1 - c := rfl
@[simp] lemma orderFiveCurve_a₂ (c : ℚ) : (orderFiveCurve c).a₂ = -c := rfl
@[simp] lemma orderFiveCurve_a₃ (c : ℚ) : (orderFiveCurve c).a₃ = -c := rfl
@[simp] lemma orderFiveCurve_a₄ (c : ℚ) : (orderFiveCurve c).a₄ = 0 := rfl
@[simp] lemma orderFiveCurve_a₆ (c : ℚ) : (orderFiveCurve c).a₆ = 0 := rfl

/-- Discriminant of the order-five Tate family. -/
theorem orderFiveCurve_discriminant (c : ℚ) :
    (orderFiveCurve c).Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  simp only [orderFiveCurve, tateNormalCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- The polynomial giving the `c₄` invariant of the order-five family. -/
def orderFiveC4Polynomial (c : ℚ) : ℚ :=
  c ^ 4 - 12 * c ^ 3 + 14 * c ^ 2 + 12 * c + 1

/-- The `c₄` invariant of the order-five Tate family. -/
theorem orderFiveCurve_c₄ (c : ℚ) :
    (orderFiveCurve c).c₄ = orderFiveC4Polynomial c := by
  simp only [orderFiveCurve, tateNormalCurve, orderFiveC4Polynomial,
    WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

/-- Exact order five forces the two Tate parameters to coincide. -/
theorem tateNormalCurve_parameters_eq_of_order_five
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5) :
    b = c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  obtain ⟨hns₂, hdouble⟩ := two_mul_origin_coordinates b c hb h00
  obtain ⟨hns₃, htriple⟩ := three_mul_origin_coordinates b c hb h00
  have hfive : (5 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hsum : P + P + P + (P + P) = 0 := by
    rw [← hfive]
    abel
  rw [htriple, hdouble, add_eq_zero_iff_eq_neg,
    WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq] at hsum
  exact hsum.1.symm

/-- The marked origin on the diagonal family is killed by five. -/
theorem five_nsmul_orderFiveOrigin
    (c : ℚ) (hc : c ≠ 0)
    (h00 : (orderFiveCurve c).toAffine.Nonsingular 0 0) :
    (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (orderFiveCurve c).toAffine.Point) = 0 := by
  change (5 : ℕ) •
      (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve c c).toAffine.Point) = 0
  let P : (tateNormalCurve c c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  obtain ⟨h₂, hdouble⟩ :=
    two_mul_origin_coordinates c c hc h00
  obtain ⟨h₃, htriple⟩ :=
    three_mul_origin_coordinates c c hc h00
  have hneg :
      WeierstrassCurve.Affine.Point.some c (c - c) h₃ =
        -(WeierstrassCurve.Affine.Point.some c (c * c) h₂) := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some
      (orderFiveCurve c) rfl (by
        simp only [tateNormalCurve,
          WeierstrassCurve.Affine.negY]
        ring)
  calc
    (5 : ℕ) • P = (P + P + P) + (P + P) := by abel
    _ = WeierstrassCurve.Affine.Point.some c (c - c) h₃ +
          WeierstrassCurve.Affine.Point.some c (c * c) h₂ := by
        rw [htriple, hdouble]
    _ = 0 := by rw [hneg, neg_add_cancel]

/-- An affine point whose abscissa is one of the two poles of the paired
Vélu formula belongs to the marked order-five subgroup. -/
theorem five_nsmul_eq_zero_of_orderFive_kernel_abscissa
    {c x y : ℚ} (hc : c ≠ 0)
    (hP : (orderFiveCurve c).toAffine.Nonsingular x y)
    (hx : x = 0 ∨ x = c) :
    (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y hP :
          (orderFiveCurve c).toAffine.Point) = 0 := by
  change (tateNormalCurve c c).toAffine.Nonsingular x y at hP
  change (5 : ℕ) •
      (WeierstrassCurve.Affine.Point.some x y hP :
        (tateNormalCurve c c).toAffine.Point) = 0
  let h00 : (tateNormalCurve c c).toAffine.Nonsingular 0 0 :=
    tateNormalCurve_nonsingular_origin c c hc
  let O : (tateNormalCurve c c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveO : (5 : ℕ) • O = 0 :=
    five_nsmul_orderFiveOrigin c hc h00
  obtain ⟨h₂, hdouble⟩ :=
    two_mul_origin_coordinates c c hc h00
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  rcases hx with hx0 | hxc
  · subst x
    have hy : y = 0 ∨ y = c := by
      have hyprod : y * (y - c) = 0 := by
        simp only [tateNormalCurve_a₁, tateNormalCurve_a₂,
          tateNormalCurve_a₃, tateNormalCurve_a₄,
          tateNormalCurve_a₆] at hcurve
        linear_combination hcurve
      rcases mul_eq_zero.mp hyprod with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    rcases hy with hy0 | hyc
    · subst y
      simpa only [O] using hfiveO
    · have hneg :
          (WeierstrassCurve.Affine.Point.some 0 y hP :
              (tateNormalCurve c c).toAffine.Point) = -O := by
        change (WeierstrassCurve.Affine.Point.some 0 y hP :
            (tateNormalCurve c c).toAffine.Point) =
          -(WeierstrassCurve.Affine.Point.some 0 0 h00)
        rw [WeierstrassCurve.Affine.Point.neg_some]
        exact WeierstrassCurve.Affine.Point.some_eq_some
          (tateNormalCurve c c) rfl (by
            simp only [tateNormalCurve,
              WeierstrassCurve.Affine.negY]
            calc
              y = c := hyc
              _ = -0 - (1 - c) * 0 - -c := by ring)
      rw [hneg]
      calc
        (5 : ℕ) • (-O) = -((5 : ℕ) • O) := by abel
        _ = 0 := by rw [hfiveO, neg_zero]
  · subst x
    have hy : y = 0 ∨ y = c * c := by
      have hyprod : y * (y - c * c) = 0 := by
        simp only [tateNormalCurve_a₁, tateNormalCurve_a₂,
          tateNormalCurve_a₃, tateNormalCurve_a₄,
          tateNormalCurve_a₆] at hcurve
        linear_combination hcurve
      rcases mul_eq_zero.mp hyprod with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    have hfiveDouble :
        (5 : ℕ) •
            (WeierstrassCurve.Affine.Point.some c (c * c) h₂ :
              (tateNormalCurve c c).toAffine.Point) = 0 := by
      rw [← hdouble]
      change (5 : ℕ) • (O + O) = 0
      rw [nsmul_add, hfiveO, zero_add]
    rcases hy with hy0 | hyc
    · have hneg :
          (WeierstrassCurve.Affine.Point.some c y hP :
              (tateNormalCurve c c).toAffine.Point) =
            -(WeierstrassCurve.Affine.Point.some c (c * c) h₂) := by
        rw [WeierstrassCurve.Affine.Point.neg_some]
        exact WeierstrassCurve.Affine.Point.some_eq_some
          (tateNormalCurve c c) rfl (by
            simp only [tateNormalCurve,
              WeierstrassCurve.Affine.negY]
            rw [hy0]
            ring)
      rw [hneg]
      calc
        (5 : ℕ) •
            (-(WeierstrassCurve.Affine.Point.some c (c * c) h₂)) =
              -((5 : ℕ) •
                (WeierstrassCurve.Affine.Point.some c (c * c) h₂)) := by
                  abel
        _ = 0 := by rw [hfiveDouble, neg_zero]
    · have heq :
          (WeierstrassCurve.Affine.Point.some c y hP :
              (tateNormalCurve c c).toAffine.Point) =
            WeierstrassCurve.Affine.Point.some c (c * c) h₂ := by
        exact WeierstrassCurve.Affine.Point.some_eq_some
          (tateNormalCurve c c) rfl hyc
      rw [heq]
      exact hfiveDouble

/-- Explicit Tate normalization at an affine point of exact order five
produces equal, nonzero Tate parameters. This pins down the parameter chosen
by the normalization, rather than merely asserting that some order-five
parameter exists. -/
theorem pointTate_parameters_eq_of_order_five
    (W : WeierstrassCurve ℚ)
    {X Y : ℚ} (hns : W.toAffine.Nonsingular X Y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some X Y hns :
        W.toAffine.Point) = 5) :
    pointTateBeta W X Y ≠ 0 ∧
      pointTateAlpha W X Y ≠ 0 ∧
      pointTateB W X Y = pointTateC W X Y ∧
      pointTateC W X Y ≠ 0 := by
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some X Y hns
  have hnot : ∀ n : ℕ, ¬(5 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (horder ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hP2 : P + P ≠ 0 := by
    intro h
    exact hnot 2 (by norm_num) (by simpa [two_nsmul] using h)
  have hP3 : P + P + P ≠ 0 := by
    intro h
    exact hnot 3 (by norm_num) (by
      rw [show (3 : ℕ) • P = P + P + P by abel]
      exact h)
  have hnotvertical : Y ≠ W.toAffine.negY X Y := fun h ↦
    hP2 (by
      dsimp only [P]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq h)
  have hbeta : pointTateBeta W X Y ≠ 0 := by
    intro h
    apply hnotvertical
    rw [WeierstrassCurve.Affine.negY]
    unfold pointTateBeta at h
    linarith
  have htangentDenom : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    simpa only [pointTateBeta] using hbeta
  set lambda : ℚ :=
    (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) /
      (W.a₃ + X * W.a₁ + 2 * Y) with hlambda
  have hlambdaPoint : lambda = pointTateLambda W X Y := by
    rw [hlambda]
    rfl
  set C₁ : WeierstrassCurve.VariableChange ℚ := ⟨1, X, lambda, Y⟩ with hC₁
  have hC₁a₃ : (C₁ • W).a₃ = pointTateBeta W X Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]
    simp [pointTateBeta]
  have hC₁a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hlambda]
    field_simp [htangentDenom]
    ring
  have hC₁a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have hC₁a₂ : (C₁ • W).a₂ = pointTateAlpha W X Y := by
    rw [WeierstrassCurve.variableChange_a₂, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    simp only [pointTateAlpha]
    rw [← hlambdaPoint]
    ring
  have h00₁ : (C₁ • W).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₁a₆, Or.inl (by rw [hC₁a₃]; exact hbeta)⟩
  have hmap₁ :
      WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
    dsimp only [P]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [C₁]) (by simp [C₁])
  have halpha : pointTateAlpha W X Y ≠ 0 := by
    rw [← hC₁a₂]
    intro hzero
    apply hP3
    have htriple :
        WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 :=
      three_nsmul_origin_eq_zero (C₁ • W) hzero hC₁a₄
        (by rw [hC₁a₃]; exact hbeta) h00₁
    have himage :=
      congrArg (WeierstrassCurve.Affine.Point.equivVariableChange W C₁)
        htriple
    rwa [map_add, map_add, map_zero, hmap₁] at himage
  let scale : ℚˣ := Units.mk0
    (pointTateBeta W X Y / pointTateAlpha W X Y)
    (div_ne_zero hbeta halpha)
  let C₂ : WeierstrassCurve.VariableChange ℚ := ⟨scale, 0, 0, 0⟩
  have hscale : (scale : ℚ) =
      pointTateBeta W X Y / pointTateAlpha W X Y := rfl
  have hscale0 : (scale : ℚ) ≠ 0 := scale.ne_zero
  let b : ℚ := -(C₂ • (C₁ • W)).a₂
  let c : ℚ := 1 - (C₂ • (C₁ • W)).a₁
  have hC₂a₄ : (C₂ • (C₁ • W)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄]
    simp [C₂, hC₁a₄]
  have hC₂a₆ : (C₂ • (C₁ • W)).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆]
    simp [C₂, hC₁a₆]
  have hC₂a₂a₃ :
      (C₂ • (C₁ • W)).a₃ = (C₂ • (C₁ • W)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₂]
    simp only [C₂, Units.val_inv_eq_inv_val]
    rw [hC₁a₃, hC₁a₂, hscale]
    field_simp [hbeta, halpha]
    ring
  have hC₂a₂ :
      (C₂ • (C₁ • W)).a₂ =
        ((scale : ℚ))⁻¹ ^ 2 * (C₁ • W).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂]
    simp [C₂]
  have hC₂a₂ne : (C₂ • (C₁ • W)).a₂ ≠ 0 := by
    rw [hC₂a₂, hC₁a₂]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hscale0)) halpha
  have hb0 : b ≠ 0 := by
    dsimp only [b]
    exact neg_ne_zero.mpr hC₂a₂ne
  have hcurve : C₂ • (C₁ • W) = tateNormalCurve b c := by
    ext <;> simp [tateNormalCurve, b, c, hC₂a₄, hC₂a₆,
      hC₂a₂a₃]
  have h00₂ : (C₂ • (C₁ • W)).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₂a₆, Or.inl (by rw [hC₂a₂a₃]; exact hC₂a₂ne)⟩
  let h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0 :=
    hcurve ▸ h00₂
  let e : W.toAffine.Point ≃+ (tateNormalCurve b c).toAffine.Point :=
    (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      ((WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (WeierstrassCurve.Affine.Point.equivOfEq hcurve))
  have heP : e P = WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    have hfirst :
        (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm_apply_apply _
    have hsecond :
        WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂
            (WeierstrassCurve.Affine.Point.some 0 0 h00₂) =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact WeierstrassCurve.Affine.Point.some_eq_some _
        (by simp [C₂]) (by simp [C₂])
    simp only [e, AddEquiv.trans_apply, hfirst, ← hsecond,
      AddEquiv.symm_apply_apply, WeierstrassCurve.Affine.Point.equivOfEq_some]
  have horderOrigin :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5 := by
    rw [← heP, AddEquiv.addOrderOf_eq]
    exact horder
  have hbc : b = c :=
    tateNormalCurve_parameters_eq_of_order_five b c hb0 h00 horderOrigin
  have hbFormula : b = pointTateB W X Y := by
    dsimp only [b, pointTateB]
    rw [hC₂a₂, hC₁a₂, hscale]
    field_simp [hbeta, halpha]
  have hcFormula : c = pointTateC W X Y := by
    dsimp only [c, pointTateC]
    rw [WeierstrassCurve.variableChange_a₁]
    simp only [C₂, Units.val_inv_eq_inv_val]
    rw [WeierstrassCurve.variableChange_a₁]
    simp only [C₁, inv_one, Units.val_one, one_mul]
    rw [hlambdaPoint, hscale]
    field_simp [hbeta, halpha]
    ring
  have hparameters : pointTateB W X Y = pointTateC W X Y :=
    hbFormula.symm.trans (hbc.trans hcFormula)
  refine ⟨hbeta, halpha, hparameters, ?_⟩
  rw [← hparameters, ← hbFormula]
  exact hb0

/-- An exact order-five point admits order-five Tate normalization while
retaining the invariant scales and the marked-point equivalence. -/
theorem exists_orderFiveCurve_scaled
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (horder : addOrderOf P = 5) :
    ∃ (c u : ℚ) (_ : c ≠ 0) (_ : c ^ 2 - 11 * c - 1 ≠ 0)
      (_ : u ≠ 0)
      (h00 : (orderFiveCurve c).toAffine.Nonsingular 0 0)
      (e : W.toAffine.Point ≃+ (orderFiveCurve c).toAffine.Point),
      e P = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * W.Δ = (orderFiveCurve c).Δ ∧
        u ^ 4 * W.c₄ = (orderFiveCurve c).c₄ ∧
        u ^ 6 * W.c₆ = (orderFiveCurve c).c₆ := by
  have hnot : ∀ n : ℕ, ¬ (5 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (horder ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hP2 : P + P ≠ 0 := by
    intro hzero
    apply hnot 2 (by norm_num)
    simpa only [two_nsmul] using hzero
  have hP3 : P + P + P ≠ 0 := by
    intro hzero
    apply hnot 3 (by norm_num)
    calc
      (3 : ℕ) • P = P + P + P := by abel
      _ = 0 := hzero
  obtain ⟨b, c, u, hu, hb, h00, e, heP, hdisc, hc₄, hc₆⟩ :=
    exists_tateNormalCurve_scaled W P hP2 hP3
  have horderOrigin :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5 := by
    rw [← heP, AddEquiv.addOrderOf_eq]
    exact horder
  have hbc : b = c :=
    tateNormalCurve_parameters_eq_of_order_five b c hb h00 horderOrigin
  subst b
  have hfactor : c ^ 2 - 11 * c - 1 ≠ 0 := by
    intro hzero
    have hDeltaZero : (orderFiveCurve c).Δ = 0 := by
      rw [orderFiveCurve_discriminant, hzero, mul_zero]
    have hdiscFive : u ^ 12 * W.Δ = (orderFiveCurve c).Δ := by
      exact hdisc
    have hDeltaNe : (orderFiveCurve c).Δ ≠ 0 := by
      rw [← hdiscFive]
      exact mul_ne_zero (pow_ne_zero 12 hu) W.isUnit_Δ.ne_zero
    exact hDeltaNe hDeltaZero
  exact ⟨c, u, hb, hfactor, hu, h00, e, heP, hdisc, hc₄, hc₆⟩

/-- Eliminating the normalization scale gives the cleared `j`-identity
attached to an exact order-five point.  This is the invariant interface used
to compare the original marked five-subgroup with a residual five-subgroup
on an isogenous quotient. -/
theorem exists_orderFiveParameter_relation_of_exactOrder
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (horder : addOrderOf P = 5) :
    ∃ c : ℚ, c ≠ 0 ∧ c ^ 2 - 11 * c - 1 ≠ 0 ∧
      orderFiveC4Polynomial c ^ 3 * W.Δ =
        W.c₄ ^ 3 * (c ^ 5 * (c ^ 2 - 11 * c - 1)) := by
  obtain ⟨c, u, hc, hfactor, -, -, -, -, hdisc, hc₄, -⟩ :=
    exists_orderFiveCurve_scaled W P horder
  refine ⟨c, hc, hfactor, ?_⟩
  calc
    orderFiveC4Polynomial c ^ 3 * W.Δ =
        (orderFiveCurve c).c₄ ^ 3 * W.Δ := by
      rw [orderFiveCurve_c₄]
    _ = (u ^ 4 * W.c₄) ^ 3 * W.Δ := by rw [hc₄]
    _ = W.c₄ ^ 3 * (u ^ 12 * W.Δ) := by ring
    _ = W.c₄ ^ 3 * (orderFiveCurve c).Δ := by rw [hdisc]
    _ = W.c₄ ^ 3 *
        (c ^ 5 * (c ^ 2 - 11 * c - 1)) := by
      rw [orderFiveCurve_discriminant]

end MazurTorsion.Kubert

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

/-!
# The direct two-by-ten obstruction

This file carries the exceptional subgroup `ZMod 2 × ZMod 10` from the group law on a rational
elliptic curve to one explicit Diophantine endpoint.  A point of order five is put into Tate normal
form

`y² + (1-c)xy - cy = x³ - cx²`.

Full rational two-torsion makes the Weierstrass discriminant a square.  Since the Tate-form
discriminant is `c⁵(c² - 11c - 1)`, clearing denominators reduces the obstruction to the quartic

`e² = X⁴ - 11X²Y² - Y⁴`

for coprime nonzero integers `X` and `Y`.  The public predicate `NoExceptionalQuartic` states
precisely this remaining infinite-descent input.  The final theorem proves the forbidden embedding
conditionally on that single arithmetic statement; all geometric, group-theoretic, denominator,
sign, and coprimality reductions are completed here.

The Tate-normal-form formulas are the classical Kubert formulas.  The coordinate-change and
three-root cubic infrastructure used below is supplied by the project's Apache-licensed elliptic
curve foundations.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion
namespace ExceptionalTwoTen

/-- The order-five diagonal in the Tate-normal-form family. -/
def tateFiveCurve (c : ℚ) : WeierstrassCurve ℚ :=
  Kubert.orderFiveCurve c

@[simp] lemma tateFiveCurve_a₁ (c : ℚ) : (tateFiveCurve c).a₁ = 1 - c := rfl
@[simp] lemma tateFiveCurve_a₂ (c : ℚ) : (tateFiveCurve c).a₂ = -c := rfl
@[simp] lemma tateFiveCurve_a₃ (c : ℚ) : (tateFiveCurve c).a₃ = -c := rfl
@[simp] lemma tateFiveCurve_a₄ (c : ℚ) : (tateFiveCurve c).a₄ = 0 := rfl
@[simp] lemma tateFiveCurve_a₆ (c : ℚ) : (tateFiveCurve c).a₆ = 0 := rfl

/-- The cubic whose roots are the abscissae of the nonzero two-torsion. -/
def twoDivisionCubic (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

/-- Explicit two-division cubic of the order-five Tate family. -/
lemma twoDivisionCubic_tateFiveCurve (c x : ℚ) :
    twoDivisionCubic (tateFiveCurve c) x =
      4 * x ^ 3 + (c ^ 2 - 6 * c + 1) * x ^ 2 +
        2 * (c ^ 2 - c) * x + c ^ 2 := by
  simp only [twoDivisionCubic, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, tateFiveCurve_a₁, tateFiveCurve_a₂,
    tateFiveCurve_a₃, tateFiveCurve_a₄, tateFiveCurve_a₆]
  ring

/-- Discriminant of the order-five Tate family. -/
lemma tateFiveCurve_discriminant (c : ℚ) :
    (tateFiveCurve c).Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  exact Kubert.orderFiveCurve_discriminant c

/-- Exact order five forces the two Tate parameters to coincide. -/
lemma tateNormalCurve_parameters_eq_of_order_five
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5) :
    b = c := by
  exact Kubert.tateNormalCurve_parameters_eq_of_order_five
    b c hb h00 horder

/-- A rational point of exact order five produces a nonzero diagonal Tate
parameter and an explicit twelfth-power discriminant scaling. -/
theorem exists_tateFive_discriminant_of_order_five
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 5) :
    ∃ c u : ℚ, u ≠ 0 ∧ c ≠ 0 ∧
      u ^ 12 * E.Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have hQ2 : Q + Q ≠ 0 := by
    intro h
    have hdvd : addOrderOf Q ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hQ] at hdvd
    norm_num at hdvd
  have hQ3 : Q + Q + Q ≠ 0 := by
    intro h
    have hdvd : addOrderOf Q ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        have hthree : (3 : ℕ) • Q = Q + Q + Q := by abel
        rw [hthree]
        exact h)
    rw [hQ] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, -, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) Q hQ2 hQ3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hbc : b = c :=
    tateNormalCurve_parameters_eq_of_order_five b c hb h00 hmarked
  subst c
  refine ⟨b, u, hu, hb, ?_⟩
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  rw [← hbase, hdisc]
  exact tateFiveCurve_discriminant b

/-- The single Diophantine leaf needed by the direct exceptional
`ZMod 2 × ZMod 10` obstruction. -/
def NoExceptionalQuartic : Prop :=
  ∀ {X Y e : ℤ}, IsCoprime X Y → X ≠ 0 → Y ≠ 0 →
    e ^ 2 ≠ X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4

/-- Assuming the quartic leaf, a coprime product in the conductor-twenty
two-descent cannot be a square. -/
theorem not_isSquare_coprime_product
    (hquartic : NoExceptionalQuartic) {m n : ℤ}
    (hmn : IsCoprime m n) (hm : m ≠ 0) (hn : 0 < n) :
    ¬ IsSquare (m * n * (m ^ 2 - 11 * m * n - n ^ 2)) := by
  intro hsq
  set k : ℤ := m ^ 2 - 11 * m * n - n ^ 2 with hkdef
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hkdef] at hk
    have hA : (2 * m - 11 * n) ^ 2 = 125 * n ^ 2 := by
      linear_combination 4 * hk
    obtain ⟨A₁, hA₁⟩ : (5 : ℤ) ∣ (2 * m - 11 * n) := by
      apply Int.Prime.dvd_pow' (k := 2) (by decide : Nat.Prime 5)
      refine ⟨25 * n ^ 2, ?_⟩
      push_cast
      linear_combination hA
    have hA₁sq : A₁ ^ 2 = 5 * n ^ 2 := by
      have h25 : (25 : ℤ) * A₁ ^ 2 = 25 * (5 * n ^ 2) := by
        linear_combination hA - (2 * m - 11 * n + 5 * A₁) * hA₁
      linarith
    obtain ⟨A₂, hA₂⟩ : (5 : ℤ) ∣ A₁ := by
      apply Int.Prime.dvd_pow' (k := 2) (by decide : Nat.Prime 5)
      refine ⟨n ^ 2, ?_⟩
      push_cast
      linear_combination hA₁sq
    have hnsq : n ^ 2 = 5 * A₂ ^ 2 := by
      have h5 : (5 : ℤ) * n ^ 2 = 5 * (5 * A₂ ^ 2) := by
        linear_combination -hA₁sq + (A₁ + 5 * A₂) * hA₂
      linarith
    have hfive_n : (5 : ℤ) ∣ n := by
      apply Int.Prime.dvd_pow' (k := 2) (by decide : Nat.Prime 5)
      refine ⟨A₂ ^ 2, ?_⟩
      push_cast
      linear_combination hnsq
    obtain ⟨n₁, hn₁⟩ := id hfive_n
    have hm5 : (5 : ℤ) ∣ m := by
      have h2m : (5 : ℤ) ∣ 2 * m :=
        ⟨A₁ + 11 * n₁, by linear_combination hA₁ + 11 * hn₁⟩
      rcases Int.Prime.dvd_mul' (by decide : Nat.Prime 5) h2m with h5two | h5m
      · norm_num at h5two
      · push_cast at h5m
        exact h5m
    exact absurd (Int.isUnit_iff.mp (hmn.isUnit_of_dvd' hm5 hfive_n)) (by norm_num)
  have hmk : IsCoprime m k := by
    have h := ((hmn.pow_right (n := 2)).neg_right).add_mul_left_right (m - 11 * n)
    have heq : -n ^ 2 + m * (m - 11 * n) = k := by
      rw [hkdef]
      ring
    rwa [heq] at h
  have hnk : IsCoprime n k := by
    have h := (hmn.symm.pow_right (n := 2)).add_mul_left_right (-(11 * m) - n)
    have heq : m ^ 2 + n * (-(11 * m) - n) = k := by
      rw [hkdef]
      ring
    rwa [heq] at h
  obtain ⟨s, hs⟩ := hsq
  obtain ⟨b, hb⟩ : ∃ b : ℤ, n = b ^ 2 ∨ n = -b ^ 2 :=
    Int.sq_of_isCoprime (hmn.symm.mul_right hnk) (c := s)
      (by linear_combination hs)
  obtain ⟨a, ha⟩ : ∃ a : ℤ, m = a ^ 2 ∨ m = -a ^ 2 :=
    Int.sq_of_isCoprime (hmn.mul_right hmk) (c := s)
      (by linear_combination hs)
  obtain ⟨e, he⟩ : ∃ e : ℤ, k = e ^ 2 ∨ k = -e ^ 2 :=
    Int.sq_of_isCoprime (hmk.symm.mul_right hnk.symm) (c := s)
      (by linear_combination hs)
  have hbn : n = b ^ 2 := by
    rcases hb with hb | hb
    · exact hb
    · exfalso
      linarith [sq_nonneg b]
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb] at hbn
    norm_num at hbn
    linarith
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    apply hm
    rcases ha with ha | ha <;> simpa using ha
  have hprod : 0 < m * n * k := by
    refine lt_of_le_of_ne ?_ (Ne.symm (mul_ne_zero (mul_ne_zero hm hn.ne') hk0))
    rw [hs]
    exact mul_self_nonneg s
  have hmkpos : 0 < m * k := by
    by_contra h
    have hnonpos : m * k ≤ 0 := not_lt.mp h
    have : m * k * n ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hnonpos, hn.le⟩)
    linarith
  have hab : IsCoprime a b := by
    have hsquares : IsCoprime (a ^ 2) (b ^ 2) := by
      rcases ha with ha | ha
      · rw [← ha, ← hbn]
        exact hmn
      · have hneg : IsCoprime (-(a ^ 2)) (b ^ 2) := by
          rw [← ha, ← hbn]
          exact hmn
        simpa using hneg.neg_left
    have ha_dvd : a ∣ a ^ 2 := dvd_pow_self a (by norm_num)
    have hb_dvd : b ∣ b ^ 2 := dvd_pow_self b (by norm_num)
    have hba_sq : IsCoprime (b ^ 2) a :=
      (hsquares.of_isCoprime_of_dvd_left ha_dvd).symm
    have hba : IsCoprime b a := hba_sq.of_isCoprime_of_dvd_left hb_dvd
    exact hba.symm
  rcases ha with hma | hma <;> rcases he with hke | hke
  · have hq : e ^ 2 = a ^ 4 - 11 * a ^ 2 * b ^ 2 - b ^ 4 := by
      rw [← hke, hkdef, hma, hbn]
      ring
    exact hquartic hab ha0 hb0 hq
  · rw [hma, hke] at hmkpos
    nlinarith [sq_nonneg a, sq_nonneg e]
  · rw [hma, hke] at hmkpos
    nlinarith [sq_nonneg a, sq_nonneg e]
  · have hq0 : -e ^ 2 = a ^ 4 + 11 * a ^ 2 * b ^ 2 - b ^ 4 := by
      rw [← hke, hkdef, hma, hbn]
      ring
    have hq : e ^ 2 = b ^ 4 - 11 * b ^ 2 * a ^ 2 - a ^ 4 := by
      linarith
    exact hquartic hab.symm hb0 ha0 hq

/-- Clearing denominators turns a nonzero rational point on
`v² = c³ - 11c² - c` into the integral product certificate. -/
lemma integral_certificate_of_rational_solution
    {c v : ℚ} (hcurve : v ^ 2 = c ^ 3 - 11 * c ^ 2 - c) :
    IsSquare
      (c.num * (c.den : ℤ) *
        (c.num ^ 2 - 11 * c.num * (c.den : ℤ) - (c.den : ℤ) ^ 2)) := by
  rw [← Rat.isSquare_intCast_iff]
  refine ⟨v * (c.den : ℚ) ^ 2, ?_⟩
  have hden : ((c.den : ℚ)) ≠ 0 := by
    exact_mod_cast c.den_ne_zero
  have hnum : (c.num : ℚ) = c * (c.den : ℚ) :=
    (div_eq_iff hden).mp (Rat.num_div_den c)
  push_cast
  rw [hnum]
  linear_combination -((c.den : ℚ)) ^ 4 * hcurve

/-- The exceptional quartic leaf rules out all nonzero rational points on
the conductor-twenty curve. -/
theorem no_rational_solution
    (hquartic : NoExceptionalQuartic) {c v : ℚ} (hc : c ≠ 0) :
    v ^ 2 ≠ c ^ 3 - 11 * c ^ 2 - c := by
  intro hcurve
  have hcoprime : IsCoprime c.num (c.den : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using c.reduced)
  have hnum : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  have hden : (0 : ℤ) < (c.den : ℤ) := by
    exact_mod_cast c.den_pos
  exact not_isSquare_coprime_product hquartic hcoprime hnum hden
    (integral_certificate_of_rational_solution hcurve)

/-- Combining a square discriminant with the order-five Tate discriminant
produces a rational point on the conductor-twenty curve. -/
lemma conductorTwenty_solution_of_discriminants
    {c u D t : ℚ} (hc : c ≠ 0)
    (htate : u ^ 12 * D = c ^ 5 * (c ^ 2 - 11 * c - 1))
    (hsquare : D = t ^ 2) :
    (u ^ 6 * t / c ^ 2) ^ 2 = c ^ 3 - 11 * c ^ 2 - c := by
  rw [div_pow, div_eq_iff (pow_ne_zero 2 (pow_ne_zero 2 hc))]
  linear_combination htate - u ^ 12 * hsquare

/-- A nonzero point killed by two has affine coordinates in which its
ordinate is determined by its abscissa. -/
lemma exists_two_torsion_coordinates
    {W : WeierstrassCurve.Affine ℚ} (T : W.Point)
    (hT2 : T + T = 0) (hT0 : T ≠ 0) :
    ∃ x y : ℚ,
      (∃ hns : W.Nonsingular x y,
        T = WeierstrassCurve.Affine.Point.some x y hns) ∧
      W.Equation x y ∧ y = W.negY x y := by
  rcases T with _ | ⟨x, y, hns⟩
  · exact (hT0 rfl).elim
  · have hneg :
        -WeierstrassCurve.Affine.Point.some x y hns =
          WeierstrassCurve.Affine.Point.some x y hns :=
      neg_eq_of_add_eq_zero_left hT2
    rw [WeierstrassCurve.Affine.Point.neg_some] at hneg
    have hy : W.negY x y = y :=
      (WeierstrassCurve.Affine.Point.some.inj hneg).2
    exact ⟨x, y, ⟨hns, rfl⟩, hns.1, hy.symm⟩

/-- Full rational two-torsion forces the Weierstrass discriminant to be
a rational square. -/
theorem exists_discriminant_square_of_full_two_torsion
    (E : WeierstrassCurve ℚ)
    (f : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ d : ℚ, E.Δ = d ^ 2 := by
  have htwo₁ : f (1, 0) + f (1, 0) = 0 := by
    rw [← map_add, show ((1 : ZMod 2), (0 : ZMod 2)) + (1, 0) = 0 by decide,
      map_zero]
  have htwo₂ : f (0, 1) + f (0, 1) = 0 := by
    rw [← map_add, show ((0 : ZMod 2), (1 : ZMod 2)) + (0, 1) = 0 by decide,
      map_zero]
  have htwo₃ : f (1, 1) + f (1, 1) = 0 := by
    rw [← map_add, show ((1 : ZMod 2), (1 : ZMod 2)) + (1, 1) = 0 by decide,
      map_zero]
  have hne₁ : f (1, 0) ≠ 0 := fun h =>
    (by
      apply (show ((1 : ZMod 2), (0 : ZMod 2)) ≠ 0 by decide)
      exact hf (h.trans (map_zero f).symm))
  have hne₂ : f (0, 1) ≠ 0 := fun h =>
    (by
      apply (show ((0 : ZMod 2), (1 : ZMod 2)) ≠ 0 by decide)
      exact hf (h.trans (map_zero f).symm))
  have hne₃ : f (1, 1) ≠ 0 := fun h =>
    (by
      apply (show ((1 : ZMod 2), (1 : ZMod 2)) ≠ 0 by decide)
      exact hf (h.trans (map_zero f).symm))
  have hne₁₂ : f (1, 0) ≠ f (0, 1) := fun h =>
    (show ((1 : ZMod 2), (0 : ZMod 2)) ≠ (0, 1) by decide) (hf h)
  have hne₁₃ : f (1, 0) ≠ f (1, 1) := fun h =>
    (show ((1 : ZMod 2), (0 : ZMod 2)) ≠ (1, 1) by decide) (hf h)
  have hne₂₃ : f (0, 1) ≠ f (1, 1) := fun h =>
    (show ((0 : ZMod 2), (1 : ZMod 2)) ≠ (1, 1) by decide) (hf h)
  obtain ⟨x₁, y₁, ⟨hns₁, hpoint₁⟩, heq₁, hneg₁⟩ :=
    exists_two_torsion_coordinates (f (1, 0)) htwo₁ hne₁
  obtain ⟨x₂, y₂, ⟨hns₂, hpoint₂⟩, heq₂, hneg₂⟩ :=
    exists_two_torsion_coordinates (f (0, 1)) htwo₂ hne₂
  obtain ⟨x₃, y₃, ⟨hns₃, hpoint₃⟩, heq₃, hneg₃⟩ :=
    exists_two_torsion_coordinates (f (1, 1)) htwo₃ hne₃
  rw [WeierstrassCurve.Affine.negY] at hneg₁ hneg₂ hneg₃
  rw [WeierstrassCurve.Affine.equation_iff] at heq₁ heq₂ heq₃
  have hx₁₂ : x₁ ≠ x₂ := by
    intro hx
    subst x₂
    have hy : y₁ = y₂ := by linarith
    subst y₂
    rw [hpoint₁, hpoint₂] at hne₁₂
    exact hne₁₂ rfl
  have hx₁₃ : x₁ ≠ x₃ := by
    intro hx
    subst x₃
    have hy : y₁ = y₃ := by linarith
    subst y₃
    rw [hpoint₁, hpoint₃] at hne₁₃
    exact hne₁₃ rfl
  have hx₂₃ : x₂ ≠ x₃ := by
    intro hx
    subst x₃
    have hy : y₂ = y₃ := by linarith
    subst y₃
    rw [hpoint₂, hpoint₃] at hne₂₃
    exact hne₂₃ rfl
  have hroot₁ :
      4 * x₁ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * x₁ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * x₁ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * y₁ + (E⁄ℚ).a₁ * x₁ + (E⁄ℚ).a₃) * hneg₁ - 4 * heq₁
  have hroot₂ :
      4 * x₂ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * x₂ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * x₂ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * y₂ + (E⁄ℚ).a₁ * x₂ + (E⁄ℚ).a₃) * hneg₂ - 4 * heq₂
  have hroot₃ :
      4 * x₃ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * x₃ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * x₃ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * y₃ + (E⁄ℚ).a₁ * x₃ + (E⁄ℚ).a₃) * hneg₃ - 4 * heq₃
  obtain ⟨hb₂, hb₄, hb₆⟩ :=
    FullFour.cubic_coefficients_of_three_roots
      hx₁₂ hx₁₃ hx₂₃ hroot₁ hroot₂ hroot₃
  have ha₁ : (E⁄ℚ).a₁ = E.a₁ := by simp [WeierstrassCurve.baseChange]
  have ha₂ : (E⁄ℚ).a₂ = E.a₂ := by simp [WeierstrassCurve.baseChange]
  have ha₃ : (E⁄ℚ).a₃ = E.a₃ := by simp [WeierstrassCurve.baseChange]
  have ha₄ : (E⁄ℚ).a₄ = E.a₄ := by simp [WeierstrassCurve.baseChange]
  have ha₆ : (E⁄ℚ).a₆ = E.a₆ := by simp [WeierstrassCurve.baseChange]
  simp only [ha₁, ha₂, ha₃, ha₄, ha₆] at hb₂ hb₄ hb₆
  have hB₂ : E.b₂ = -4 * (x₁ + x₂ + x₃) := by
    simp only [WeierstrassCurve.b₂]
    linarith
  have hB₄ : E.b₄ = 2 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) := by
    simp only [WeierstrassCurve.b₄]
    linarith
  have hB₆ : E.b₆ = -4 * (x₁ * x₂ * x₃) := by
    simp only [WeierstrassCurve.b₆]
    linarith
  have hB₈ : E.b₈ = (E.b₂ * E.b₆ - E.b₄ ^ 2) / 4 := by
    have h := E.b_relation
    linarith
  refine ⟨4 * (x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃), ?_⟩
  simp only [WeierstrassCurve.Δ, hB₈, hB₂, hB₄, hB₆]
  ring

/-- The complete geometric-to-Diophantine reduction: the exceptional
quartic leaf rules out full rational two-torsion together with a point of
order five. -/
theorem false_of_full_two_torsion_and_order_five
    (hquartic : NoExceptionalQuartic)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f)
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 5) :
    False := by
  obtain ⟨t, ht⟩ := exists_discriminant_square_of_full_two_torsion E f hf
  obtain ⟨c, u, hu, hc, hdisc⟩ :=
    exists_tateFive_discriminant_of_order_five E Q hQ
  apply no_rational_solution hquartic hc
  exact conductorTwenty_solution_of_discriminants hc hdisc ht

/-- Conditional only on the explicit quartic leaf, rational elliptic-curve
points forbid an embedding of `ZMod 2 × ZMod 10`. -/
theorem forbidsEmbedding_zmod_two_prod_ten_of_quartic
    (hquartic : NoExceptionalQuartic)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ForbidsEmbedding (ZMod 2 × ZMod 10) (E⁄ℚ).Point := by
  intro f hf
  let crt : ZMod 10 ≃+ ZMod 2 × ZMod 5 :=
    (ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 5)).toAddEquiv
  let g : ZMod 2 →+ ZMod 10 :=
    crt.symm.toAddMonoidHom.comp (AddMonoidHom.inl (ZMod 2) (ZMod 5))
  have hg : Function.Injective g :=
    crt.symm.injective.comp (fun _ _ h => congrArg Prod.fst h)
  let f₂ : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point :=
    f.comp ((AddMonoidHom.id (ZMod 2)).prodMap g)
  have hf₂ : Function.Injective f₂ := by
    apply hf.comp
    rw [AddMonoidHom.coe_prodMap]
    exact Function.Injective.prodMap (fun _ _ h => h) hg
  let Q : (E⁄ℚ).Point := f ((0 : ZMod 2), (2 : ZMod 10))
  have hQ : addOrderOf Q = 5 := by
    dsimp [Q]
    rw [addOrderOf_injective f hf]
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact addOrderOf_eq_prime (by decide) (by decide)
  exact false_of_full_two_torsion_and_order_five hquartic E f₂ hf₂ Q hQ

end ExceptionalTwoTen
end MazurTorsion

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

/-!
# Infinite descent for the exceptional two-by-ten quartic

This file proves that the primitive nonzero integral equation

`q² = x⁴ - 11x²y² - y⁴`

has no solutions.  Reduction modulo eight first makes `x` and `q` odd and makes `y`
divisible by four.  Writing `y = 2z`, two positive coprime factors have product
`125 z⁴`.  Their fourth-power decomposition produces a primitive Pythagorean triple.
The standard parametrization of that triple gives another solution whose
`Int.natAbs` of the second coordinate is strictly smaller.  A least-counterexample
argument completes the descent.
-/


private lemma quartic_mod_eight :
    ∀ x y q : ZMod 8,
      q ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 - y ^ 4 →
        (((ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) x ≠ 0) ∧
          ((ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)) y = 0) ∧
          ((ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) q ≠ 0)) ∨
        (((ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) x = 0) ∧
          ((ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) y = 0)) := by
  decide

private lemma two_nonsquare_mod_five :
    ∀ x z : ZMod 5, x ^ 2 = 2 * z ^ 2 → z = 0 := by
  decide

private lemma square_zero_mod_two :
    ∀ x : ZMod 2, x ^ 2 = 0 → x = 0 := by
  decide


namespace MazurTorsion.ExceptionalTwoTen

private lemma quartic_parity
    {X Y q : ℤ} (hcop : IsCoprime X Y)
    (h : q ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4) :
    (X : ZMod 2) ≠ 0 ∧ (Y : ZMod 4) = 0 ∧ (q : ZMod 2) ≠ 0 := by
  have h8 :
      (q : ZMod 8) ^ 2 =
        (X : ZMod 8) ^ 4 - 11 * (X : ZMod 8) ^ 2 * (Y : ZMod 8) ^ 2 -
          (Y : ZMod 8) ^ 4 := by
    simpa using congrArg (fun z : ℤ => (z : ZMod 8)) h
  rcases quartic_mod_eight (X : ZMod 8) (Y : ZMod 8) (q : ZMod 8) h8 with hgood | hbad
  · simpa [ZMod.castHom_apply] using hgood
  · exfalso
    have hX : (2 : ℤ) ∣ X := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd X 2).mp
      simpa [ZMod.castHom_apply] using hbad.1
    have hY : (2 : ℤ) ∣ Y := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd Y 2).mp
      simpa [ZMod.castHom_apply] using hbad.2
    have hu : IsUnit (2 : ℤ) := hcop.isRelPrime hX hY
    exact (Nat.prime_iff_prime_int.mp Nat.prime_two).not_unit hu

private lemma exceptional_factors_coprime
    {x z D₁ D₂ : ℤ} (hcop : IsCoprime x z)
    (hprod : D₁ * D₂ = 125 * z ^ 4)
    (hsum : D₁ + D₂ = x ^ 2 - 22 * z ^ 2) :
    IsCoprime D₁ D₂ := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpgZ : (p : ℤ) ∣ (Int.gcd D₁ D₂ : ℤ) := by
    exact_mod_cast hpg
  have hpD₁ : (p : ℤ) ∣ D₁ := hpgZ.trans (Int.gcd_dvd_left D₁ D₂)
  have hpD₂ : (p : ℤ) ∣ D₂ := hpgZ.trans (Int.gcd_dvd_right D₁ D₂)
  have hpSum : (p : ℤ) ∣ x ^ 2 - 22 * z ^ 2 := by
    rw [← hsum]
    exact dvd_add hpD₁ hpD₂
  have hpz_not : ¬(p : ℤ) ∣ z := by
    intro hpz
    have hpzSq : (p : ℤ) ∣ z ^ 2 := by
      simpa [pow_two] using dvd_mul_of_dvd_left hpz z
    have hpTerm : (p : ℤ) ∣ 22 * z ^ 2 :=
      dvd_mul_of_dvd_right hpzSq 22
    have hpxSq : (p : ℤ) ∣ x ^ 2 := by
      simpa only [sub_add_cancel] using dvd_add hpSum hpTerm
    have hpx : (p : ℤ) ∣ x := hpZ.dvd_of_dvd_pow hpxSq
    exact hpZ.not_unit (hcop.isRelPrime hpx hpz)
  have hpRight : (p : ℤ) ∣ 125 * z ^ 4 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpD₁ D₂
  have hp125 : (p : ℤ) ∣ 125 := by
    rcases hpZ.dvd_mul.mp hpRight with hp125 | hpz
    · exact hp125
    · exact (hpz_not (hpZ.dvd_of_dvd_pow hpz)).elim
  have hpFivePow : (p : ℤ) ∣ (5 : ℤ) ^ 3 := by
    norm_num at hp125 ⊢
    exact hp125
  have hpFive : (p : ℤ) ∣ 5 := hpZ.dvd_of_dvd_pow hpFivePow
  have hpFiveNat : p ∣ 5 := by
    exact_mod_cast hpFive
  have hp_eq_five : p = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hpFiveNat with hp1 | hp5
    · exact (hp.ne_one hp1).elim
    · exact hp5
  subst p
  have hD₁5 : (D₁ : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd D₁ 5).mpr hpD₁
  have hD₂5 : (D₂ : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd D₂ 5).mpr hpD₂
  have hsum5 := congrArg (fun t : ℤ => (t : ZMod 5)) hsum
  have hmod : (x : ZMod 5) ^ 2 = 2 * (z : ZMod 5) ^ 2 := by
    push_cast at hsum5
    rw [hD₁5, hD₂5] at hsum5
    have hz := hsum5.symm
    norm_num at hz
    exact sub_eq_zero.mp hz
  have hz5 : (z : ZMod 5) = 0 :=
    two_nonsquare_mod_five (x : ZMod 5) (z : ZMod 5) hmod
  apply hpz_not
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mp hz5

private lemma exceptional_factorization_of_five_dvd_left
    {D₁ D₂ z : ℤ} (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hz : 0 < z)
    (hcop : IsCoprime D₁ D₂) (hprod : D₁ * D₂ = 125 * z ^ 4)
    (hfive : (5 : ℤ) ∣ D₁) :
    ∃ a b : ℤ, IsCoprime a b ∧ a ≠ 0 ∧ b ≠ 0 ∧
      D₁ = 125 * a ^ 4 ∧ D₂ = b ^ 4 ∧ z ^ 2 = (a * b) ^ 2 := by
  have hpFive : Prime (5 : ℤ) :=
    Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 5)
  have hfive_not_D₂ : ¬(5 : ℤ) ∣ D₂ := by
    intro hfive₂
    exact hpFive.not_unit (hcop.isRelPrime hfive hfive₂)
  have hcopFive : IsCoprime (5 : ℤ) D₂ :=
    hpFive.coprime_iff_not_dvd.mpr hfive_not_D₂
  have hcopScaled : IsCoprime ((5 : ℤ) * D₁) D₂ :=
    IsCoprime.mul_left hcopFive hcop
  have hscaled : ((5 : ℤ) * D₁) * D₂ = (5 * z) ^ 4 := by
    rw [mul_assoc, hprod]
    ring
  have hgcdScaled : IsUnit (gcd ((5 : ℤ) * D₁) D₂) :=
    gcd_isUnit_iff_isRelPrime.mpr hcopScaled.isRelPrime
  obtain ⟨A, hAassoc⟩ :=
    exists_associated_pow_of_mul_eq_pow hgcdScaled hscaled
  have hscaled' : D₂ * ((5 : ℤ) * D₁) = (5 * z) ^ 4 := by
    simpa [mul_comm] using hscaled
  have hgcdScaled' : IsUnit (gcd D₂ ((5 : ℤ) * D₁)) :=
    gcd_isUnit_iff_isRelPrime.mpr hcopScaled.symm.isRelPrime
  obtain ⟨B, hBassoc⟩ :=
    exists_associated_pow_of_mul_eq_pow hgcdScaled' hscaled'
  have hA : A ^ 4 = 5 * D₁ := by
    rcases Int.associated_iff.mp hAassoc with hA | hA
    · exact hA
    · have hpow : 0 ≤ A ^ 4 := by positivity
      nlinarith
  have hB : B ^ 4 = D₂ := by
    rcases Int.associated_iff.mp hBassoc with hB | hB
    · exact hB
    · have hpow : 0 ≤ B ^ 4 := by positivity
      nlinarith
  have hfiveA4 : (5 : ℤ) ∣ A ^ 4 := by
    rw [hA]
    exact dvd_mul_right 5 D₁
  have hfiveA : (5 : ℤ) ∣ A := hpFive.dvd_of_dvd_pow hfiveA4
  obtain ⟨a, ha⟩ := hfiveA
  have hD₁eq : D₁ = 125 * a ^ 4 := by
    rw [ha] at hA
    nlinarith
  let b := B
  have hD₂eq : D₂ = b ^ 4 := hB.symm
  have habcop : IsCoprime a b := by
    have hpows : IsCoprime (a ^ 4) (b ^ 4) := by
      rw [hD₁eq, hD₂eq] at hcop
      exact hcop.of_mul_left_right
    exact (IsCoprime.pow_iff (by decide) (by decide)).mp hpows
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0] at hD₁eq
    norm_num at hD₁eq
    linarith
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0] at hD₂eq
    norm_num at hD₂eq
    linarith
  have hfour : (a * b) ^ 4 = z ^ 4 := by
    rw [hD₁eq, hD₂eq] at hprod
    nlinarith
  have hsquares : ((a * b) ^ 2) ^ 2 = (z ^ 2) ^ 2 := by
    calc
      ((a * b) ^ 2) ^ 2 = (a * b) ^ 4 := by ring
      _ = z ^ 4 := hfour
      _ = (z ^ 2) ^ 2 := by ring
  have habsq : (a * b) ^ 2 = z ^ 2 := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquares with hs | hs
    · exact hs
    · have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
      have habnonneg : 0 ≤ (a * b) ^ 2 := sq_nonneg _
      nlinarith
  exact ⟨a, b, habcop, ha0, hb0, hD₁eq, hD₂eq, habsq.symm⟩

private lemma exceptional_factorization
    {D₁ D₂ z : ℤ} (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hz : 0 < z)
    (hcop : IsCoprime D₁ D₂) (hprod : D₁ * D₂ = 125 * z ^ 4) :
    ∃ a b : ℤ, IsCoprime a b ∧ a ≠ 0 ∧ b ≠ 0 ∧
      D₁ + D₂ = a ^ 4 + 125 * b ^ 4 ∧ z ^ 2 = (a * b) ^ 2 := by
  have hpFive : Prime (5 : ℤ) :=
    Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 5)
  have hfiveProd : (5 : ℤ) ∣ D₁ * D₂ := by
    rw [hprod]
    exact dvd_mul_of_dvd_left (by norm_num : (5 : ℤ) ∣ 125) (z ^ 4)
  rcases hpFive.dvd_mul.mp hfiveProd with hfive₁ | hfive₂
  · obtain ⟨b, a, hba, hb0, ha0, hD₁eq, hD₂eq, hzsq⟩ :=
      exceptional_factorization_of_five_dvd_left hD₁ hD₂ hz hcop hprod hfive₁
    refine ⟨a, b, hba.symm, ha0, hb0, ?_, ?_⟩
    · rw [hD₁eq, hD₂eq]
      ring
    · simpa [mul_comm] using hzsq
  · have hprod' : D₂ * D₁ = 125 * z ^ 4 := by
      simpa [mul_comm] using hprod
    obtain ⟨b, a, hba, hb0, ha0, hD₂eq, hD₁eq, hzsq⟩ :=
      exceptional_factorization_of_five_dvd_left hD₂ hD₁ hz hcop.symm hprod' hfive₂
    refine ⟨a, b, hba.symm, ha0, hb0, ?_, ?_⟩
    · rw [hD₁eq, hD₂eq]
    · simpa [mul_comm] using hzsq

theorem exceptional_quartic_descent_step
    {x y q : ℤ} (hcop : IsCoprime x y) (hx : 0 < x) (hy : 0 < y) (hq : 0 ≤ q)
    (h : q ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 - y ^ 4) :
    ∃ x' y' q' : ℤ, IsCoprime x' y' ∧ x' ≠ 0 ∧ y' ≠ 0 ∧
      q' ^ 2 = x' ^ 4 - 11 * x' ^ 2 * y' ^ 2 - y' ^ 4 ∧
      y'.natAbs < y.natAbs := by
  have hpar := quartic_parity hcop h
  have hxNotEven : ¬Even x := by
    intro heven
    exact hpar.1 heven.intCast_zmod_two
  have hqNotEven : ¬Even q := by
    intro heven
    exact hpar.2.2 heven.intCast_zmod_two
  have hxOdd : Odd x := Int.not_even_iff_odd.mp hxNotEven
  have hqOdd : Odd q := Int.not_even_iff_odd.mp hqNotEven
  have hfourY : (4 : ℤ) ∣ y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd y 4).mp hpar.2.1
  obtain ⟨r, hr⟩ := hxOdd
  obtain ⟨s, hs⟩ := hqOdd
  obtain ⟨t, ht⟩ := hfourY
  let z : ℤ := 2 * t
  let D₁ : ℤ := 2 * r ^ 2 + 2 * r + 1 + s - 44 * t ^ 2
  let D₂ : ℤ := 2 * r ^ 2 + 2 * r - s - 44 * t ^ 2
  have hyz : y = 2 * z := by
    dsimp [z]
    rw [ht]
    ring
  have hscale₁ : 4 * D₁ = 2 * x ^ 2 - 11 * y ^ 2 + 2 * q := by
    dsimp [D₁]
    rw [hr, hs, ht]
    ring
  have hscale₂ : 4 * D₂ = 2 * x ^ 2 - 11 * y ^ 2 - 2 * q := by
    dsimp [D₂]
    rw [hr, hs, ht]
    ring
  have hxSq : 0 < x ^ 2 := sq_pos_of_pos hx
  have hyFourth : 0 < y ^ 4 := pow_pos hy 4
  have hcurveProduct :
      q ^ 2 + y ^ 4 = x ^ 2 * (x ^ 2 - 11 * y ^ 2) := by
    linear_combination h
  have hfactor : 0 < x ^ 2 - 11 * y ^ 2 := by
    by_contra hnonpos
    have hmul : x ^ 2 * (x ^ 2 - 11 * y ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (le_of_not_gt hnonpos)
    nlinarith [sq_nonneg q]
  have hcenter : 0 < 2 * x ^ 2 - 11 * y ^ 2 := by
    nlinarith
  have hcenterSq :
      (2 * x ^ 2 - 11 * y ^ 2) ^ 2 = (2 * q) ^ 2 + 125 * y ^ 4 := by
    linear_combination -4 * h
  have hcenter_gt : 2 * q < 2 * x ^ 2 - 11 * y ^ 2 := by
    nlinarith [sq_nonneg (2 * x ^ 2 - 11 * y ^ 2 - 2 * q)]
  have hD₁pos : 0 < D₁ := by
    nlinarith [hscale₁]
  have hD₂pos : 0 < D₂ := by
    nlinarith [hscale₂]
  have hzpos : 0 < z := by
    nlinarith [hy]
  have hprod : D₁ * D₂ = 125 * z ^ 4 := by
    have hscaled :
        16 * (D₁ * D₂) = 16 * (125 * z ^ 4) := by
      calc
        16 * (D₁ * D₂) = (4 * D₁) * (4 * D₂) := by ring
        _ = (2 * x ^ 2 - 11 * y ^ 2 + 2 * q) *
              (2 * x ^ 2 - 11 * y ^ 2 - 2 * q) := by rw [hscale₁, hscale₂]
        _ = (2 * x ^ 2 - 11 * y ^ 2) ^ 2 - (2 * q) ^ 2 := by ring
        _ = 125 * y ^ 4 := by nlinarith [hcenterSq]
        _ = 16 * (125 * z ^ 4) := by rw [hyz]; ring
    nlinarith
  have hsum : D₁ + D₂ = x ^ 2 - 22 * z ^ 2 := by
    have hscaled : 4 * (D₁ + D₂) = 4 * (x ^ 2 - 22 * z ^ 2) := by
      rw [mul_add, hscale₁, hscale₂, hyz]
      ring
    nlinarith
  have hcopxz : IsCoprime x z := by
    have hcop' : IsCoprime x (2 * z) := by
      simpa [hyz] using hcop
    exact hcop'.of_mul_right_right
  have hcopD : IsCoprime D₁ D₂ :=
    exceptional_factors_coprime hcopxz hprod hsum
  obtain ⟨a, b, hab, ha0, hb0, hfactorSum, hzsq⟩ :=
    exceptional_factorization hD₁pos hD₂pos hzpos hcopD hprod
  have hpyth :
      x ^ 2 = (a ^ 2 + 11 * b ^ 2) ^ 2 + (2 * b ^ 2) ^ 2 := by
    rw [hfactorSum] at hsum
    nlinarith [hzsq]
  let L : ℤ := a ^ 2 + 11 * b ^ 2
  let K : ℤ := 2 * b ^ 2
  have hLpos : 0 < L := by
    dsimp [L]
    nlinarith [sq_pos_of_ne_zero ha0, sq_nonneg b]
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (by norm_num) (sq_pos_of_ne_zero hb0)
  have htrip : PythagoreanTriple L K x := by
    delta PythagoreanTriple
    dsimp only [L, K]
    simpa only [pow_two] using hpyth.symm
  have hLoddCast : (L : ZMod 2) ≠ 0 := by
    intro hLzero
    have hKzero : (K : ZMod 2) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd K 2).2 ⟨b ^ 2, rfl⟩
    have hpythLK : x ^ 2 = L ^ 2 + K ^ 2 := by
      simpa [L, K] using hpyth
    have htrip2 := congrArg (fun w : ℤ => (w : ZMod 2)) hpythLK
    push_cast at htrip2
    rw [hLzero, hKzero] at htrip2
    norm_num at htrip2
    apply hpar.1
    exact square_zero_mod_two (x : ZMod 2) htrip2
  have hLNotEven : ¬Even L := by
    intro heven
    exact hLoddCast heven.intCast_zmod_two
  have hLmod : L % 2 = 1 := Int.not_even_iff.mp hLNotEven
  have hcopLb : IsCoprime L b := by
    have haSqCop : IsCoprime (a ^ 2) b := hab.pow_left
    dsimp [L]
    obtain ⟨c, d, hbez⟩ := haSqCop
    refine ⟨c, d - 11 * c * b, ?_⟩
    linear_combination hbez
  have hcopLtwo : IsCoprime L (2 : ℤ) := by
    have htwoNot : ¬(2 : ℤ) ∣ L := by
      intro htwo
      exact hLoddCast (even_iff_two_dvd.mpr htwo).intCast_zmod_two
    exact ((Nat.prime_iff_prime_int.mp Nat.prime_two).coprime_iff_not_dvd.mpr htwoNot).symm
  have hcopLK : IsCoprime L K := by
    dsimp [K]
    exact IsCoprime.mul_right hcopLtwo hcopLb.pow_right
  have hLKgcd : Int.gcd L K = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcopLK
  obtain ⟨m, n, hL, hK, hxmn, hmngcd, _hmnParity, hmnonneg⟩ :=
    htrip.coprime_classification' hLKgcd hLmod hx
  have hmn : b ^ 2 = m * n := by
    dsimp [K] at hK
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    simpa [mul_assoc] using hK
  have hbSqPos : 0 < b ^ 2 := sq_pos_of_ne_zero hb0
  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0] at hmn
    norm_num at hmn
    exact hb0 hmn
  have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hm0)
  have hmnpos : 0 < m * n := by
    rw [← hmn]
    exact hbSqPos
  have hnpos : 0 < n := pos_of_mul_pos_right hmnpos (le_of_lt hmpos)
  have hmnCop : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hmngcd
  obtain ⟨u, huSign⟩ := Int.sq_of_gcd_eq_one hmngcd hmn.symm
  have hnm : n * m = b ^ 2 := by
    simpa [mul_comm] using hmn.symm
  have hnmgcd : Int.gcd n m = 1 := by
    simpa [Int.gcd_comm] using hmngcd
  obtain ⟨v, hvSign⟩ := Int.sq_of_gcd_eq_one hnmgcd hnm
  have hu : m = u ^ 2 := by
    rcases huSign with hu | hu
    · exact hu
    · have hmle : m ≤ 0 := by
        rw [hu]
        exact neg_nonpos.mpr (sq_nonneg u)
      exact (not_lt_of_ge hmle hmpos).elim
  have hv : n = v ^ 2 := by
    rcases hvSign with hv | hv
    · exact hv
    · have hnle : n ≤ 0 := by
        rw [hv]
        exact neg_nonpos.mpr (sq_nonneg v)
      exact (not_lt_of_ge hnle hnpos).elim
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0] at hu
    norm_num at hu
    exact hm0 hu
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0] at hv
    norm_num at hv
    exact hn0 hv
  have huvCop : IsCoprime u v := by
    rw [hu, hv] at hmnCop
    exact (IsCoprime.pow_iff (by decide) (by decide)).mp hmnCop
  have hbuv : b ^ 2 = (u * v) ^ 2 := by
    rw [hmn, hu, hv]
    ring
  have hnew : a ^ 2 = u ^ 4 - 11 * u ^ 2 * v ^ 2 - v ^ 4 := by
    dsimp [L] at hL
    rw [hu, hv] at hL
    calc
      a ^ 2 = (u ^ 2) ^ 2 - (v ^ 2) ^ 2 - 11 * b ^ 2 := by
        linarith only [hL]
      _ = u ^ 4 - 11 * u ^ 2 * v ^ 2 - v ^ 4 := by
        rw [hbuv]
        ring
  have hzAbs : z.natAbs = (a * b).natAbs := by
    rcases eq_or_eq_neg_of_sq_eq_sq z (a * b) hzsq with hzab | hzab
    · rw [hzab]
    · rw [hzab, Int.natAbs_neg]
  have hbAbs : b.natAbs = (u * v).natAbs := by
    rcases eq_or_eq_neg_of_sq_eq_sq b (u * v) hbuv with hbuv' | hbuv'
    · rw [hbuv']
    · rw [hbuv', Int.natAbs_neg]
  have haAbsPos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
  have huAbsPos : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  have hzAbsEq : z.natAbs = a.natAbs * b.natAbs := by
    rw [hzAbs, Int.natAbs_mul]
  have hbAbsEq : b.natAbs = u.natAbs * v.natAbs := by
    rw [hbAbs, Int.natAbs_mul]
  have hv_le_b : v.natAbs ≤ b.natAbs := by
    rw [hbAbsEq]
    exact le_mul_of_one_le_left (Nat.zero_le _) huAbsPos
  have hb_le_z : b.natAbs ≤ z.natAbs := by
    rw [hzAbsEq]
    exact le_mul_of_one_le_left (Nat.zero_le _) haAbsPos
  have hyAbs : y.natAbs = 2 * z.natAbs := by
    rw [hyz, Int.natAbs_mul]
    norm_num
  have hzAbsPos : 0 < z.natAbs := Int.natAbs_pos.mpr (ne_of_gt hzpos)
  have hmeasure : v.natAbs < y.natAbs := by
    rw [hyAbs]
    omega
  exact ⟨u, v, a, huvCop, hu0, hv0, hnew, hmeasure⟩

private lemma normalize_exceptional_solution
    {X Y e : ℤ} (hcop : IsCoprime X Y) (hX : X ≠ 0) (hY : Y ≠ 0)
    (h : e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4) :
    ∃ x y q : ℤ, IsCoprime x y ∧ 0 < x ∧ 0 < y ∧ 0 ≤ q ∧
      q ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 - y ^ 4 ∧
      y.natAbs = Y.natAbs := by
  let x : ℤ := X.natAbs
  let y : ℤ := Y.natAbs
  let q : ℤ := e.natAbs
  have hxpos : 0 < x := by
    dsimp only [x]
    exact_mod_cast Int.natAbs_pos.mpr hX
  have hypos : 0 < y := by
    dsimp only [y]
    exact_mod_cast Int.natAbs_pos.mpr hY
  have hqnonneg : 0 ≤ q := by
    dsimp only [q]
    exact Int.natCast_nonneg _
  have hcop' : IsCoprime x y := by
    simpa only [x, y, Int.natCast_natAbs] using hcop.abs_abs
  have hcurve :
      q ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 - y ^ 4 := by
    have hpow4 (z : ℤ) : |z| ^ 4 = z ^ 4 :=
      (show Even 4 from by decide).pow_abs z
    simpa only [x, y, q, Int.natCast_natAbs, sq_abs, hpow4] using h
  have hyabs : y.natAbs = Y.natAbs := by
    dsimp only [y]
    rw [Int.natCast_natAbs]
    exact Int.natAbs_abs Y
  exact ⟨x, y, q, hcop', hxpos, hypos, hqnonneg, hcurve, hyabs⟩

/--
The exceptional quartic has no primitive nonzero integral solution.  The proof
uses infinite descent with the strict measure `Int.natAbs Y`.
-/
theorem noExceptionalQuartic : NoExceptionalQuartic := by
  classical
  intro X Y e hcop hX hY h
  let P : ℕ → Prop := fun n =>
    ∃ X Y e : ℤ, IsCoprime X Y ∧ X ≠ 0 ∧ Y ≠ 0 ∧
      e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4 ∧ Y.natAbs = n
  have hP : ∃ n : ℕ, P n :=
    ⟨Y.natAbs, X, Y, e, hcop, hX, hY, h, rfl⟩
  obtain ⟨X₀, Y₀, e₀, hcop₀, hX₀, hY₀, hcurve₀, hYmeasure⟩ :=
    Nat.find_spec hP
  obtain ⟨x, y, q, hcopxy, hx, hy, hq, hcurve, hynorm⟩ :=
    normalize_exceptional_solution hcop₀ hX₀ hY₀ hcurve₀
  obtain ⟨x', y', q', hcop', hx', hy', hcurve', hdesc⟩ :=
    exceptional_quartic_descent_step hcopxy hx hy hq hcurve
  have hP' : P y'.natAbs :=
    ⟨x', y', q', hcop', hx', hy', hcurve', rfl⟩
  have hminimal : Nat.find hP ≤ y'.natAbs :=
    Nat.find_min' hP hP'
  omega

end MazurTorsion.ExceptionalTwoTen
/- Platform rational-torsion adapter: Vasily Ilin, 2026. -/
open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 2 × ZMod 10) (MazurCampaign.RationalTorsion E) := by
  intro φ hφ
  exact MazurTorsion.ExceptionalTwoTen.forbidsEmbedding_zmod_two_prod_ten_of_quartic
    MazurTorsion.ExceptionalTwoTen.noExceptionalQuartic E
    ((AddCommGroup.torsion (E⁄ℚ).Point).subtype.comp φ)
    ((AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective.comp hφ)

#print axioms solution
