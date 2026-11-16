-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaDeficitEnvelopeBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:32:54.981978+00:00
-- url     : https://prove2.me/submissions/abea7844-4fd0-4335-9af8-17f547f1a4a9

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Real
set_option autoImplicit false

/-- Pointwise dominating kernel for the stable Laplace-Gamma integration. -/
theorem solution
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u)
    (x : ℝ) (hx : 0 < x) :
    ‖(Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1)‖ ≤
      (if x ≤ 1 then u * x ^ (-alpha) else x ^ (-alpha - 1)) := by
  have hp : 0 ≤ x ^ (-alpha - 1) :=
    Real.rpow_nonneg hx.le _
  have hExpLe : Real.exp (-(u * x)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hux := mul_pos hu hx
    linarith
  have hAbs : |Real.exp (-(u * x)) - 1| =
      1 - Real.exp (-(u * x)) := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hnorm : ‖(Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1)‖ =
      (1 - Real.exp (-(u * x))) * x ^ (-alpha - 1) := by
    rw [Real.norm_eq_abs, abs_mul, hAbs, abs_of_nonneg hp]
  by_cases hcase : x ≤ 1
  · have hbound : 1 - Real.exp (-(u * x)) ≤ u * x := by
      have he := Real.add_one_le_exp (-(u * x))
      linarith
    have hpow : x * x ^ (-alpha - 1) = x ^ (-alpha) := by
      calc
        x * x ^ (-alpha - 1) =
          x ^ (1 : ℝ) * x ^ (-alpha - 1) := by rw [Real.rpow_one]
        _ = x ^ (1 + (-alpha - 1)) :=
          (Real.rpow_add hx 1 (-alpha - 1)).symm
        _ = x ^ (-alpha) := by congr 1; ring
    simp only [if_pos hcase]
    calc
      ‖(Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1)‖ =
        (1 - Real.exp (-(u * x))) * x ^ (-alpha - 1) := hnorm
      _ ≤ (u * x) * x ^ (-alpha - 1) :=
        mul_le_mul_of_nonneg_right hbound hp
      _ = u * x ^ (-alpha) := by rw [mul_assoc, hpow]
  · have hbound : 1 - Real.exp (-(u * x)) ≤ 1 := by
      have he := Real.exp_nonneg (-(u * x))
      linarith
    simp only [if_neg hcase]
    calc
      ‖(Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1)‖ =
        (1 - Real.exp (-(u * x))) * x ^ (-alpha - 1) := hnorm
      _ ≤ 1 * x ^ (-alpha - 1) :=
        mul_le_mul_of_nonneg_right hbound hp
      _ = x ^ (-alpha - 1) := one_mul _
