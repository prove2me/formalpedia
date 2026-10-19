-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.epsilon_exponent_weight_bound_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:03:25.775961+00:00
-- url     : https://prove2.me/submissions/72ebb084-288c-4687-97e3-05045b080fe1

import Mathlib
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators
theorem solution (b x : ℕ) (d : Fin (x - b + 1)) (w C ν ws : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws) (hw : ws ≤ w) : (((x - b - d.val : ℕ) : ℝ) * (C - ν * w)) ≤ -ν * (w * ((x : ℝ) - (b : ℝ))) + ν * (w * (d.val : ℝ)) + C * (w * (x : ℝ)) / ws := by
  have hd := d.isLt
  have hw0 : 0 < w := lt_of_lt_of_le hws hw
  have hratio : (x : ℝ) ≤ w * (x : ℝ) / ws := by
    rw [le_div_iff₀ hws]; nlinarith [(Nat.cast_nonneg x : (0:ℝ) ≤ x)]
  by_cases hbx : b ≤ x
  · have hn : ((x - b - d.val : ℕ) : ℝ) = (x : ℝ) - b - d.val := by
      have : d.val ≤ x - b := by omega
      push_cast [Nat.sub_sub, show b + d.val ≤ x by omega]
      ring
    rw [hn]
    have hle : (x : ℝ) - b - d.val ≤ x := by
      have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      have : (0 : ℝ) ≤ d.val := Nat.cast_nonneg _
      linarith
    have h1 : ((x : ℝ) - b - d.val) * C ≤ C * (w * (x : ℝ)) / ws := by
      rw [mul_div_assoc]
      nlinarith
    nlinarith
  · have hd0 : d.val = 0 := by omega
    have hn : x - b - d.val = 0 := by omega
    rw [hn, hd0]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    have hxb : (x : ℝ) - b ≤ 0 := by
      have : (x : ℝ) < b := by exact_mod_cast (not_le.mp hbx)
      linarith
    have h2 : 0 ≤ C * (w * (x : ℝ)) / ws := by positivity
    nlinarith [mul_nonneg hν (mul_nonneg hw0.le (show (0:ℝ) ≤ b - x by linarith))]
