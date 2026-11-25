-- Prove2me | solution 1 for LieTrotter.norm_exp_mul_exp_sub_exp_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:51:01.411488+00:00
-- url     : https://prove2.me/submissions/d2eb17a2-dd23-49b3-b1b5-8132bc06ac38

module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NoncommRing
public import Definitions.Def_LieTrotter_Basic
public import Theorems.Thm_LieTrotter_norm_exp_le_exp_norm
public import Theorems.Thm_LieTrotter_norm_exp_sub_one_sub_le

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (X Y : 𝔸) :
    ‖exp X * exp Y - exp (X + Y)‖
      ≤ (‖X‖ + ‖Y‖) ^ 2 * (3 + (‖X‖ + ‖Y‖)) * Real.exp (‖X‖ + ‖Y‖) := by
  set a := ‖X‖ with ha
  set b := ‖Y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hdecomp : exp X * exp Y - exp (X + Y)
      = (exp X - 1 - X) * exp Y + (1 + X) * (exp Y - 1 - Y)
        + (X * Y - (exp (X + Y) - 1 - (X + Y))) := by
    noncomm_ring
  have h1 : ‖(exp X - 1 - X) * exp Y‖ ≤ a ^ 2 * Real.exp a * Real.exp b := by
    calc ‖(exp X - 1 - X) * exp Y‖
        ≤ ‖exp X - 1 - X‖ * ‖exp Y‖ := norm_mul_le _ _
      _ ≤ (a ^ 2 * Real.exp a) * Real.exp b := by
          refine mul_le_mul (norm_exp_sub_one_sub_le X)
            (norm_exp_le_exp_norm Y) (norm_nonneg _) (by positivity)
  have h2 : ‖(1 + X) * (exp Y - 1 - Y)‖ ≤ (1 + a) * (b ^ 2 * Real.exp b) := by
    calc ‖(1 + X) * (exp Y - 1 - Y)‖
        ≤ ‖(1 : 𝔸) + X‖ * ‖exp Y - 1 - Y‖ := norm_mul_le _ _
      _ ≤ (1 + a) * (b ^ 2 * Real.exp b) := by
          have hone : ‖(1 : 𝔸) + X‖ ≤ 1 + a := by
            calc ‖(1 : 𝔸) + X‖ ≤ ‖(1 : 𝔸)‖ + ‖X‖ := norm_add_le _ _
              _ = 1 + a := by rw [norm_one]
          exact mul_le_mul hone (norm_exp_sub_one_sub_le Y)
            (norm_nonneg _) (by positivity)
  have h3 : ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖
      ≤ a * b + (a + b) ^ 2 * Real.exp (a + b) := by
    calc ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖
        ≤ ‖X * Y‖ + ‖exp (X + Y) - 1 - (X + Y)‖ := norm_sub_le _ _
      _ ≤ a * b + (a + b) ^ 2 * Real.exp (a + b) := by
          refine add_le_add (norm_mul_le _ _) ?_
          calc ‖exp (X + Y) - 1 - (X + Y)‖
              ≤ ‖X + Y‖ ^ 2 * Real.exp ‖X + Y‖ := norm_exp_sub_one_sub_le _
            _ ≤ (a + b) ^ 2 * Real.exp (a + b) := by
                have hab : ‖X + Y‖ ≤ a + b := norm_add_le _ _
                gcongr
  have heab : Real.exp a * Real.exp b = Real.exp (a + b) :=
    (Real.exp_add a b).symm
  have heb : Real.exp b ≤ Real.exp (a + b) :=
    Real.exp_le_exp.mpr (by linarith)
  have he1 : (1 : ℝ) ≤ Real.exp (a + b) :=
    Real.one_le_exp (by linarith)
  have hepos : (0 : ℝ) < Real.exp (a + b) := Real.exp_pos _
  -- The difference is `a² + 3ab + b² + a³ + 3a²b + 2ab² + b³ ≥ 0`.
  have hpoly : a ^ 2 + (1 + a) * b ^ 2 + (a * b + (a + b) ^ 2)
      ≤ (a + b) ^ 2 * (3 + (a + b)) := by
    nlinarith [mul_nonneg ha0 hb0, mul_nonneg (mul_nonneg ha0 ha0) hb0,
      mul_nonneg (mul_nonneg ha0 hb0) hb0, sq_nonneg a, sq_nonneg b]
  calc ‖exp X * exp Y - exp (X + Y)‖
      ≤ ‖(exp X - 1 - X) * exp Y‖ + ‖(1 + X) * (exp Y - 1 - Y)‖
        + ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖ := by
        rw [hdecomp]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ a ^ 2 * Real.exp a * Real.exp b + (1 + a) * (b ^ 2 * Real.exp b)
        + (a * b + (a + b) ^ 2 * Real.exp (a + b)) :=
        add_le_add (add_le_add h1 h2) h3
    _ ≤ a ^ 2 * Real.exp (a + b) + (1 + a) * (b ^ 2 * Real.exp (a + b))
        + (a * b * Real.exp (a + b) + (a + b) ^ 2 * Real.exp (a + b)) := by
        refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ le_rfl)
        · rw [mul_assoc, heab]
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left heb (by positivity)) (by linarith)
        · calc a * b = a * b * 1 := by ring
            _ ≤ a * b * Real.exp (a + b) :=
              mul_le_mul_of_nonneg_left he1 (mul_nonneg ha0 hb0)
    _ = (a ^ 2 + (1 + a) * b ^ 2 + (a * b + (a + b) ^ 2))
        * Real.exp (a + b) := by ring
    _ ≤ (a + b) ^ 2 * (3 + (a + b)) * Real.exp (a + b) :=
        mul_le_mul_of_nonneg_right hpoly hepos.le
end LieTrotter
