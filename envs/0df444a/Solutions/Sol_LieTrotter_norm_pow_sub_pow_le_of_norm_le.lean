-- Prove2me | solution 1 for LieTrotter.norm_pow_sub_pow_le_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:46:22.035124+00:00
-- url     : https://prove2.me/submissions/a1d08505-4cb9-4aee-92fb-ac482eb7a8cc

module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NoncommRing
public import Definitions.Def_LieTrotter_Basic

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]
omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace LieTrotter
theorem _root_.solution {S T : 𝔸} {C : ℝ} (hC : 1 ≤ C)
    (hS : ‖S‖ ≤ C) (hT : ‖T‖ ≤ C) (n : ℕ) :
    ‖S ^ n - T ^ n‖ ≤ n * C ^ n * ‖S - T‖ := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  induction n with
  | zero => simp
  | succ n ih =>
    have hdecomp : S ^ (n + 1) - T ^ (n + 1)
        = (S ^ n - T ^ n) * S + T ^ n * (S - T) := by
      rw [pow_succ, pow_succ, sub_mul, mul_sub]
      abel
    have hTn : ‖T ^ n‖ ≤ C ^ n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp
      · exact le_trans (norm_pow_le' T hpos) (by gcongr)
    have h1 : ‖S ^ (n + 1) - T ^ (n + 1)‖
        ≤ ‖S ^ n - T ^ n‖ * ‖S‖ + ‖T ^ n‖ * ‖S - T‖ := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    have h2 : ‖S ^ n - T ^ n‖ * ‖S‖ ≤ (n * C ^ n * ‖S - T‖) * C :=
      mul_le_mul ih hS (norm_nonneg _) (by positivity)
    have h3 : ‖T ^ n‖ * ‖S - T‖ ≤ C ^ n * ‖S - T‖ :=
      mul_le_mul_of_nonneg_right hTn (norm_nonneg _)
    have hCn : C ^ n ≤ C ^ (n + 1) := by
      calc C ^ n = C ^ n * 1 := by ring
        _ ≤ C ^ n * C := by gcongr
        _ = C ^ (n + 1) := by ring
    calc ‖S ^ (n + 1) - T ^ (n + 1)‖
        ≤ (n * C ^ n * ‖S - T‖) * C + C ^ n * ‖S - T‖ := by
          refine le_trans h1 (add_le_add h2 h3)
      _ = n * (C ^ n * C) * ‖S - T‖ + C ^ n * ‖S - T‖ := by ring
      _ ≤ n * C ^ (n + 1) * ‖S - T‖ + C ^ (n + 1) * ‖S - T‖ := by
          rw [show C ^ n * C = C ^ (n + 1) from by ring]
          gcongr
      _ = ((n : ℝ) + 1) * C ^ (n + 1) * ‖S - T‖ := by ring
      _ = ((n + 1 : ℕ) : ℝ) * C ^ (n + 1) * ‖S - T‖ := by push_cast; ring
end LieTrotter
