-- Prove2me | solution 1 for LieTrotter.norm_exp_le_exp_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:36:56.244027+00:00
-- url     : https://prove2.me/submissions/4f7c7a64-0086-4e7d-aea3-b870fd1eb323

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
set_option maxHeartbeats 800000
namespace LieTrotter
theorem _root_.solution (X : 𝔸) : ‖exp X‖ ≤ Real.exp ‖X‖ := by
  have hsum : HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • X ^ n) (exp X) :=
    exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hnorm : Summable fun n : ℕ => ‖((n.factorial : ℝ))⁻¹ • X ^ n‖ :=
    norm_expSeries_summable_of_mem_ball' (𝕂 := ℝ) X
      ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
  have hterm : ∀ n : ℕ, ‖((n.factorial : ℝ))⁻¹ • X ^ n‖
      ≤ ((n.factorial : ℝ))⁻¹ * ‖X‖ ^ n := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · exact mul_le_mul_of_nonneg_left (norm_pow_le' X hpos) (by positivity)
  have hdom : Summable fun n : ℕ => ((n.factorial : ℝ))⁻¹ * ‖X‖ ^ n := by
    have := Real.summable_pow_div_factorial ‖X‖
    refine this.congr fun i => ?_
    rw [div_eq_mul_inv, mul_comm]
  calc ‖exp X‖ = ‖∑' n, ((n.factorial : ℝ))⁻¹ • X ^ n‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' n, ‖((n.factorial : ℝ))⁻¹ • X ^ n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, ((n.factorial : ℝ))⁻¹ * ‖X‖ ^ n :=
        hnorm.tsum_le_tsum hterm hdom
    _ = Real.exp ‖X‖ := by
        have hexp := (exp_series_hasSum_exp' (𝕂 := ℝ) (‖X‖ : ℝ)).tsum_eq
        rw [Real.exp_eq_exp_ℝ, ← hexp]
        exact tsum_congr fun i => by rw [smul_eq_mul]
end LieTrotter
