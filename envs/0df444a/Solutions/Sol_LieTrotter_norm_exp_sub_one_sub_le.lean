-- Prove2me | solution 1 for LieTrotter.norm_exp_sub_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:37:15.406371+00:00
-- url     : https://prove2.me/submissions/c45a3932-2e28-407f-90d1-d0b78dfee204

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
omit [NormOneClass 𝔸]
set_option maxHeartbeats 800000
namespace LieTrotter
theorem _root_.solution (X : 𝔸) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  set f : ℕ → 𝔸 := fun n => ((n.factorial : ℝ))⁻¹ • X ^ n with hf
  have hsum : HasSum f (exp X) := exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hsplit : (∑ i ∈ Finset.range 2, f i) + ∑' i, f (i + 2) = ∑' i, f i :=
    hsum.summable.sum_add_tsum_nat_add 2
  have hf01 : (∑ i ∈ Finset.range 2, f i) = 1 + X := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [hf]
  have htail : exp X - 1 - X = ∑' i, f (i + 2) := by
    rw [← hsum.tsum_eq, ← hsplit, hf01]
    abel
  have hterm : ∀ i : ℕ, ‖f (i + 2)‖
      ≤ ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) := by
    intro i
    rw [hf]
    have hfe : (((i + 2).factorial : ℝ))⁻¹ ≤ ((i.factorial : ℝ))⁻¹ := by
      gcongr
      omega
    calc ‖(((i + 2).factorial : ℝ))⁻¹ • X ^ (i + 2)‖
        = (((i + 2).factorial : ℝ))⁻¹ * ‖X ^ (i + 2)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (((i + 2).factorial : ℝ))⁻¹ * ‖X‖ ^ (i + 2) :=
          mul_le_mul_of_nonneg_left (norm_pow_le' X (Nat.succ_pos _))
            (by positivity)
      _ ≤ ((i.factorial : ℝ))⁻¹ * ‖X‖ ^ (i + 2) :=
          mul_le_mul_of_nonneg_right hfe (by positivity)
      _ = ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) := by ring
  have hsummable_norm : Summable fun i : ℕ => ‖f (i + 2)‖ := by
    have h0 : Summable fun n : ℕ => ‖f n‖ :=
      norm_expSeries_summable_of_mem_ball' (𝕂 := ℝ) X
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    exact h0.comp_injective fun a b hab => by omega
  have hsummable_dom : Summable fun i : ℕ =>
      ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) := by
    refine Summable.mul_left _ ?_
    have := Real.summable_pow_div_factorial ‖X‖
    refine this.congr fun i => ?_
    rw [div_eq_mul_inv, mul_comm]
  calc ‖exp X - 1 - X‖
      = ‖∑' i, f (i + 2)‖ := by rw [htail]
    _ ≤ ∑' i, ‖f (i + 2)‖ := norm_tsum_le_tsum_norm hsummable_norm
    _ ≤ ∑' i, ‖X‖ ^ 2 * (((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i) :=
        hsummable_norm.tsum_le_tsum hterm hsummable_dom
    _ = ‖X‖ ^ 2 * ∑' i, ((i.factorial : ℝ))⁻¹ * ‖X‖ ^ i := tsum_mul_left
    _ = ‖X‖ ^ 2 * Real.exp ‖X‖ := by
        congr 1
        have hexp := (exp_series_hasSum_exp' (𝕂 := ℝ) (‖X‖ : ℝ)).tsum_eq
        rw [Real.exp_eq_exp_ℝ, ← hexp]
        exact tsum_congr fun i => by rw [smul_eq_mul]
end LieTrotter
