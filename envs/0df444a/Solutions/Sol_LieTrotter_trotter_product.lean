-- Prove2me | solution 1 for LieTrotter.trotter_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:06:33.731865+00:00
-- url     : https://prove2.me/submissions/3e67eafb-e270-4147-8c66-883d915ecd08

module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NoncommRing
public import Definitions.Def_LieTrotter_Basic
public import Theorems.Thm_LieTrotter_norm_trotter_sub_le

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n)
      Filter.atTop (nhds (exp (A + B))) := by
  set s := ‖A‖ + ‖B‖ with hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp (2 * s)))
      Filter.atTop (nhds 0) := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (s ^ 2 * (3 + s) * Real.exp (2 * s))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_trotter_sub_le A B n hn
end LieTrotter
