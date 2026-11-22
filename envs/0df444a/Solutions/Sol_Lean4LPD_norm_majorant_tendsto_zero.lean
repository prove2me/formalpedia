-- Prove2me | solution 1 for Lean4LPD.norm_majorant_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:33.849808+00:00
-- url     : https://prove2.me/submissions/2274b137-2108-4b92-8c05-73ffebae283c

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Threshold

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Filter
open scoped Topology
namespace Lean4LPD
theorem _root_.solution {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (c M : ℝ) :
    Tendsto (fun m : ℕ => q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
      atTop (𝓝 0) := by
  rcases hq0.eq_or_lt with hzero | hqpos
  · simp [hzero.symm]
  · have hlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hqpos hq1)
    have hn : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hreal := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero c (-Real.log q) hlog).comp hn
    have hscaled : Tendsto (fun m : ℕ =>
        ((m : ℝ) + 1) ^ c * Real.exp (Real.log q * ((m : ℝ) + 1)) * (Real.exp c * M))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_neg, zero_mul] using hreal.mul_const (Real.exp c * M)
    apply hscaled.congr'
    apply Filter.Eventually.of_forall
    intro m
    dsimp only
    have hp : q ^ (m + 1) = Real.exp (Real.log q * (((m + 1 : ℕ) : ℝ))) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log hqpos]
    rw [hp, Real.mul_rpow (by positivity) (by positivity), Real.exp_one_rpow]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
end Lean4LPD
