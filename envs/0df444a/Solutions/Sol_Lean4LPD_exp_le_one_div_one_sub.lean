-- Prove2me | solution 1 for Lean4LPD.exp_le_one_div_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:37.065605+00:00
-- url     : https://prove2.me/submissions/9139ea5e-8312-4624-9ec8-5980b6ff3cff

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {y : ℝ} (hy : y < 1) : exp y ≤ 1 / (1 - y) := by
  have h1 : (0 : ℝ) < 1 - y := by linarith
  have h2 : 1 - y ≤ exp (-y) := by
    have := Real.add_one_le_exp (-y)
    linarith
  have h3 : (1 - y) * exp y ≤ exp (-y) * exp y := by
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt (exp_pos y))
  rw [← Real.exp_add] at h3
  simp only [neg_add_cancel, Real.exp_zero] at h3
  rw [le_div_iff₀ h1]
  linarith [h3]
end Lean4LPD
