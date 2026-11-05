-- Prove2me | solution 1 for Groundwork.SatNet.pow_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:41:16.453954+00:00
-- url     : https://prove2.me/submissions/c3d1c2c6-d30f-4a1e-9692-3f662f2d9c40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_StepMachines_Math_SatArith

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
namespace Groundwork.SatNet
theorem _root_.solution (A : ℕ) {c : ℝ} (hc : 0 < c) : ∃ C : ℕ, ∀ x : ℕ, (x : ℝ) ^ A ≤ C * (2 : ℝ) ^ (c * x) := by
  have hl : 0 < c * Real.log 2 := mul_pos hc (Real.log_pos one_lt_two)
  refine ⟨⌈(A.factorial : ℝ) / (c * Real.log 2) ^ A⌉₊, fun x => ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (c * Real.log 2 * x) (by positivity) A
  have h2 : (2 : ℝ) ^ (c * x) = Real.exp (c * Real.log 2 * x) := by
    rw [Real.rpow_def_of_pos two_pos]; congr 1; ring
  have hf : (0 : ℝ) < A.factorial := by exact_mod_cast A.factorial_pos
  have h3 : (x : ℝ) ^ A = (A.factorial / (c * Real.log 2) ^ A) * ((c * Real.log 2 * x) ^ A / A.factorial) := by
    rw [mul_pow (c * Real.log 2)]; field_simp
  rw [h2, h3]
  exact mul_le_mul (Nat.le_ceil _) h1 (by positivity) (by positivity)
end Groundwork.SatNet
