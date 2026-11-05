-- Prove2me | solution 1 for Groundwork.exists_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:48:22.419737+00:00
-- url     : https://prove2.me/submissions/2ea02511-6936-4542-91d5-558f90b7c13f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_StepMachines_Prog_Decode
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_ToTuring_Machine_EndTM
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open Groundwork
open Sat3 Turing
open scoped NNReal
namespace Groundwork
theorem _root_.solution (k : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ C : ℕ, ∀ n : ℕ, ((n : ℝ) + 2) ^ k ≤ C * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ε * Real.log 2 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact mul_pos hε (Real.log_pos one_lt_two)
  refine ⟨⌈(k.factorial : ℝ) / a ^ k * Real.exp (a * 2)⌉₊, fun n => ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (a * ((n : ℝ) + 2)) (by positivity) k
  have h2 : (2 : ℝ) ^ (ε * n) = Real.exp (a * n) := by
    rw [Real.rpow_def_of_pos two_pos, ha]; congr 1; ring
  have h3 : Real.exp (a * ((n : ℝ) + 2)) = Real.exp (a * 2) * Real.exp (a * n) := by
    rw [← Real.exp_add]; congr 1; ring
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h4 : ((n : ℝ) + 2) ^ k ≤ (k.factorial : ℝ) / a ^ k * Real.exp (a * 2) * Real.exp (a * n) := by
    rw [mul_pow, div_le_iff₀ hk, h3] at h1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  rw [h2]
  exact h4.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Real.exp_pos _).le)
end Groundwork
