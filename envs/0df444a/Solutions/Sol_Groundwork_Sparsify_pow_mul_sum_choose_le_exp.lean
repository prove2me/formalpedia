-- Prove2me | solution 1 for Groundwork.Sparsify.pow_mul_sum_choose_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:24:48.77894+00:00
-- url     : https://prove2.me/submissions/a2d189ce-ebf3-4cf7-b579-2b3ad50a7f1f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_StepMachines_Math_SparsifyCount

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
namespace Groundwork.Sparsify
theorem _root_.solution {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {r D : ℕ} (hr : r ≤ D) :
    x ^ r * ((∑ j ∈ Finset.range (r + 1), D.choose j : ℕ) : ℝ) ≤ Real.exp ((D : ℝ) * x) := by
  calc x ^ r * ((∑ j ∈ Finset.range (r + 1), D.choose j : ℕ) : ℝ)
      = ∑ j ∈ Finset.range (r + 1), x ^ r * (D.choose j : ℝ) := by
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (r + 1), x ^ j * 1 ^ (D - j) * (D.choose j : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [one_pow, mul_one]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx0.le hx1 hj') (Nat.cast_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (D + 1), x ^ j * 1 ^ (D - j) * (D.choose j : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (Nat.succ_le_succ hr)) fun j _ _ => ?_
        positivity
    _ = (x + 1) ^ D := (add_pow x 1 D).symm
    _ ≤ Real.exp x ^ D := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp x) D
    _ = Real.exp ((D : ℝ) * x) := (Real.exp_nat_mul x D).symm
end Groundwork.Sparsify
