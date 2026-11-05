-- Prove2me | solution 1 for Groundwork.Sparsify.sum_choose_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:22:24.300942+00:00
-- url     : https://prove2.me/submissions/f9cb381b-fdb0-452f-832b-43ea1bd3bc4c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
variable {step} {G : σ → ℕ → ℕ → Prop} {D T q : ℕ}
namespace Groundwork.Sparsify
theorem _root_.solution (d h : ℕ) :
    ∑ j ∈ range (h + 1 + 1), (d + 1).choose j =
      ∑ j ∈ range (h + 1 + 1), d.choose j + ∑ j ∈ range (h + 1), d.choose j := by
  rw [sum_range_succ' _ (h + 1), sum_range_succ' _ (h + 1)]
  simp only [Nat.choose_succ_succ, sum_add_distrib, Nat.choose_zero_right, Nat.succ_eq_add_one]
  omega
end Groundwork.Sparsify
