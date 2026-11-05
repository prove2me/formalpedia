-- Prove2me | solution 1 for Groundwork.Sparsify.one_le_sum_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:22:34.719329+00:00
-- url     : https://prove2.me/submissions/812c72d1-dace-45ca-a32f-0f78256e3505

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
theorem _root_.solution (d h : ℕ) : 1 ≤ ∑ j ∈ range (h + 1), d.choose j := by
  rw [sum_range_succ']
  simp
end Groundwork.Sparsify
