-- Prove2me | solution 1 for Groundwork.Sparsify.leaves_length_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:21:40.55921+00:00
-- url     : https://prove2.me/submissions/3b80c18b-51fd-46ce-9a59-e2a7441137b9

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
namespace Groundwork.Sparsify
theorem _root_.solution (k : ℕ) (s : σ) : 0 < (leaves step k s).length := by
  induction k generalizing s with
  | zero => simp [leaves]
  | succ k ih =>
    rw [leaves]
    split
    · simp
    · rename_i l h _
      have := ih l
      simp only [List.length_append]
      omega
end Groundwork.Sparsify
