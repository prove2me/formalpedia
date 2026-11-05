-- Prove2me | solution 1 for Groundwork.Sparsify.round_iterate_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:44.260627+00:00
-- url     : https://prove2.me/submissions/bccbf0b6-c171-4e0a-9e1b-844c9a720daa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree
import Theorems.Thm_Groundwork_Sparsify_round_nil_iterate
import Theorems.Thm_Groundwork_Sparsify_round_iterate

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
namespace Groundwork.Sparsify
theorem _root_.solution (k : ℕ) (s : σ) (hk : ∀ x ∈ leaves step k s, step x = none) (R : ℕ)
    (hR : 2 * (leaves step k s).length - 1 ≤ R) :
    (round step)^[R] ([s], []) = ([], (leaves step k s).reverse) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hR
  rw [Function.iterate_add_apply, round_iterate step k s hk, round_nil_iterate]
  simp
end Groundwork.Sparsify
