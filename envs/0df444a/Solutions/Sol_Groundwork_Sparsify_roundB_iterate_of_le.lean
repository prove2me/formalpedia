-- Prove2me | solution 1 for Groundwork.Sparsify.roundB_iterate_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:25:01.551467+00:00
-- url     : https://prove2.me/submissions/2bf1d196-2f85-4bdd-82bf-caca89a878d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree
import Theorems.Thm_Groundwork_Sparsify_round_iterate_of_le
import Theorems.Thm_Groundwork_Sparsify_roundB_iterate

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
namespace Groundwork.Sparsify
theorem _root_.solution (test : σ → Bool) (k : ℕ) (s : σ)
    (hk : ∀ x ∈ leaves step k s, step x = none) (R : ℕ) (hR : 2 * (leaves step k s).length - 1 ≤ R) :
    (roundB step test)^[R] ([s], false) = ([], (leaves step k s).any test) := by
  have := roundB_iterate step test R [s] []
  rw [round_iterate_of_le step k s hk R hR] at this
  simpa using this
end Groundwork.Sparsify
