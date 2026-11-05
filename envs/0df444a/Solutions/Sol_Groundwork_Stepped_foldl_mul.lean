-- Prove2me | solution 1 for Groundwork.Stepped.foldl_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:40.531269+00:00
-- url     : https://prove2.me/submissions/ce5ce092-7758-4998-9703-df4e22c90146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Definitions.Def_StepMachines_Prog_Range
import Theorems.Thm_Groundwork_Stepped_foldl_range_succ

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Finset
variable {α β γ : Type}
namespace Groundwork.Stepped
theorem _root_.solution (v : ℕ → ℤ) (k : ℕ) :
    (List.range k).foldl (fun c y => c * v y) 1 = ∏ y ∈ range k, v y := by
  induction k with
  | zero => rfl
  | succ k ih => rw [foldl_range_succ, ih, prod_range_succ]
end Groundwork.Stepped
