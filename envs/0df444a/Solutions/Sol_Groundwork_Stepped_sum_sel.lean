-- Prove2me | solution 1 for Groundwork.Stepped.sum_sel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:26.657325+00:00
-- url     : https://prove2.me/submissions/1dff3ec9-5f3d-4db3-8efb-2889549d0d68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
namespace Groundwork.Stepped
theorem _root_.solution (sel : τ → Option ν) (t : ℕ) (xs : List τ) :
    (xs.map fun x => ((sel x).map fun _ => t).getD 0 + 1).sum = xs.length + (xs.filterMap sel).length * t := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases h : sel x
    · simp only [List.filterMap_cons, h, Option.map_none, Option.getD_none, List.length_cons]; omega
    · simp only [List.filterMap_cons, h, Option.map_some, Option.getD_some, List.length_cons, Nat.succ_mul]; omega
end Groundwork.Stepped
