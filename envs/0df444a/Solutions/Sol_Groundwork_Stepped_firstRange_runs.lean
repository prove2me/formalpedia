-- Prove2me | solution 1 for Groundwork.Stepped.firstRange_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:41.64675+00:00
-- url     : https://prove2.me/submissions/6beae30e-ef27-4bef-bee2-7d3d47e55427

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Definitions.Def_StepMachines_Prog_Range
import Theorems.Thm_Groundwork_Stepped_foldRange_runs
import Theorems.Thm_Groundwork_Stepped_foldl_first
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
open Finset
variable {α β γ : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) β} {p : β → Bool} {a : α}
    (t : ℕ → ℕ) (v : ℕ → β) (Sm : ℕ) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y)) :
    (firstRange N M p).Runs a (∑ y ∈ range (N a), (t y + 1))
      (size a + size (N a) + (size (N a) + 1 + Sm) + 1) ((List.range (N a)).find? fun y => p (v y)) := by
  rw [← foldl_first fun y => p (v y)]
  refine foldRange_runs t v _ Sm hM fun k hk => ?_
  rw [show List.foldl (fun c y => firstG p c y (v y)) (noneC a) (List.range k)
    = (List.range k).find? fun y => p (v y) from foldl_first (fun y => p (v y)) k]
  cases h : (List.range k).find? fun y => p (v y) with
  | none => simp only [size_none]; omega
  | some i =>
    have hi := List.mem_range.1 (List.mem_of_find?_eq_some h)
    have := Nat.size_le_size (hi.le.trans hk)
    simp only [size_some, size_nat]; omega
end Groundwork.Stepped
