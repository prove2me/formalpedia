-- Prove2me | solution 1 for Groundwork.Stepped.filterMap_visits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:41:31.309582+00:00
-- url     : https://prove2.me/submissions/532179a6-e13a-4b03-835b-9a22f1babe64

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
variable (step : ν → Option (ν × ν))
namespace Groundwork.Stepped
theorem _root_.solution (k : ℕ) (s : ν) (r : List ν) (hk : ∀ x ∈ leaves step k s, step x = none) :
    (visits step k s r).filterMap (walkSel step) = leaves step k s := by
  induction k generalizing s r with
  | zero =>
    have h0 : step s = none := hk s (by simp [leaves])
    simp [visits, leaves, walkSel, h0]
  | succ k ih =>
    cases h0 : step s with
    | none => simp [visits, leaves, walkSel, h0]
    | some lh =>
      have el : leaves step (k + 1) s = leaves step k lh.1 ++ leaves step k lh.2 := by simp [leaves, h0]
      rw [el] at hk ⊢
      have h1 := ih lh.1 (lh.2 :: r) fun x hx => hk x (List.mem_append_left _ hx)
      have h2 := ih lh.2 r fun x hx => hk x (List.mem_append_right _ hx)
      simp [visits, walkSel, h0, h1, h2]
end Groundwork.Stepped
