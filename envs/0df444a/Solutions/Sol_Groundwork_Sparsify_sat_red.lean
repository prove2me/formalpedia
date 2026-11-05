-- Prove2me | solution 1 for Groundwork.Sparsify.sat_red
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:25:18.087078+00:00
-- url     : https://prove2.me/submissions/7786abd7-8e37-4bcf-8255-7559822cb0bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Ring.Nat
import Definitions.Def_StepMachines_Math_Sparsify
import Theorems.Thm_Groundwork_Sparsify_red_subset
import Theorems.Thm_Groundwork_Sparsify_exists_red_subset

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
namespace Groundwork.Sparsify
theorem _root_.solution (v : α → Prop) (F : Finset (Finset α)) : Sat v (red F) ↔ Sat v F := by
  constructor
  · intro h C hC
    obtain ⟨D, hD, hDC⟩ := exists_red_subset hC
    obtain ⟨l, hl, hv⟩ := h D hD
    exact ⟨l, hDC hl, hv⟩
  · intro h C hC
    exact h C (red_subset F hC)
end Groundwork.Sparsify
