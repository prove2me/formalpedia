-- Prove2me | solution 1 for Groundwork.Code.card_filter_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:24.765472+00:00
-- url     : https://prove2.me/submissions/07474d47-b75b-4d7d-acdb-bcef9d1f67ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution (τ : List Bool) : #{j ∈ range τ.length | τ.getD j false = true} = τ.count true := by
  induction τ with
  | nil => simp
  | cons b τ ih =>
    rw [card_filter] at ih ⊢
    rw [List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.count_cons]
    cases b <;> simp
end Groundwork.Code
