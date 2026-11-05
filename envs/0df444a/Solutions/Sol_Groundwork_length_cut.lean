-- Prove2me | solution 1 for Groundwork.length_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:44:51.580227+00:00
-- url     : https://prove2.me/submissions/9f758c52-7015-465d-8ab9-48f680eca507

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_StepMachines_Prog_Chunks
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words

set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace Groundwork
theorem _root_.solution (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) (hw : w.length = (e.map c).sum)
    {i : ι} (h : i ∈ e) : (cut c d e w i).length = c i := by
  induction e generalizing w with
  | nil => simp at h
  | cons j e ih =>
    simp only [List.map_cons, List.sum_cons] at hw
    by_cases hji : i = j
    · subst hji; simp only [cut, Function.update_self, List.length_take]; omega
    · rw [cut, Function.update_of_ne hji]
      exact ih _ (by rw [List.length_drop]; omega) ((List.mem_cons.1 h).resolve_left hji)
end Groundwork
