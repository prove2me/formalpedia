-- Prove2me | solution 1 for Groundwork.cut_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:38.578031+00:00
-- url     : https://prove2.me/submissions/5fcaab5d-f791-49af-9df0-b69ffd67418c

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
import Theorems.Thm_Groundwork_glue_congr
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words

set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace Groundwork
theorem _root_.solution (c : ι → ℕ) (d : List Bool) (e : List ι) (he : e.Nodup) (t : ι → List Bool)
    (h : ∀ i ∈ e, (t i).length = c i) (h' : ∀ i, i ∉ e → t i = d) : cut c d e (glue e t) = t := by
  induction e generalizing t with
  | nil => funext i; exact (h' i (by simp)).symm
  | cons j e ih =>
    rw [List.nodup_cons] at he
    have h2 : glue (j :: e) t = t j ++ glue e t := by simp [glue]
    have h3 : glue e t = glue e (Function.update t j d) :=
      glue_congr e fun i hi => by
        rw [Function.update_of_ne]
        rintro rfl; exact he.1 hi
    have hj := h j List.mem_cons_self
    have h4 := ih he.2 (Function.update t j d)
      (fun i hi => by
        rw [Function.update_of_ne (by rintro rfl; exact he.1 hi)]
        exact h i (List.mem_cons_of_mem _ hi))
      (fun i hi => by
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij]; exact h' i (by simp [hij, hi]))
    rw [cut, h2, ← hj, List.drop_left, List.take_left, h3, h4, Function.update_idem, Function.update_eq_self]
end Groundwork
