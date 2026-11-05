-- Prove2me | solution 1 for Groundwork.glue_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:10.342835+00:00
-- url     : https://prove2.me/submissions/e46354aa-3497-4eb0-92be-401650e900f4

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
theorem _root_.solution (c : ι → ℕ) (d : List Bool) (e : List ι) (he : e.Nodup) (w : List Bool)
    (hw : w.length = (e.map c).sum) : glue e (cut c d e w) = w := by
  induction e generalizing w with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_eq_zero_iff] at hw; simp [glue, hw]
  | cons j e ih =>
    simp only [List.map_cons, List.sum_cons] at hw
    rw [List.nodup_cons] at he
    have h1 : glue e (cut c d (j :: e) w) = glue e (cut c d e (w.drop (c j))) :=
      glue_congr e fun i hi => by
        rw [cut, Function.update_of_ne]
        rintro rfl; exact he.1 hi
    have h2 : glue (j :: e) (cut c d (j :: e) w) = cut c d (j :: e) w j ++ glue e (cut c d (j :: e) w) := by
      simp [glue]
    rw [h2, h1, ih he.2 _ (by rw [List.length_drop]; omega), cut, Function.update_self, List.take_append_drop]
end Groundwork
