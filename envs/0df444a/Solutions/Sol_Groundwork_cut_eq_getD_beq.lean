-- Prove2me | solution 1 for Groundwork.cut_eq_getD_beq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:22.789969+00:00
-- url     : https://prove2.me/submissions/eaa74235-4b96-4e6d-9816-d25ca24a6fa5

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
theorem _root_.solution [BEq ι] [LawfulBEq ι] (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool)
    (i : ι) : cut c d e w i = (chunks (e.map c) w).getD (e.idxOf i) d := by
  induction e generalizing w with
  | nil => rfl
  | cons j e ih =>
    by_cases h : j = i
    · subst h; simp [cut, chunks]
    · have h' : (j == i) = false := by simpa using h
      simp [cut, chunks, List.idxOf_cons, h', Function.update_of_ne (Ne.symm h), ih]
end Groundwork
