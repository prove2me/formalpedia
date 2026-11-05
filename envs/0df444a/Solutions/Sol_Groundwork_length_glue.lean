-- Prove2me | solution 1 for Groundwork.length_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:11.614002+00:00
-- url     : https://prove2.me/submissions/1c0fbaa7-10a6-4b2c-b0c1-87782e0ee947

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
omit [DecidableEq ι]
namespace Groundwork
theorem _root_.solution (c : ι → ℕ) (e : List ι) (t : ι → List Bool) (h : ∀ i ∈ e, (t i).length = c i) :
    (glue e t).length = (e.map c).sum := by
  induction e with
  | nil => rfl
  | cons j e ih =>
    have h2 : glue (j :: e) t = t j ++ glue e t := by simp [glue]
    rw [h2, List.length_append, h j List.mem_cons_self, ih fun i hi => h i (List.mem_cons_of_mem _ hi)]
    simp
end Groundwork
