-- Prove2me | solution 1 for Groundwork.tri_zero_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:44:54.214254+00:00
-- url     : https://prove2.me/submissions/1a75b25c-5a9a-4d81-b658-0276595bff0b

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
namespace Groundwork
theorem _root_.solution (b : ℕ) : tri 0 (b + 1) = tri 0 b + b := by
  have : (b + 1) * (b + 1 - 1) = b * (b - 1) + 2 * b := by
    cases b with
    | zero => rfl
    | succ b => simp only [Nat.add_sub_cancel]; ring
  simp only [tri, this, add_zero]
  rw [Nat.add_mul_div_left _ _ (by omega)]
end Groundwork
