-- Prove2me | solution 1 for Groundwork.getD_chunks_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:39.810819+00:00
-- url     : https://prove2.me/submissions/9af2203f-1c63-4dac-a976-3b7fff5749ab

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
theorem _root_.solution (ℓ r j : ℕ) (w d : List Bool) (hj : j < r) :
    (chunks (List.replicate r ℓ) w).getD j d = block ℓ j w := by
  induction r generalizing j w with
  | zero => omega
  | succ r ih =>
    rw [List.replicate_succ, chunks]
    cases j with
    | zero => simp [block]
    | succ j =>
      rw [List.getD_cons_succ, ih j _ (by omega), block, block, List.drop_drop]
      congr 2; ring
end Groundwork
