-- Prove2me | solution 1 for Groundwork.TM.code_mir
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:41:52.727023+00:00
-- url     : https://prove2.me/submissions/f08da6c7-59fc-4f05-b59e-d72c9cd7fa4a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_ToTuring_TM_Tree
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
namespace Groundwork.TM
theorem _root_.solution (x : V) : code x.mir = mirror (code x) := by
  induction x with
  | nil => rfl
  | bit b => rfl
  | cons x y ihx ihy => simp [V.mir, code, ihx, ihy, mirror, Sym.flip]
end Groundwork.TM
