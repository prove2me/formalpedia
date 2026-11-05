-- Prove2me | solution 1 for Groundwork.TM.length_mirror
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:23:13.727117+00:00
-- url     : https://prove2.me/submissions/d0fe1c4d-ad85-449e-b66e-1afff8f3767f

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
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
namespace Groundwork.TM
theorem _root_.solution (w : List Sym) : (mirror w).length = w.length := by simp [mirror]
end Groundwork.TM
