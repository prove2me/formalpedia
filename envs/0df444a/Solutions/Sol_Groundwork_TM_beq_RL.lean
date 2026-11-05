-- Prove2me | solution 1 for Groundwork.TM.beq_RL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:22:31.612967+00:00
-- url     : https://prove2.me/submissions/a40c8e6c-2b96-45b2-bb32-7bd115e071a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_ToTuring_TM_Tree

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
namespace Groundwork.TM
theorem _root_.solution : (Sym.R == Sym.L) = false := by decide
end Groundwork.TM
