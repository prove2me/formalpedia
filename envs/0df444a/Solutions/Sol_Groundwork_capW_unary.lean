-- Prove2me | solution 1 for Groundwork.capW_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:59:28.924205+00:00
-- url     : https://prove2.me/submissions/a585b28a-ab40-4a5a-b7fa-3b7b470a606b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_ToTuring_Poly_Digits
import Theorems.Thm_Groundwork_tb_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_Unary_add


set_option autoImplicit false
section
section
open Groundwork
variable {α : Type} [Enc α]
namespace Groundwork
theorem _root_.solution {n c : α → ℕ} (hn : Unary n) (hc : Unary c) : Unary fun a => Prog.capW (n a) (c a) :=
  hn.add (tb_unary hc)
end Groundwork
