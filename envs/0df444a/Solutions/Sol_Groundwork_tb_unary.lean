-- Prove2me | solution 1 for Groundwork.tb_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:56:25.828386+00:00
-- url     : https://prove2.me/submissions/e6a384ac-5eb1-4424-8367-be361f640c90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_ToTuring_Poly_Digits
import Theorems.Thm_Groundwork_tb_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Prog_tb_le
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_le
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open Groundwork
variable {α : Type} [Enc α]
namespace Groundwork
theorem _root_.solution {f : α → ℕ} (hf : Unary f) : Unary fun a => Prog.tb (f a) :=
  (((Unary.const 2).mul hf).add (Unary.const 1)).of_le (tb_polyT hf) fun _ => Prog.tb_le _
end Groundwork
