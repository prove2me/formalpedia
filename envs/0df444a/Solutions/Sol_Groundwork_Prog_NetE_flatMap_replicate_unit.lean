-- Prove2me | solution 1 for Groundwork.Prog.NetE.flatMap_replicate_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:32:42.416174+00:00
-- url     : https://prove2.me/submissions/9075e6ae-b0c2-423d-b187-3bf2af25df81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_ToTuring_Poly_NetFun
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
variable {α β : Type} [Enc α] [Enc β]
namespace Groundwork.Prog.NetE
theorem _root_.solution {β : Type} (f : β → ℕ) (l : List β) :
    (l.flatMap fun b => List.replicate (f b) ()) = List.replicate (l.map f).sum () := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, ih, List.map_cons, List.sum_cons, List.replicate_add]
end Groundwork.Prog.NetE
