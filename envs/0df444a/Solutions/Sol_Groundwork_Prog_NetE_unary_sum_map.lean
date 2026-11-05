-- Prove2me | solution 1 for Groundwork.Prog.NetE.unary_sum_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:34:46.118936+00:00
-- url     : https://prove2.me/submissions/90f2da41-2ec5-4ad2-b427-34509460fb54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_ToTuring_Poly_NetFun
import Theorems.Thm_Groundwork_Prog_NetE_flatMap_replicate_unit
import Theorems.Thm_Groundwork_PolyT_congr
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
theorem _root_.solution {f : α → β → ℕ} {l : α → List β} (hf : Unary fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    Unary fun a => ((l a).map (f a)).sum := by
  unfold Unary at *
  have h : PolyT fun a => (l a).flatMap fun b => List.replicate (f a b) () := PolyT.flatMap hf hl
  exact h.congr fun a => flatMap_replicate_unit _ _
end Groundwork.Prog.NetE
