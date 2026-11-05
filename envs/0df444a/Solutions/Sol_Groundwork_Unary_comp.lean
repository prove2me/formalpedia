-- Prove2me | solution 1 for Groundwork.Unary.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:28:12.753733+00:00
-- url     : https://prove2.me/submissions/7ac7dbcb-0bb7-47ba-aad2-eece0554a910

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
attribute [local fun_prop] Groundwork.PolyT.comp



set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}
namespace Groundwork.Unary
theorem _root_.solution (hf : Unary f) {h : β → α} (hh : PolyT h) :
    Unary fun b => f (h b) :=
  PolyT.comp hf hh
end Groundwork.Unary
