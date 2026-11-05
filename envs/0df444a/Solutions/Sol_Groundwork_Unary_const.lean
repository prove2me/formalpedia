-- Prove2me | solution 1 for Groundwork.Unary.const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:29:12.017041+00:00
-- url     : https://prove2.me/submissions/50a1b72e-08f9-428e-9b1d-a2a2f5a650e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}
namespace Groundwork.Unary
theorem _root_.solution (n : ℕ) :
    Unary fun _ : α => n :=
  PolyT.const _
end Groundwork.Unary
