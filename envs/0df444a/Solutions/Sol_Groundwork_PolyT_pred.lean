-- Prove2me | solution 1 for Groundwork.PolyT.pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:35:57.420895+00:00
-- url     : https://prove2.me/submissions/ef22aca7-7bc5-4e28-8683-e57540a81d5f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Nat1
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => f x - 1) := sub_aux hf (const 1)
end Groundwork.PolyT
