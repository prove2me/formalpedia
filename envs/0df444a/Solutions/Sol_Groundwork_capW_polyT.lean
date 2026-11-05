-- Prove2me | solution 1 for Groundwork.capW_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:02:26.737302+00:00
-- url     : https://prove2.me/submissions/46718325-d6f4-43b8-a16b-88c0e571acb0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_ToTuring_Poly_Digits
import Theorems.Thm_Groundwork_capW_unary
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open Groundwork
variable {α : Type} [Enc α]
namespace Groundwork
theorem _root_.solution {n c : α → ℕ} (hn : Unary n) (hc : PolyT c) (h : ∀ a, c a ≤ n a) :
    PolyT fun a => Prog.capW (n a) (c a) :=
  (capW_unary hn (hn.of_le hc h)).poly
end Groundwork
