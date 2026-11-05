-- Prove2me | solution 1 for Groundwork.DecodeK.eq_of_slots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:26:22.276245+00:00
-- url     : https://prove2.me/submissions/3d231a45-86a0-498e-90e1-e488a7e82427

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_WidthK_Decode

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode
namespace Groundwork.DecodeK
theorem _root_.solution {k n : ℕ} {C D : List (Lit n)} (hC : C.length ≤ k) (hD : D.length ≤ k)
    (h : ∀ j < k, C[j]? = D[j]?) : C = D :=
  List.ext_getElem? fun j => by
    by_cases hj : j < k
    · exact h j hj
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
end Groundwork.DecodeK
