-- Prove2me | solution 1 for GraphProblems.ofWord_binary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:04:18.775997+00:00
-- url     : https://prove2.me/submissions/7156e7ee-bc46-4959-9abc-5e6b396448ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_WidthK_Top_Sat
import Mathlib.Tactic
import Definitions.Def_GraphProblems_Sized
import Theorems.Thm_Groundwork_Decode_toWord_eq
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_ofWord_toWord
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Finset
namespace GraphProblems
theorem _root_.solution {N v : ℕ} (h : v ≤ 2 ^ N) : ofWord (SatK.binary N v) = v := by
  have h2 : v < 2 ^ (N + 1) := lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [SatK.binary, ← Decode.toWord_eq, ofWord_toWord h2]
end GraphProblems
