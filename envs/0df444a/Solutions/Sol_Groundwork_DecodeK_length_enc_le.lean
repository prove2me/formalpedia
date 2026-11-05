-- Prove2me | solution 1 for Groundwork.DecodeK.length_enc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:33:45.297318+00:00
-- url     : https://prove2.me/submissions/32431d76-04f3-4449-950d-2f4efe9a7e0b

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
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Sat3_Is3CNF_length_le


set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode
namespace Groundwork.DecodeK
theorem _root_.solution {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) :
    (enc k φ).length ≤ n + 1 + k * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ k := by
  rw [length_enc, Nat.mul_comm φ.length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (IsKCNF.length_le h)) _
end Groundwork.DecodeK
