-- Prove2me | solution 1 for Groundwork.DecodeK.length_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:14:29.65075+00:00
-- url     : https://prove2.me/submissions/0c691017-171b-4d84-bb9c-06252eacfd06

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
import Theorems.Thm_Groundwork_DecodeK_enc_eq
import Theorems.Thm_Groundwork_DecodeK_length_body
import Theorems.Thm_Groundwork_Decode_enc_eq
import Theorems.Thm_Groundwork_Decode_length_body
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode
namespace Groundwork.DecodeK
theorem _root_.solution (k : ℕ) {n : ℕ} (φ : CNF n) :
    (enc k φ).length = n + 1 + φ.length * (k * (Nat.log2 (2 * n) + 1)) := by
  simp only [enc_eq, List.length_append, List.length_replicate, List.length_cons, length_body]; omega
end Groundwork.DecodeK
