-- Prove2me | solution 1 for Groundwork.DecodeK.length_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:31.72431+00:00
-- url     : https://prove2.me/submissions/2b48db03-6672-43ff-9e8c-d48c0d5bbe7c

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
import Theorems.Thm_Groundwork_DecodeK_length_blk
import Theorems.Thm_Groundwork_Decode_length_blk
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
    (φ.map (blk k n)).flatten.length = φ.length * (k * (Nat.log2 (2 * n) + 1)) := by
  induction φ with
  | nil => simp
  | cons C φ ih => simp only [List.map_cons, List.flatten_cons, List.length_append, ih, length_blk, List.length_cons]; ring
end Groundwork.DecodeK
