-- Prove2me | solution 1 for Groundwork.Decode.length_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:41:24.100014+00:00
-- url     : https://prove2.me/submissions/6011ef08-7b73-48ab-925a-444f0f1a9b11

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_Decode_length_blk
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution {n : ℕ} (φ : CNF n) : (φ.map (blk n)).flatten.length = φ.length * (3 * (Nat.log2 (2 * n) + 1)) := by
  induction φ with
  | nil => simp
  | cons C φ ih => simp only [List.map_cons, List.flatten_cons, List.length_append, ih, length_blk, List.length_cons]; ring
end Groundwork.Decode
