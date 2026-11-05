-- Prove2me | solution 1 for Groundwork.Decode.dropWhile_header
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:35.050595+00:00
-- url     : https://prove2.me/submissions/f3b6e993-93b8-4402-bec8-e36d0a232d31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution (n : ℕ) (l : List Bool) :
    (List.replicate n true ++ false :: l).dropWhile id = false :: l := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]
end Groundwork.Decode
