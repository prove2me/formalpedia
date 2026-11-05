-- Prove2me | solution 1 for Groundwork.Decode.width_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:20.063934+00:00
-- url     : https://prove2.me/submissions/7af7f1e3-ca39-42aa-b051-e55f149592a9

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
theorem _root_.solution (n : ℕ) : width n = (Nat.log2 (2 * n) + 1) := by
  unfold width
  split_ifs with h
  · subst h; simp
  · have h0 : 2 * n ≠ 0 := by omega
    apply le_antisymm
    · exact Nat.size_le.2 Nat.lt_log2_self
    · exact Nat.lt_size.2 (Nat.log2_self_le h0)
end Groundwork.Decode
