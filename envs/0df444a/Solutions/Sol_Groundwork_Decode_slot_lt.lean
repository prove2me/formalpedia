-- Prove2me | solution 1 for Groundwork.Decode.slot_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:04.278738+00:00
-- url     : https://prove2.me/submissions/829bca51-6cf3-4dcd-ac3d-119902c87d61

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
theorem _root_.solution {n : ℕ} (o : Option (Lit n)) : slot o < 2 ^ (Nat.log2 (2 * n) + 1) := by
  refine lt_of_le_of_lt ?_ Nat.lt_log2_self
  rcases o with _ | ⟨i, b⟩
  · exact Nat.zero_le _
  · have := i.2
    cases b <;> simp only [slot, Bool.toNat_false, Bool.toNat_true] <;> omega
end Groundwork.Decode
