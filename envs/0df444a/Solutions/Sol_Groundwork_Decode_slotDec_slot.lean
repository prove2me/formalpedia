-- Prove2me | solution 1 for Groundwork.Decode.slotDec_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:08.656556+00:00
-- url     : https://prove2.me/submissions/c9e4a5d1-1826-4f77-bb5d-12af4eb1d917

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
theorem _root_.solution {n : ℕ} (o : Option (Lit n)) : slotDec (slot o) = o.map fun l => (l.1.val, l.2) := by
  rcases o with _ | ⟨i, b⟩
  · rfl
  · cases b
    · simp [slotDec, slot]
    · simp [slotDec, slot]
      omega
end Groundwork.Decode
