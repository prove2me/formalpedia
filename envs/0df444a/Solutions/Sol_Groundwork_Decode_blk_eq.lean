-- Prove2me | solution 1 for Groundwork.Decode.blk_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:33.789227+00:00
-- url     : https://prove2.me/submissions/7aa816fb-69e1-465f-8b4a-04fe0c4674b7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_Decode_toWord_eq
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution (n : ℕ) (C : List (Lit n)) : blk n C =
    [toWord ((Nat.log2 (2 * n) + 1)) (slot C[0]?), toWord ((Nat.log2 (2 * n) + 1)) (slot C[1]?),
      toWord ((Nat.log2 (2 * n) + 1)) (slot C[2]?)].flatten := by
  simp [blk, toWord_eq, show List.range 3 = [0, 1, 2] from rfl]
end Groundwork.Decode
