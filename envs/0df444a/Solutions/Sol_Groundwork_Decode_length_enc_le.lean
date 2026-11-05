-- Prove2me | solution 1 for Groundwork.Decode.length_enc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:02.770713+00:00
-- url     : https://prove2.me/submissions/f1dead24-340a-4762-bb18-247768a81c56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Sat3_Is3CNF_length_le


set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution {n : ℕ} {φ : CNF n} (h : Is3CNF φ) :
    (enc φ).length ≤ n + 1 + 3 * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ 3 := by
  rw [length_enc, Nat.mul_comm φ.length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h.length_le) _
end Groundwork.Decode
