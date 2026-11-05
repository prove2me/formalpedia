-- Prove2me | solution 1 for Groundwork.Decode.length_enc_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:51.877489+00:00
-- url     : https://prove2.me/submissions/aa7993cc-5044-4cdd-a80d-d2980589223c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_Decode_length_enc_le
import Theorems.Thm_Groundwork_Decode_bitLen_le

set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : (enc φ).length + 1 ≤ 25 * (n + 2) ^ 4 := by
  have h1 := length_enc_le h
  have h2 : 3 * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ 3 ≤ 3 * (n + 2) * (2 * (n + 2)) ^ 3 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ ((bitLen_le n).trans (by omega))) (Nat.pow_le_pow_left (by omega) 3)
  have h3 : 3 * (n + 2) * (2 * (n + 2)) ^ 3 = 24 * (n + 2) ^ 4 := by ring
  have h4 : n + 2 ≤ (n + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  omega
end Groundwork.Decode
