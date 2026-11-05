-- Prove2me | solution 1 for Groundwork.DecodeK.length_enc_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:44.075057+00:00
-- url     : https://prove2.me/submissions/73b4671a-f8e3-468c-90c6-ef857471869c

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
import Theorems.Thm_Groundwork_DecodeK_length_enc_le
import Theorems.Thm_Groundwork_Decode_bitLen_le
import Theorems.Thm_Groundwork_Decode_length_enc_le


set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode
namespace Groundwork.DecodeK
theorem _root_.solution {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) :
    (enc k φ).length + 1 ≤ (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) := by
  have h1 := length_enc_le h
  have h2 : k * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ k ≤ k * (n + 2) * (2 * (n + 2)) ^ k :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ ((bitLen_le n).trans (by omega))) (Nat.pow_le_pow_left (by omega) k)
  have h3 : k * (n + 2) * (2 * (n + 2)) ^ k = k * 2 ^ k * (n + 2) ^ (k + 1) := by rw [mul_pow]; ring
  have h4 : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
  rw [Nat.add_mul, Nat.one_mul]
  omega
end Groundwork.DecodeK
