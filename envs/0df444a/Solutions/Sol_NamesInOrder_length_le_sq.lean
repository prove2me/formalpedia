-- Prove2me | solution 1 for NamesInOrder.length_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:19.868661+00:00
-- url     : https://prove2.me/submissions/b919bd3c-8654-4eec-9cf9-40275063037c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_NamesInOrder_Arith
import Theorems.Thm_NamesInOrder_variablesAreFew
import Theorems.Thm_NamesInOrder_log2_succ_le
import Theorems.Thm_ClauseBound_Alg_End_length_enc
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hm : 1 ≤ φ.length) (hφ : SatK.IsKCNF k φ) (ho : SatM.AllOccur φ) : (SatM.enc k φ).length ≤ 6 * (k * φ.length) ^ 2 := by
  have hn := variablesAreFew k n φ hφ ho
  have hx : 1 ≤ k * φ.length := Nat.mul_pos hk hm
  have hkx : k ≤ k * φ.length := Nat.le_mul_of_pos_right k hm
  have hl := log2_succ_le hn hx
  rw [ClauseBound.Alg.End.length_enc]
  have e : φ.length * (k * (Nat.log2 (2 * n) + 1)) = k * φ.length * (Nat.log2 (2 * n) + 1) := by ring
  rw [e]
  generalize k * φ.length = x at *
  have h2 : x * (Nat.log2 (2 * n) + 1) ≤ x * (2 * x) := Nat.mul_le_mul_left x hl
  nlinarith
end NamesInOrder
