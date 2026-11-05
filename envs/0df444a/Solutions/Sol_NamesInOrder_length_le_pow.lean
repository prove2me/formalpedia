-- Prove2me | solution 1 for NamesInOrder.length_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:23.228549+00:00
-- url     : https://prove2.me/submissions/72332d42-c80b-4ddd-8f8e-27d88bc7ed55

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
import Theorems.Thm_NamesInOrder_log2_succ_le
import Theorems.Thm_ClauseBound_Alg_End_length_enc
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_clauseCount
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hn : 1 ≤ n) (hφ : SatK.IsKCNF k φ) : (SatM.enc k φ).length ≤ k * (2 * n + 1) ^ (k + 3) := by
  have hm := clauseCount k n φ hφ
  have hl := log2_succ_le (le_refl n) hn
  rw [ClauseBound.Alg.End.length_enc]
  generalize hy : 2 * n + 1 = y at *
  have hy3 : 3 ≤ y := by omega
  have h1 : φ.length * (k * (Nat.log2 (2 * n) + 1)) ≤ y ^ k * (k * y) := Nat.mul_le_mul hm (Nat.mul_le_mul_left k (by omega))
  have h2 : k + n + 2 ≤ k * y ^ 2 := by
    have : n + 3 ≤ y ^ 2 := by nlinarith
    nlinarith
  have h3 : y ^ 2 ≤ y ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : y ^ (k + 3) = y ^ (k + 1) * y ^ 2 := by rw [← pow_add]
  have h5 : y ^ k * (k * y) = k * y ^ (k + 1) := by rw [pow_succ]; ring
  have h6 : 9 ≤ y ^ 2 := by nlinarith
  have h7 : 0 < y ^ (k + 1) := by positivity
  rw [h4]
  calc k + n + 2 + φ.length * (k * (Nat.log2 (2 * n) + 1)) ≤ k * y ^ (k + 1) + k * y ^ (k + 1) := Nat.add_le_add (h2.trans (Nat.mul_le_mul_left k h3)) (h1.trans_eq h5)
    _ = k * (y ^ (k + 1) * 2) := by ring
    _ ≤ k * (y ^ (k + 1) * y ^ 2) := Nat.mul_le_mul_left k (Nat.mul_le_mul_left _ (by omega))
end NamesInOrder
