-- Prove2me | solution 1 for NamesInOrder.pow_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:19:42.095712+00:00
-- url     : https://prove2.me/submissions/2622f49d-2286-409f-83ba-9ed8d286e54c

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
import Theorems.Thm_PairsToBound_mul_lg_le_expN
import Theorems.Thm_PairsToBound_natCast_pow_eq
import Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : ((k * (2 * n + 1) ^ (k + 3) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((9 : ℕ) : ℝ) * expN k n) := by
  have h1 := mul_lg_le_expN hk hn
  have hL : 1 ≤ lg n := one_le_lg (by omega)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    have := natCast_le_two_rpow k (le_refl (1 : ℝ))
    rwa [mul_one] at this
  have hnat : (2 * n + 1) ^ (k + 3) ≤ n ^ (8 * k) := by
    calc (2 * n + 1) ^ (k + 3) ≤ (n ^ 2) ^ (k + 3) := Nat.pow_le_pow_left (by nlinarith) _
      _ = n ^ (2 * (k + 3)) := by rw [← pow_mul]
      _ ≤ n ^ (8 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcast : (((2 * n + 1) ^ (k + 3) : ℕ) : ℝ) ≤ (n : ℝ) ^ (8 * k) := by exact_mod_cast hnat
  calc ((k * (2 * n + 1) ^ (k + 3) : ℕ) : ℝ) = (k : ℝ) * (((2 * n + 1) ^ (k + 3) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (2 : ℝ) ^ (k : ℝ) * (n : ℝ) ^ (8 * k) := mul_le_mul hk2 hcast (Nat.cast_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ ((k : ℝ) + ((8 * k : ℕ) : ℝ) * lg n) := by rw [natCast_pow_eq (by omega) (8 * k), ← Real.rpow_add two_pos]
    _ ≤ (2 : ℝ) ^ (((9 : ℕ) : ℝ) * expN k n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        push_cast
        nlinarith
end NamesInOrder
