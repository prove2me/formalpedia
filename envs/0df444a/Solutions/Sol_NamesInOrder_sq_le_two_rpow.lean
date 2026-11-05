-- Prove2me | solution 1 for NamesInOrder.sq_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:28:04.631448+00:00
-- url     : https://prove2.me/submissions/05c4ad69-c825-47cb-be60-02b0092fa660

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
import Theorems.Thm_NamesInOrder_le_expM
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_PairsToBound_natCast_pow_eq
import Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow
import Theorems.Thm_VariableBound_Paper_two_le_expM


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : ((6 * (k * m) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((6 : ℕ) : ℝ) * expM k m) := by
  obtain ⟨h1, h2⟩ := le_expM hk hm
  have hX := two_le_expM hk hm
  have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    have := natCast_le_two_rpow k (le_refl (1 : ℝ))
    rwa [mul_one] at this
  have hm2 : (m : ℝ) ^ 2 = (2 : ℝ) ^ (((2 : ℕ) : ℝ) * lg m) := natCast_pow_eq (by omega) 2
  have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  calc ((6 * (k * m) ^ 2 : ℕ) : ℝ) = 6 * ((k : ℝ) ^ 2 * (m : ℝ) ^ 2) := by push_cast; ring
    _ ≤ 8 * (((2 : ℝ) ^ (k : ℝ)) ^ 2 * (m : ℝ) ^ 2) := by
        have a1 : (k : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (k : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk2 2
        have a2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
        have a3 : (0 : ℝ) ≤ (k : ℝ) ^ 2 * (m : ℝ) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right a1 a2]
    _ = (2 : ℝ) ^ ((3 : ℝ) + (k : ℝ) * 2 + ((2 : ℕ) : ℝ) * lg m) := by
        rw [hm2, h8, ← Real.rpow_natCast ((2 : ℝ) ^ (k : ℝ)) 2, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring
    _ ≤ (2 : ℝ) ^ (((6 : ℕ) : ℝ) * expM k m) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        push_cast
        linarith
end NamesInOrder
