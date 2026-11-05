-- Prove2me | solution 1 for NamesInOrder.poly_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:39:16.501961+00:00
-- url     : https://prove2.me/submissions/b599ecf9-554a-4e29-a670-53e2dbb89338

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
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution (c a : ℕ) {N : ℕ} {X : ℝ} (hX : 1 ≤ X) (hN : (N : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) * X)) : ((c * N ^ c : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((c + a * c : ℕ) : ℝ) * X) := by
  calc ((c * N ^ c : ℕ) : ℝ) = (c : ℝ) * (N : ℝ) ^ c := by push_cast; ring
    _ ≤ (2 : ℝ) ^ ((c : ℝ) * X) * ((2 : ℝ) ^ ((a : ℝ) * X)) ^ c := mul_le_mul (natCast_le_two_rpow c hX) (pow_le_pow_left₀ (Nat.cast_nonneg N) hN c) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (((c + a * c : ℕ) : ℝ) * X) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring
end NamesInOrder
