-- Prove2me | solution 1 for NamesInOrder.timeM_add_timeM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:08.416474+00:00
-- url     : https://prove2.me/submissions/0a3bea02-efc2-4fb3-ab5f-ff81d2031548

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
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PairsToBound_two_rpow_mono
import Theorems.Thm_VariableBound_Paper_two_le_expM


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution (a b : ℕ) {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : timeM a k m + timeM b k m ≤ timeM (max a b + 1) k m := by
  have hX := two_le_expM hk hm
  have hX0 : 0 ≤ expM k m := by linarith
  have h1 : ((timeM a k m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max a b : ℕ) : ℝ) * expM k m) := (Nat.floor_le (by positivity)).trans (two_rpow_mono (le_max_left a b) hX0)
  have h2 : ((timeM b k m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max a b : ℕ) : ℝ) * expM k m) := (Nat.floor_le (by positivity)).trans (two_rpow_mono (le_max_right a b) hX0)
  have e : (2 : ℝ) ^ (((max a b + 1 : ℕ) : ℝ) * expM k m) = (2 : ℝ) ^ (((max a b : ℕ) : ℝ) * expM k m) * (2 : ℝ) ^ expM k m := by
    rw [← Real.rpow_add two_pos]
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ expM k m := by
    have := Real.rpow_le_rpow_of_exponent_le one_le_two (show (1 : ℝ) ≤ expM k m by linarith)
    rwa [Real.rpow_one] at this
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (((max a b : ℕ) : ℝ) * expM k m) := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 hp
  refine Nat.le_floor ?_
  rw [e, Nat.cast_add]
  linarith
end NamesInOrder
