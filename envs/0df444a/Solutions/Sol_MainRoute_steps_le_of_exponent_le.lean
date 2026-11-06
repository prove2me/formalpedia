-- Prove2me | solution 1 for MainRoute.steps_le_of_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:12:45.666707+00:00
-- url     : https://prove2.me/submissions/3a5489ff-84d1-4041-b009-58f8e09d14ae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_Defs
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_VariableBound_Paper_Rename_Time
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_MainRoute_EveryMachine
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_poly_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Arith_poly_le
import Theorems.Thm_VariableBound_Net_SizeP_one_le_two_pow
import Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow
import Theorems.Thm_VariableBound_Rename_poly_le
import Theorems.Thm_VariableBound_Rename_poly_mono
import Theorems.Thm_VariableBound_Rename_steps_split


set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
namespace MainRoute
theorem _root_.solution (q G : ℕ) {E L : ℕ} {X : ℝ} (hX : 1 ≤ X) (hE : (E : ℝ) ≤ G * X) (hL : 1 ≤ L) :
    q * (L + 2 ^ E + 1) ^ q ≤ ⌊(2 : ℝ) ^ (((2 * q + 2 * q * (G + 1) + q * 4 ^ q : ℕ) : ℝ) * X)⌋₊ + (2 * q + 2 * q * (G + 1) + q * 4 ^ q) * L ^ (2 * q + 2 * q * (G + 1) + q * 4 ^ q) := by
  have h0 := VariableBound.Rename.steps_split q L 0 E
  have h1 : q * 2 ^ q * (L + 1) ^ q ≤ (2 * q + 2 * q * (G + 1) + q * 4 ^ q) * L ^ (2 * q + 2 * q * (G + 1) + q * 4 ^ q) :=
    (VariableBound.Rename.poly_le q hL).trans (VariableBound.Rename.poly_mono (by omega) hL)
  have h2 : 2 * q * (0 + 2 ^ E + 1) ^ (2 * q) ≤ ⌊(2 : ℝ) ^ (((2 * q + 2 * q * (G + 1) + q * 4 ^ q : ℕ) : ℝ) * X)⌋₊ := by
    refine Nat.le_floor ?_
    have a1 : 0 + 2 ^ E + 1 ≤ 2 ^ (E + 1) := by
      have : 1 ≤ 2 ^ E := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    have a2 : 2 * q * (0 + 2 ^ E + 1) ^ (2 * q) ≤ 2 * q * 2 ^ ((E + 1) * (2 * q)) := by
      rw [pow_mul 2 (E + 1) (2 * q)]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left a1 _)
    have a3 : ((2 * q * (0 + 2 ^ E + 1) ^ (2 * q) : ℕ) : ℝ) ≤ ((2 * q : ℕ) : ℝ) * (2 : ℝ) ^ (((E + 1) * (2 * q) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast a2
    have a4 : ((2 * q : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * q : ℕ) : ℝ) * X) := VariableBound.Paper.natCast_le_two_rpow (2 * q) hX
    have a5 : (((E + 1) * (2 * q) : ℕ) : ℝ) ≤ ((2 * q * (G + 1) : ℕ) : ℝ) * X := by
      push_cast
      have : (E : ℝ) + 1 ≤ (G + 1) * X := by nlinarith
      have hq : (0 : ℝ) ≤ 2 * q := by positivity
      nlinarith
    have a6 : (2 : ℝ) ^ (((E + 1) * (2 * q) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * q * (G + 1) : ℕ) : ℝ) * X) := Real.rpow_le_rpow_of_exponent_le one_le_two a5
    have a7 : (2 : ℝ) ^ (((2 * q : ℕ) : ℝ) * X) * (2 : ℝ) ^ (((2 * q * (G + 1) : ℕ) : ℝ) * X) ≤ (2 : ℝ) ^ (((2 * q + 2 * q * (G + 1) + q * 4 ^ q : ℕ) : ℝ) * X) := by
      rw [← Real.rpow_add two_pos]
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      push_cast
      have : (0 : ℝ) ≤ (q : ℝ) * 4 ^ q * X := by positivity
      nlinarith
    exact a3.trans ((mul_le_mul a4 a6 (by positivity) (by positivity)).trans a7)
  omega
end MainRoute
