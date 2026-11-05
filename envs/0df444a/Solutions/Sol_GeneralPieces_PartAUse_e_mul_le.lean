-- Prove2me | solution 1 for GeneralPieces.PartAUse.e_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:39.678415+00:00
-- url     : https://prove2.me/submissions/523a69b5-dd25-487c-836f-6a091babfd79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_GeneralPieces_PartAUse_two_le_K
import Theorems.Thm_GeneralPieces_PartAUse_two_pow_le_logK
import Theorems.Thm_GeneralPieces_PartAUse_e_le_div_rpow
import Theorems.Thm_GeneralPieces_PartAUse_log_le_of_le_pow
import Theorems.Thm_GeneralPieces_PartAUse_add_four_le_pow
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution {l n : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (hle : K x₀ l ^ 17 ≤ n) (hlt : n < K x₀ (l + 1) ^ 17) :
    e ρ x₀ l * (((l + 1 : ℕ) : ℝ) + 1) ≤
      ((3 * (171 * (3 * x₀ + 6)) : ℕ) : ℝ) * (Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) / Real.logb 2 ((n : ℝ) + 4) ^ Real.logb 2 (1 / ρ)) := by
  have hA := thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy : (2 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 4) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_two]
    linarith
  have h1 : (n : ℝ) + 4 ≤ (K x₀ l : ℝ) ^ 171 := by exact_mod_cast add_four_le_pow hA hlt
  have hyx := log_le_of_le_pow (by positivity) h1
  have hK : (0 : ℝ) < K x₀ l := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_K hA l)
  have hxy : Real.logb 2 (K x₀ l) ≤ Real.logb 2 ((n : ℝ) + 4) := by
    have h2 : K x₀ l ≤ n + 4 := ((Nat.le_self_pow (by norm_num) _).trans hle).trans (Nat.le_add_right _ _)
    exact Real.logb_le_logb_of_le (by norm_num) hK (by exact_mod_cast h2)
  have he := e_le_div_rpow hA hρ hρ1 (by norm_num : 1 ≤ 171) (by linarith) hyx
  have h2l : (2 : ℝ) ^ l ≤ Real.logb 2 ((n : ℝ) + 4) := by
    have h3 : (2 : ℝ) ^ l ≤ 2 ^ (l + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ l)
    exact (h3.trans (two_pow_le_logK hA (by omega) l)).trans hxy
  generalize Real.logb 2 ((n : ℝ) + 4) = y at *
  have hlz : (l : ℝ) ≤ Real.logb 2 y := by
    rwa [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast]
  have hz : (1 : ℝ) ≤ Real.logb 2 y := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
    exact hy
  generalize Real.logb 2 y = z at *
  generalize Real.logb 2 (1 / ρ) = α at *
  have hyα : 0 < y ^ α := Real.rpow_pos_of_pos (by linarith) _
  have hl2 : ((l + 1 : ℕ) : ℝ) + 1 ≤ 3 * z := by push_cast; linarith
  calc e ρ x₀ l * (((l + 1 : ℕ) : ℝ) + 1) ≤ (((171 * (3 * x₀ + 6) : ℕ) : ℝ) / y ^ α) * (3 * z) :=
        mul_le_mul he hl2 (by positivity) (by positivity)
    _ = ((3 * (171 * (3 * x₀ + 6)) : ℕ) : ℝ) * (z / y ^ α) := by push_cast; ring
end GeneralPieces.PartAUse
