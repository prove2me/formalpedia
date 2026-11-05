-- Prove2me | solution 1 for GeneralPieces.PartAUse.e_le_rPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:38.449204+00:00
-- url     : https://prove2.me/submissions/d7d756f3-ac79-4396-ab4c-002b1559b1b0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_GeneralPieces_PartAUse_e_le_div_rpow
import Theorems.Thm_GeneralPieces_PartAUse_log_le_of_le_pow
import Theorems.Thm_GeneralPieces_PartAUse_add_two_le_pow
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution {l m : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (h : (root9 m).length < K x₀ (l + 1)) :
    e ρ x₀ l ≤ ((91 * (3 * x₀ + 6) : ℕ) : ℝ) * SatM.rPow (Real.logb 2 (1 / ρ)) m := by
  have hA := thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hy : (1 : ℝ) ≤ Real.logb 2 ((m : ℝ) + 2) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    norm_num
  have h1 : (m : ℝ) + 2 ≤ (K x₀ l : ℝ) ^ 91 := by exact_mod_cast add_two_le_pow hA h
  have h2 := e_le_div_rpow hA hρ hρ1 (by norm_num : 1 ≤ 91) hy (log_le_of_le_pow (by positivity) h1)
  unfold SatM.rPow
  rwa [mul_one_div]
end GeneralPieces.PartAUse
