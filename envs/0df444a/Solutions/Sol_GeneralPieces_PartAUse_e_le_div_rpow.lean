-- Prove2me | solution 1 for GeneralPieces.PartAUse.e_le_div_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:52:20.104743+00:00
-- url     : https://prove2.me/submissions/7b056452-bdd9-4a8f-ad9e-46b98c7a1ccc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_GeneralPieces_PartAUse_e_le_of_log_le

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) {l d : ℕ} {y : ℝ} (hd : 1 ≤ d) (hy : 1 ≤ y)
    (h : y ≤ d * Real.logb 2 (K x₀ l)) : e ρ x₀ l ≤ ((d * (3 * x₀ + 6) : ℕ) : ℝ) / y ^ Real.logb 2 (1 / ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have ha1 : Real.logb 2 (1 / ρ) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hρ0]
    linarith
  have h3 := e_le_of_log_le hA hρ0 hρ1.le (by linarith) (Nat.cast_nonneg d) h
  generalize Real.logb 2 (1 / ρ) = α at *
  have hc : (1 : ℝ) ≤ ((d * (3 * x₀ + 6) : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd (by omega)
  have hcc : (d : ℝ) * (3 * x₀ + 6) = ((d * (3 * x₀ + 6) : ℕ) : ℝ) := by push_cast; ring
  rw [hcc] at h3
  generalize ((d * (3 * x₀ + 6) : ℕ) : ℝ) = a at *
  have h6 : (a / y) ^ α = a ^ α / y ^ α := Real.div_rpow (by linarith) (by linarith) α
  have h7 : a ^ α ≤ a := by
    calc a ^ α ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc ha1
      _ = a := Real.rpow_one _
  have hyα : 0 < y ^ α := Real.rpow_pos_of_pos (by linarith) _
  have h8 : a ^ α / y ^ α ≤ a / y ^ α := div_le_div_of_nonneg_right h7 hyα.le
  have h9 : 0 ≤ a ^ α / y ^ α := div_nonneg (Real.rpow_nonneg (by linarith) _) hyα.le
  rw [h6] at h3
  linarith
end GeneralPieces.PartAUse
