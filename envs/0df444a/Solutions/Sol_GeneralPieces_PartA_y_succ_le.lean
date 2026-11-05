-- Prove2me | solution 1 for GeneralPieces.PartA.y_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:40.224349+00:00
-- url     : https://prove2.me/submissions/240c768f-5266-4ae5-a615-ae3a018ee044

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_e_ge_half_pow
import Theorems.Thm_ClauseBound_Gen_K_cast


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) :
    y ρ x₀ (l + 1) ≤ (1 + 1 / 2 ^ (l + 2)) * y ρ x₀ l + 6 * 2 ^ l / K x₀ l := by
  have hρ0 : 0 < ρ := by linarith
  have hr : 0 < ρ ^ l := by positivity
  have hK : (0 : ℝ) < K x₀ l := by rw [K_cast]; positivity
  have hy : 0 ≤ y ρ x₀ l := div_nonneg (le_trans (by positivity) (e_ge_half_pow ρ x₀ l hρ)) hr.le
  -- the two parts of e_{ℓ+1}, divided by ρ^{ℓ+1}
  have h0 : y ρ x₀ (l + 1) = (1 + 3 * zeta l / ρ) * y ρ x₀ l + 3 / K x₀ l / ρ ^ (l + 1) := by
    simp only [y, e, pow_succ]; field_simp
  -- 3ζ_ℓ/ρ ≤ 6ζ_ℓ ≤ 2^{−ℓ−2}
  have h1 : 3 * zeta l / ρ ≤ 1 / 2 ^ (l + 2) := by
    have hz : zeta l = 1 / 2 ^ (l + 2) / 8 := by rw [zeta, pow_add, pow_add]; field_simp; norm_num
    have hp : (0 : ℝ) < 1 / 2 ^ (l + 2) := by positivity
    rw [hz, div_le_iff₀ hρ0]
    nlinarith
  -- 1/ρ^{ℓ+1} ≤ 2^{ℓ+1}
  have h2 : 3 / (K x₀ l : ℝ) / ρ ^ (l + 1) ≤ 6 * 2 ^ l / K x₀ l := by
    have hp : (1 / 2 : ℝ) ^ (l + 1) ≤ ρ ^ (l + 1) := pow_le_pow_left₀ (by norm_num) hρ _
    have hq : (1 : ℝ) ≤ 2 ^ (l + 1) * ρ ^ (l + 1) := by
      have : (2 : ℝ) ^ (l + 1) * (1 / 2) ^ (l + 1) = 1 := by rw [← mul_pow]; norm_num
      calc (1 : ℝ) = 2 ^ (l + 1) * (1 / 2) ^ (l + 1) := this.symm
        _ ≤ 2 ^ (l + 1) * ρ ^ (l + 1) := mul_le_mul_of_nonneg_left hp (by positivity)
    rw [div_div, div_le_div_iff₀ (by positivity) hK]
    have : 3 * (K x₀ l : ℝ) * 1 ≤ 3 * (K x₀ l : ℝ) * (2 ^ (l + 1) * ρ ^ (l + 1)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    calc 3 * (K x₀ l : ℝ) = 3 * (K x₀ l : ℝ) * 1 := (mul_one _).symm
      _ ≤ 3 * (K x₀ l : ℝ) * (2 ^ (l + 1) * ρ ^ (l + 1)) := this
      _ = 6 * 2 ^ l * (K x₀ l * ρ ^ (l + 1)) := by rw [pow_succ (2 : ℝ) l]; ring
  rw [h0]
  have h3 : (1 + 3 * zeta l / ρ) * y ρ x₀ l ≤ (1 + 1 / 2 ^ (l + 2)) * y ρ x₀ l :=
    mul_le_mul_of_nonneg_right (by linarith) hy
  linarith
end GeneralPieces.PartA
