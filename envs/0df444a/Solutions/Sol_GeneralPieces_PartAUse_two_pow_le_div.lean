-- Prove2me | solution 1 for GeneralPieces.PartAUse.two_pow_le_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:47:09.392416+00:00
-- url     : https://prove2.me/submissions/deb28441-96c0-44f3-9d1e-2d89cc1150e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_Groundwork_PolyT_div_pow
attribute [local fun_prop] Groundwork.PolyT.div_pow



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) {C : ℕ} (hC : ρ ^ C ≤ 1 / 2) (l : ℕ) :
    (2 : ℝ) ^ (l + 1) ≤ (2 / e ρ x₀ l) ^ (C + 1) := by
  have hρ0 : 0 < ρ := by linarith
  have hpl : 0 < ρ ^ l := by positivity
  have he0 : 0 < e ρ x₀ l := lt_of_lt_of_le (by positivity) (hA.e_bounds l).1
  have he1 : e ρ x₀ l ≤ ρ ^ l := by linarith [(hA.e_bounds l).2]
  have h2 : 2 / ρ ^ l ≤ 2 / e ρ x₀ l := div_le_div_of_nonneg_left (by norm_num) he0 he1
  have hC1 : ρ ^ (C + 1) ≤ 1 / 2 := by
    calc ρ ^ (C + 1) = ρ ^ C * ρ := pow_succ _ _
      _ ≤ ρ ^ C * 1 := mul_le_mul_of_nonneg_left hρ1.le (by positivity)
      _ ≤ 1 / 2 := by rw [mul_one]; exact hC
  have h3 : (2 : ℝ) ^ l * (ρ ^ (C + 1)) ^ l ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by nlinarith)
  have h4 : (2 : ℝ) ≤ 2 ^ (C + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
      _ ≤ 2 ^ (C + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq : 0 < (ρ ^ (C + 1)) ^ l := by positivity
  calc (2 : ℝ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    _ ≤ 2 ^ (C + 1) * (1 / (ρ ^ (C + 1)) ^ l) := by
        refine mul_le_mul h4 ?_ (by positivity) (by positivity)
        rw [le_div_iff₀ hq]
        exact h3
    _ = (2 / ρ ^ l) ^ (C + 1) := by
        rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (C + 1) l]
        ring
    _ ≤ (2 / e ρ x₀ l) ^ (C + 1) := pow_le_pow_left₀ (by positivity) h2 _
end GeneralPieces.PartAUse
