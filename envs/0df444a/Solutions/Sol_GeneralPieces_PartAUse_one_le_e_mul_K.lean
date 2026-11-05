-- Prove2me | solution 1 for GeneralPieces.PartAUse.one_le_e_mul_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:45:01.511205+00:00
-- url     : https://prove2.me/submissions/4a70fba5-f69f-4a21-ba25-1ca65b47d9da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_GeneralPieces_PartAUse_e_nonneg
import Theorems.Thm_GeneralPieces_PartAUse_inv_two_pow_le_e
import Theorems.Thm_GeneralPieces_PartA_K_ge_pow
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (l : ℕ) : 1 ≤ e ρ x₀ l * K x₀ l := by
  have h1 : 2 ^ (l + 1) ≤ 2 ^ (18 * (l + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (l + 1) ≤ K x₀ l := by exact_mod_cast h1.trans (K_ge_pow x₀ l hx)
  calc (1 : ℝ) = 1 / 2 ^ (l + 1) * 2 ^ (l + 1) := by field_simp
    _ ≤ e ρ x₀ l * K x₀ l := mul_le_mul (inv_two_pow_le_e hA hρ l) h2 (by positivity) (e_nonneg hA (by linarith) l)
end GeneralPieces.PartAUse
