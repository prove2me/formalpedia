-- Prove2me | solution 1 for GeneralPieces.PartAUse.inv_two_pow_le_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:02:47.008617+00:00
-- url     : https://prove2.me/submissions/90da72ad-ec3e-4d15-8da3-c46920497720

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (l : ℕ) : 1 / (2 : ℝ) ^ (l + 1) ≤ e ρ x₀ l := by
  have h1 : (1 / 2 : ℝ) ^ l ≤ ρ ^ l := pow_le_pow_left₀ (by norm_num) hρ l
  have h2 : 1 / (2 : ℝ) ^ (l + 1) = 1 / 2 * (1 / 2) ^ l := by rw [pow_succ, one_div_pow]; field_simp
  rw [h2]
  linarith [(hA.e_bounds l).1]
end GeneralPieces.PartAUse
