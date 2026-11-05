-- Prove2me | solution 1 for GeneralPieces.PartAUse.inv_logK_pow_le_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:52:06.907009+00:00
-- url     : https://prove2.me/submissions/292b84cc-5e34-4e66-904a-ed81b39921dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_GeneralPieces_PartAUse_two_pow_le_logK
import Theorems.Thm_GeneralPieces_PartAUse_inv_logK_le_e

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hx : 2 ≤ x₀) (l C : ℕ) (hC : 1 ≤ C) :
    1 / Real.logb 2 (K x₀ l) ^ C ≤ e ρ x₀ l := by
  have h1 : (1 : ℝ) ≤ Real.logb 2 (K x₀ l) := le_trans (one_le_pow₀ (by norm_num)) (two_pow_le_logK hA hx l)
  exact le_trans (one_div_le_one_div_of_le (by linarith) (le_self_pow₀ h1 (by omega))) (inv_logK_le_e hA hρ hx l)
end GeneralPieces.PartAUse
