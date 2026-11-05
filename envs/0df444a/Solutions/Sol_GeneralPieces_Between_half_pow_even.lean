-- Prove2me | solution 1 for GeneralPieces.Between.half_pow_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:43:27.978238+00:00
-- url     : https://prove2.me/submissions/2575da42-f324-48bc-bc4b-c37416461a26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_Num_Between
import Theorems.Thm_Groundwork_PolyT_div_pow
attribute [local fun_prop] Groundwork.PolyT.div_pow



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Between
open Groundwork PaddedDescent.F Levels.Gen
namespace GeneralPieces.Between
theorem _root_.solution (j : ℕ) : (1 / Real.sqrt 2) ^ (2 * j) = 1 / (2 : ℝ) ^ j := by
  rw [pow_mul, div_pow, Real.sq_sqrt (by norm_num), one_pow, div_pow, one_pow]
end GeneralPieces.Between
