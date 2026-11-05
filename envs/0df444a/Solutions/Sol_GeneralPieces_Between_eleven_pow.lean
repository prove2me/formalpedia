-- Prove2me | solution 1 for GeneralPieces.Between.eleven_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:43:21.968204+00:00
-- url     : https://prove2.me/submissions/d03b16c5-c4f6-4ca7-8600-68fa769160c1

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
theorem _root_.solution (l : ℕ) : ((11 ^ l : ℕ) : ℝ) / ((12 ^ l : ℕ) : ℝ) = (11 / 12 : ℝ) ^ l := by
  push_cast
  rw [div_pow]
end GeneralPieces.Between
