-- Prove2me | solution 1 for GeneralPieces.Asymptotic.alpha_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:41:51.053193+00:00
-- url     : https://prove2.me/submissions/d9633f95-f126-4881-97ea-c72cfe4a6ddf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Asymptotic
open Levels.Gen ClauseBound.Gen GeneralPieces.PartA
namespace GeneralPieces.Asymptotic
theorem _root_.solution : Real.logb 2 (1 / (1 / Real.sqrt 2)) = 1 / 2 := by
  rw [one_div_one_div, Real.sqrt_eq_rpow, Real.logb_rpow (by norm_num) (by norm_num)]
end GeneralPieces.Asymptotic
