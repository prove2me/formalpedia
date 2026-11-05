-- Prove2me | solution 1 for GeneralPieces.Consts.four_mul_rho_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:52.616165+00:00
-- url     : https://prove2.me/submissions/56a35d2e-12ed-43d9-a447-efaf446cda9e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_GeneralPieces_Half_Consts
import Theorems.Thm_GeneralPieces_Bits_four_mul_rho


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Real ClauseBound.Inst.Half
open GeneralPieces.Consts
namespace GeneralPieces.Consts
theorem _root_.solution : 4 * (1 / √(2 : ℝ)) ≤ 3 := by
  rw [Bits.four_mul_rho]
  have h1 : √(2 : ℝ) ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  linarith
end GeneralPieces.Consts
