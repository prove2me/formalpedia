-- Prove2me | solution 1 for GeneralPieces.Bits.four_mul_rho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:28:11.26759+00:00
-- url     : https://prove2.me/submissions/5b74cbdc-3fd1-4b47-b602-11cc86877bcb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution : 4 * (1 / √(2 : ℝ)) = 2 * √2 := by
  rw [← Real.sqrt_div_self']
  ring
end GeneralPieces.Bits
