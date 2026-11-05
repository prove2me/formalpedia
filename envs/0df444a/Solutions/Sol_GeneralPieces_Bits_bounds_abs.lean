-- Prove2me | solution 1 for GeneralPieces.Bits.bounds_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:28:01.810033+00:00
-- url     : https://prove2.me/submissions/12d6ff82-ed46-4404-a8f4-b6caa3319dd6

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
theorem _root_.solution (hB : Bounds B C) : Bounds |B| C := by
  refine ⟨fun E hE => ?_, hB.2⟩
  have h1 := hB.1 E hE
  have h2 : 0 ≤ logb 2 E := Real.logb_nonneg (by norm_num) (by exact_mod_cast hE)
  have h3 : B * logb 2 E ≤ |B| * logb 2 E := mul_le_mul_of_nonneg_right (le_abs_self B) h2
  linarith
end GeneralPieces.Bits
