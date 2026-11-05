-- Prove2me | solution 1 for GeneralPieces.Bits.Rrow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:30:58.529806+00:00
-- url     : https://prove2.me/submissions/e826430a-2246-470e-90d6-bcd268e279fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_pZ_mono

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (h : ℕ) (s : ℤ) : Rrow h s ≤ (2 * h + 1) * pZ (2 * h + s) := by
  unfold Rrow
  refine (sum_le_card_nsmul _ _ (pZ (2 * h + s)) fun i hi => pZ_mono (by have := mem_range.1 hi; omega)).trans ?_
  rw [card_range, smul_eq_mul]
end GeneralPieces.Bits
