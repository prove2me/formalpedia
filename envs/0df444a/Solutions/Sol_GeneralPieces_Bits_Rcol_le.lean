-- Prove2me | solution 1 for GeneralPieces.Bits.Rcol_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:31:33.336841+00:00
-- url     : https://prove2.me/submissions/40076003-a375-4ac7-8583-e3bec3f3b926

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
theorem _root_.solution (h : ℕ) (s : ℤ) : Rcol h s ≤ (2 * h + 1) * pZ (2 * h - s) := by
  unfold Rcol
  refine (sum_le_card_nsmul _ _ (pZ (2 * h - s)) fun i _ => pZ_mono (by omega)).trans ?_
  rw [card_range, smul_eq_mul]
end GeneralPieces.Bits
