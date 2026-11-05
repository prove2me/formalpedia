-- Prove2me | solution 1 for GeneralPieces.Sizes.Delta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:27:42.446826+00:00
-- url     : https://prove2.me/submissions/fa72f8ca-e8f9-4fc3-a48c-8c8ce6d5f2c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_p_mono
import Theorems.Thm_ClauseBound_Part_p_mono


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (h : ℕ) : Delta h ≤ (4 * h + 1) * Partitions.p (4 * h) := by
  unfold Delta
  refine (sum_le_card_nsmul _ _ (Partitions.p (4 * h)) fun E hE => p_mono (by have := mem_range.1 hE; omega)).trans ?_
  rw [card_range, smul_eq_mul]
end GeneralPieces.Sizes
