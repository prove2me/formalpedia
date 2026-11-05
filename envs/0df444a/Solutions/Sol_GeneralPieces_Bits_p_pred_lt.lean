-- Prove2me | solution 1 for GeneralPieces.Bits.p_pred_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:30:27.992+00:00
-- url     : https://prove2.me/submissions/24d93de2-5a4e-4c44-8c4f-329b0219334d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_ClauseBound_Part_Bits_p_pred_lt
import Theorems.Thm_GeneralPieces_Lex_hOf_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution {lam : ℕ} (hl : 1 ≤ lam) : p (AppHalfPieces.hOf lam - 1) < 2 ^ lam := by
  rw [hOf_eq]
  exact ClauseBound.Part.Bits.p_pred_lt hl
end GeneralPieces.Bits
