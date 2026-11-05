-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.card_terms_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:41:46.603068+00:00
-- url     : https://prove2.me/submissions/86cc27c8-0456-4e0a-bfad-e4490242ead3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_card_ptnsZ

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (h : ℕ) (s : ℤ) : ∑ i ∈ range (2 * h + 1), #(ptnsZ (2 * h - s - i)) = Rcol h s :=
  sum_congr rfl fun _ _ => card_ptnsZ _
end GeneralPieces.ThmHalfPieces
