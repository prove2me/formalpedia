-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.piece_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:28:26.457895+00:00
-- url     : https://prove2.me/submissions/76ee8bc3-c25f-44f8-923e-f3e4c4248349

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_cast_num_coef
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    piece h mu s x y u v = ((∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (s + i),
      fa h i (s - h + i) (mu x) σ (mu y) * fb (h - s - i) (mu v) (mu u) σ : ℤ) : ℚ) := by
  unfold piece
  rw [hP.row h _ _ _ _ s hh (IsMu.wt hmu x) (IsMu.wt hmu y) (IsMu.wt hmu u) (IsMu.wt hmu v)]
  push_cast
  refine sum_congr rfl fun i _ => sum_congr rfl fun σ _ => ?_
  rw [fa, fb]
  push_cast
  rw [cast_num_coef (hP.int_a _ _ _ _ _), cast_num_coef (hP.int_b _ _ _)]
end GeneralPieces.ThmHalfPieces
