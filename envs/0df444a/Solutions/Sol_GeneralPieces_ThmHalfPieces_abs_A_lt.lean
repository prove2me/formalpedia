-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.abs_A_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:44:49.848108+00:00
-- url     : https://prove2.me/submissions/d886dc96-4dc0-4d13-8ec3-b6fb24d4e4da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_cast_A
import Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_piece_le
import Theorems.Thm_GeneralPieces_ThmHalfPieces_bound_lt_big

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) :
    |(fam h mu).A s x y u v| < 2 ^ ClauseBound.Boson.big h := by
  have h1 := abs_piece_le hP hmu hh hs x y u v
  rw [← cast_A hP hmu hh] at h1
  have h2 : |(fam h mu).A s x y u v| ≤ ((Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) : ℕ) : ℤ) := by exact_mod_cast h1
  exact h2.trans_lt (by exact_mod_cast bound_lt_big h)
end GeneralPieces.ThmHalfPieces
