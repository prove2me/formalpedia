-- Prove2me | solution 1 for GeneralPieces.Lex.IsMu.injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:25:08.287955+00:00
-- url     : https://prove2.me/submissions/3a884d77-fe04-46c2-9aee-772485ddb6c9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Lex_val_injective

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
namespace IsMu
theorem _root_.solution {lam h : ℕ} {mu : Pieces.Bits lam → Ptn} (hmu : IsMu lam h mu) : Function.Injective mu := fun x y hxy =>
  val_injective lam (by rw [← (hmu x).2, ← (hmu y).2, hxy])
end IsMu
end GeneralPieces.Lex
