-- Prove2me | solution 1 for GeneralPieces.Lex.existsUnique_isMu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:27:31.768527+00:00
-- url     : https://prove2.me/submissions/304d7cee-fda6-45e6-832b-02a7bedf1b07

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Lex_lexNum_injOn
import Theorems.Thm_GeneralPieces_Lex_exists_lexNum_eq
import Theorems.Thm_GeneralPieces_Lex_val_lt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
theorem _root_.solution {lam h : ℕ} (hp : 2 ^ lam ≤ Partitions.p h) : ∃! mu : Pieces.Bits lam → Ptn, IsMu lam h mu := by
  choose mu h1 h2 using fun x : Pieces.Bits lam => exists_lexNum_eq ((val_lt x).trans_le hp)
  refine ⟨mu, fun x => ⟨h1 x, h2 x⟩, fun mu' h' => funext fun x => ?_⟩
  exact lexNum_injOn h (h' x).1 (h1 x) ((h' x).2.trans (h2 x).symm)
end GeneralPieces.Lex
