-- Prove2me | solution 1 for GeneralPieces.Lex.val_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:25.268192+00:00
-- url     : https://prove2.me/submissions/b5e8be2d-97b4-43f8-a648-53d895328d54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
theorem _root_.solution {lam : ℕ} (x : Pieces.Bits lam) : val x = ∑ i ∈ (univ.filter fun i : Fin lam => x i = true).map Fin.valEmbedding, 2 ^ i := by
  unfold AppHalfPieces.val
  rw [sum_map, sum_filter]
  rfl
end GeneralPieces.Lex
