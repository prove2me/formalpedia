-- Prove2me | solution 1 for GeneralPieces.Lex.IsMu.wt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:32:45.545938+00:00
-- url     : https://prove2.me/submissions/dcbc9af3-7d78-45be-adec-7f7a9f4c75f7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Ring_mem_ptns


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
namespace IsMu
theorem _root_.solution {lam h : ℕ} {mu : Pieces.Bits lam → Ptn} (hmu : IsMu lam h mu) (x : Pieces.Bits lam) : AppHalfPieces.wt (mu x) = h :=
  (GeneralPieces.Ring.mem_ptns h _).1 (hmu x).1
end IsMu
end GeneralPieces.Lex
