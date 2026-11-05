-- Prove2me | solution 1 for GeneralPieces.Lex.exists_lexNum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:26:17.069844+00:00
-- url     : https://prove2.me/submissions/19e730a1-d7fe-4441-862d-130bd018d97c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Lex_exists_rank_eq
import Theorems.Thm_GeneralPieces_Lex_desc_injective
import Theorems.Thm_GeneralPieces_Ring_card_ptns


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
theorem _root_.solution {h j : ℕ} (hj : j < Partitions.p h) : ∃ μ ∈ ptns h, lexNum h μ = j :=
  exists_rank_eq (ptns h) desc desc_injective.injOn (by rwa [GeneralPieces.Ring.card_ptns])
end GeneralPieces.Lex
