-- Prove2me | solution 1 for GeneralPieces.Lex.rank_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:23:11.002075+00:00
-- url     : https://prove2.me/submissions/41fb698b-b7a1-4fec-ab47-cbbe122982d3

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
variable {α β : Type} [LinearOrder β] [DecidableRel fun a b : β => a < b] (S : Finset α) (f : α → β)
namespace GeneralPieces.Lex
theorem _root_.solution {a : α} (ha : a ∈ S) : #{c ∈ S | f c < f a} < #S :=
  card_lt_card ⟨filter_subset _ _, fun hsub => lt_irrefl _ (mem_filter.1 (hsub ha)).2⟩
end GeneralPieces.Lex
