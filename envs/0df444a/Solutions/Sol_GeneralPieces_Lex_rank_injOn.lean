-- Prove2me | solution 1 for GeneralPieces.Lex.rank_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:23:49.845681+00:00
-- url     : https://prove2.me/submissions/7a707e8b-e737-4734-a3b8-15ffe299d962

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Lex_rank_lt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
variable {α β : Type} [LinearOrder β] [DecidableRel fun a b : β => a < b] (S : Finset α) (f : α → β)
namespace GeneralPieces.Lex
theorem _root_.solution (hf : Set.InjOn f S) : Set.InjOn (fun a => #{c ∈ S | f c < f a}) S := by
  intro a ha b hb hab
  rcases lt_trichotomy (f a) (f b) with h | h | h
  · exact absurd hab (rank_lt S f ha h).ne
  · exact hf ha hb h
  · exact absurd hab (rank_lt S f hb h).ne'
end GeneralPieces.Lex
