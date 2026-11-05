-- Prove2me | solution 1 for GeneralPieces.Lex.rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:22:50.555346+00:00
-- url     : https://prove2.me/submissions/73f7fed4-d406-4c55-8018-8c04898943bc

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
theorem _root_.solution {a b : α} (ha : a ∈ S) (hab : f a < f b) : #{c ∈ S | f c < f a} < #{c ∈ S | f c < f b} := by
  refine card_lt_card ⟨fun c hc => ?_, fun hsub => ?_⟩
  · exact mem_filter.2 ⟨(mem_filter.1 hc).1, (mem_filter.1 hc).2.trans hab⟩
  · exact lt_irrefl _ (mem_filter.1 (hsub (mem_filter.2 ⟨ha, hab⟩))).2
end GeneralPieces.Lex
