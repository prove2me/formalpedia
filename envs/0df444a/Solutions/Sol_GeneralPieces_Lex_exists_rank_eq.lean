-- Prove2me | solution 1 for GeneralPieces.Lex.exists_rank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:24:51.398754+00:00
-- url     : https://prove2.me/submissions/756286d3-6fe7-4e04-acc2-be1fa9ecd73e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Lex_rank_lt_card
import Theorems.Thm_GeneralPieces_Lex_rank_injOn

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
variable {α β : Type} [LinearOrder β] [DecidableRel fun a b : β => a < b] (S : Finset α) (f : α → β)
namespace GeneralPieces.Lex
theorem _root_.solution (hf : Set.InjOn f S) {j : ℕ} (hj : j < #S) : ∃ a ∈ S, #{c ∈ S | f c < f a} = j := by
  have h1 : S.image (fun a => #{c ∈ S | f c < f a}) = range #S := by
    refine eq_of_subset_of_card_le (fun i hi => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hi
      exact mem_range.2 (rank_lt_card S f ha)
    · rw [card_range, card_image_of_injOn (rank_injOn S f hf)]
  obtain ⟨a, ha, h⟩ := mem_image.1 (h1 ▸ mem_range.2 hj : j ∈ S.image _)
  exact ⟨a, ha, h⟩
end GeneralPieces.Lex
