-- Prove2me | solution 1 for GeneralPieces.Lex.desc_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:24.056815+00:00
-- url     : https://prove2.me/submissions/c1ea3110-c3ee-4701-887e-126462144e73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Ring_toN_injective


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
theorem _root_.solution : Function.Injective desc := fun μ ν h => by
  have h1 : ((desc μ : List ℕ) : Multiset ℕ) = desc ν := by rw [h]
  unfold desc at h1
  rw [Multiset.sort_eq, Multiset.sort_eq] at h1
  exact GeneralPieces.Ring.toN_injective h1
end GeneralPieces.Lex
