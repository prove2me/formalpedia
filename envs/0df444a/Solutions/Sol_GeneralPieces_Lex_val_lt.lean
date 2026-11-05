-- Prove2me | solution 1 for GeneralPieces.Lex.val_lt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:08:40.786268+00:00
-- url     : https://prove2.me/submissions/4e3f4a99-7d55-4288-bb6a-9f55fba4c71c

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

theorem solution {lam : ℕ} (x : Pieces.Bits lam) : val x < 2 ^ lam := by
  have val_eq : val x = ∑ i ∈ (univ.filter fun i : Fin lam => x i = true).map Fin.valEmbedding, 2 ^ i := by
    unfold AppHalfPieces.val
    rw [sum_map, sum_filter]
    rfl
  rw [val_eq]
  refine Nat.geomSum_lt (le_refl 2) fun i hi => ?_
  obtain ⟨j, _, rfl⟩ := mem_map.1 hi
  exact j.isLt
