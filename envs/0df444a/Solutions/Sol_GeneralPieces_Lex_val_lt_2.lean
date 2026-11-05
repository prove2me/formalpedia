-- Prove2me | solution 2 for GeneralPieces.Lex.val_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:23:12.395265+00:00
-- url     : https://prove2.me/submissions/98fc2481-e8f2-4362-9885-09eeceffe41b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Lex_val_eq

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
theorem _root_.solution {lam : ℕ} (x : Pieces.Bits lam) : val x < 2 ^ lam := by
  rw [val_eq]
  refine Nat.geomSum_lt (le_refl 2) fun i hi => ?_
  obtain ⟨j, _, rfl⟩ := mem_map.1 hi
  exact j.isLt
end GeneralPieces.Lex
