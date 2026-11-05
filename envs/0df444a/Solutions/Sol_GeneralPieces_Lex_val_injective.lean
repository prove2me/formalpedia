-- Prove2me | solution 1 for GeneralPieces.Lex.val_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:24:04.858064+00:00
-- url     : https://prove2.me/submissions/b3c8f270-5add-45d1-a757-a643c39537eb

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
theorem _root_.solution (lam : ℕ) : Function.Injective (val (lam := lam)) := fun x y h => by
  rw [val_eq, val_eq] at h
  have h1 := map_injective _ (Finset.geomSum_injective (le_refl 2) h)
  funext i
  have h2 : x i = true ↔ y i = true := by
    have := Finset.ext_iff.1 h1 i
    simpa using this
  cases hx : x i <;> cases hy : y i <;> simp_all
end GeneralPieces.Lex
