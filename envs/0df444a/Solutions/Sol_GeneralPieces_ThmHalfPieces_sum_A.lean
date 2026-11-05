-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.sum_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:34:59.886463+00:00
-- url     : https://prove2.me/submissions/1a6d809f-d656-4023-9359-9bce1f6032fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_cast_A
import Theorems.Thm_GeneralPieces_Lex_IsMu_injective
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (x y u v : Pieces.Bits lam) :
    ∑ s ∈ (fam h mu).I, (fam h mu).A s x y u v = (fam h mu).d * Pieces.cross x y u v := by
  have e : ((∑ s ∈ (fam h mu).I, (fam h mu).A s x y u v : ℤ) : ℚ) = (((fam h mu).d * Pieces.cross x y u v : ℤ) : ℚ) := by
    push_cast
    simp_rw [cast_A hP hmu hh]
    have h1 := hP.sum h (mu x) (mu y) (mu u) (mu v) hh (IsMu.wt hmu x) (IsMu.wt hmu y) (IsMu.wt hmu u) (IsMu.wt hmu v)
    change ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), coef (mu u) (Q h s (aFam (mu x)) (bFam (mu v)) (tpow (mu y))) = ((h.factorial : ℤ) : ℚ) * _
    rw [h1, Pieces.cross]
    have h2 : (mu x = mu v ∧ mu y = mu u) ↔ (x = v ∧ y = u) := by rw [(IsMu.injective hmu).eq_iff, (IsMu.injective hmu).eq_iff]
    by_cases h3 : x = v ∧ y = u
    · rw [if_pos (h2.2 h3), if_pos h3]
      push_cast
      ring
    · rw [if_neg (fun h4 => h3 (h2.1 h4)), if_neg h3]
      push_cast
      ring
  exact_mod_cast e
end GeneralPieces.ThmHalfPieces
