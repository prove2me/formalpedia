-- Prove2me | solution 1 for GeneralPieces.Sizes.mul_count_le_wt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:28:29.08821+00:00
-- url     : https://prove2.me/submissions/769aa5d9-e877-4500-bfed-8853c462a6c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (σ : Ptn) (k : ℕ+) : (k : ℕ) * σ.count k ≤ wt σ := by
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have e : wt (a ::ₘ s) = a + wt s := by unfold wt; rw [Multiset.map_cons, Multiset.sum_cons]
    rw [e, Multiset.count_cons]
    split_ifs with hka
    · subst hka
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [Nat.add_zero]
      omega
end GeneralPieces.Sizes
