-- Prove2me | solution 1 for GeneralPieces.GenF.bra_prod_tT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:52:48.335614+00:00
-- url     : https://prove2.me/submissions/bbc91d2d-cc40-4411-a2e7-b2f9d0b023b4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_bra_one
import Theorems.Thm_GeneralPieces_GenF_bra_tT_mul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (σ σ' : Multiset ℕ) : bra σ ((σ'.map tT).prod) = if σ = σ' then 1 else 0 := by
  induction σ' using Multiset.induction_on generalizing σ with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, bra_one]
  | cons k σ' ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, bra_tT_mul]
    by_cases hk : k ∈ σ
    · rw [if_pos hk, ih]
      by_cases e : σ.erase k = σ'
      · rw [if_pos e, if_pos (by rw [← e, Multiset.cons_erase hk])]
      · rw [if_neg e, if_neg fun e' => e (by rw [e', Multiset.erase_cons_head])]
    · rw [if_neg hk, if_neg fun e' => hk (by rw [e']; exact Multiset.mem_cons_self k σ')]
end GeneralPieces.GenF
