-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:27:06.457275+00:00
-- url     : https://prove2.me/submissions/ac369a98-209c-41f3-9204-f29336754407

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_isInt_add
import Theorems.Thm_GeneralPieces_Pcs_isInt_zero

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution {ι : Type} (s : Finset ι) {F : ι → V} (hF : ∀ i ∈ s, IsInt (F i)) : IsInt (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isInt_zero
  | insert x s hx ih =>
    rw [sum_insert hx]
    exact isInt_add (hF x (mem_insert_self _ _)) (ih fun i hi => hF i (mem_insert_of_mem hi))
end GeneralPieces.Pcs
