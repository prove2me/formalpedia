-- Prove2me | solution 1 for GeneralPieces.Pcs.Le.sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:25:36.559685+00:00
-- url     : https://prove2.me/submissions/53216461-4544-4c71-9b46-96f0d2f17c2a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_Le_add
import Theorems.Thm_GeneralPieces_Pcs_Le_zero

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
namespace Le
theorem _root_.solution {ι : Type} {h : ℕ} (s : Finset ι) {F : ι → V} (hF : ∀ i ∈ s, Le h (F i)) : Le h (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Le.zero h
  | insert x s hx ih =>
    rw [sum_insert hx]
    exact (hF x (mem_insert_self _ _)).add (ih fun i hi => hF i (mem_insert_of_mem hi))
end Le
end GeneralPieces.Pcs
