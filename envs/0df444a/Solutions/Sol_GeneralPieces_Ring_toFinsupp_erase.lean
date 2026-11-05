-- Prove2me | solution 1 for GeneralPieces.Ring.toFinsupp_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:33:08.442204+00:00
-- url     : https://prove2.me/submissions/d2be5288-a2ba-4d5a-b61c-474d528104e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (π : Ptn) (l : ℕ+) : Multiset.toFinsupp (π.erase l) = Multiset.toFinsupp π - Finsupp.single l 1 := by
  ext x
  rw [Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply, Multiset.toFinsupp_apply]
  by_cases h : x = l
  · subst h
    rw [Multiset.count_erase_self, Finsupp.single_eq_same]
  · rw [Multiset.count_erase_of_ne h, Finsupp.single_eq_of_ne h, Nat.sub_zero]
end GeneralPieces.Ring
