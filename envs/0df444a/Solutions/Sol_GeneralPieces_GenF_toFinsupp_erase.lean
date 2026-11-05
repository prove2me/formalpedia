-- Prove2me | solution 1 for GeneralPieces.GenF.toFinsupp_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:01.278333+00:00
-- url     : https://prove2.me/submissions/41ee7d53-9b71-4e6b-9126-bca8ff21af12

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (σ : Multiset ℕ) (l : ℕ) : Multiset.toFinsupp (σ.erase l) = Multiset.toFinsupp σ - Finsupp.single l 1 := by
  ext x
  rw [Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply, Multiset.toFinsupp_apply]
  by_cases h : x = l
  · subst h
    rw [Multiset.count_erase_self, Finsupp.single_eq_same]
  · rw [Multiset.count_erase_of_ne h, Finsupp.single_eq_of_ne h, Nat.sub_zero]
end GeneralPieces.GenF
