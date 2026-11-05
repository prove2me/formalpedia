-- Prove2me | solution 1 for GeneralPieces.Sizes.sum_toL_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:30:26.96592+00:00
-- url     : https://prove2.me/submissions/f96faaa1-39aa-4b1b-a83e-0a3714bc84c0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (m : ℕ+ →₀ ℕ) : (toL (Finsupp.toMultiset m).toList).sum = Finsupp.weight wgt m := by
  have h1 := weight_toFinsupp (Finsupp.toMultiset m)
  rw [Finsupp.toMultiset_toFinsupp] at h1
  rw [h1, wt, toL]
  conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
  rw [Multiset.map_coe, Multiset.sum_coe]
end GeneralPieces.Sizes
