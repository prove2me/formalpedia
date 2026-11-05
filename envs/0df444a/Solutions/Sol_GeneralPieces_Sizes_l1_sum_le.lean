-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:30:45.329011+00:00
-- url     : https://prove2.me/submissions/9ab8975f-08fc-42f7-848b-399a2d5d44a1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_zero
import Theorems.Thm_GeneralPieces_Sizes_l1_add_le

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {ι : Type} (s : Finset ι) (F : ι → V) : l1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (l1_add_le _ _).trans (by gcongr)
end GeneralPieces.Sizes
