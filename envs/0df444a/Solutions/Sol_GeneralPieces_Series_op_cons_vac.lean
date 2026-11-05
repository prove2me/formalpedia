-- Prove2me | solution 1 for GeneralPieces.Series.op_cons_vac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:12.222848+00:00
-- url     : https://prove2.me/submissions/ff0f99e3-e84c-410a-a2d2-e7c059867409

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
namespace GeneralPieces.Series
theorem _root_.solution (n : ℕ) (b : List ℕ) (r : ℤ) (τ : Multiset ℕ) :
    op (n :: b) r τ 0 = ∑ l ∈ τ.toFinset, bet n l * op b (r - l) (τ.erase l) 0 := by
  show nop n (op b) r τ 0 = _
  rw [nop, Multiset.toFinset_zero, sum_empty, add_zero]
  exact sum_congr rfl fun l hl => by rw [cre, if_pos (Multiset.mem_toFinset.1 hl)]
end GeneralPieces.Series
