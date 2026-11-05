-- Prove2me | solution 1 for GeneralPieces.Ring.op_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:19:32.262596+00:00
-- url     : https://prove2.me/submissions/6f4fdc48-689a-4b28-8c10-31f1d4b4aa44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_op_eq_sum
import Theorems.Thm_ClauseBound_Boson_op_eq_sum


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (a a' : V) (r : ℤ) (f : V) : op (a + a') r f = op a r f + op a' r f := by
  rw [op_eq_sum (a + a') r f (S := a.support ∪ a'.support) support_add, op_eq_sum a r f (S := a.support ∪ a'.support) subset_union_left,
    op_eq_sum a' r f (S := a.support ∪ a'.support) subset_union_right, ← sum_add_distrib]
  exact sum_congr rfl fun m _ => by rw [coeff_add, add_smul]
end GeneralPieces.Ring
