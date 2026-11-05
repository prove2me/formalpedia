-- Prove2me | solution 1 for GeneralPieces.LemQ.eq_sum_ptnsLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:11:04.382819+00:00
-- url     : https://prove2.me/submissions/0ffcc516-a7fd-46e2-b6d0-8e8e58d35d24

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_coef_sum
import Theorems.Thm_GeneralPieces_LemQ_eq_sum_of_subset
import Theorems.Thm_GeneralPieces_LemQ_coef_part
import Theorems.Thm_GeneralPieces_LemQ_mem_ptnsLe

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution {h : ℕ} {a : V} (ha : WtLe h a) : a = ∑ μ ∈ ptnsLe h, coef μ a • tpow μ := by
  refine eq_sum_of_subset a _ fun μ hμ => (mem_ptnsLe h μ).2 ?_
  by_contra hlt
  refine hμ ?_
  rw [ha, coef_sum]
  refine sum_eq_zero fun h' hh' => ?_
  rw [coef_part, if_neg (by have := mem_range.1 hh'; omega)]
end GeneralPieces.LemQ
