-- Prove2me | solution 1 for GeneralPieces.Pcs.wtLe_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:24:05.909219+00:00
-- url     : https://prove2.me/submissions/cb61a193-0e72-4e16-bcaf-39d499bf5876

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_LemQ_coef_part
import Theorems.Thm_GeneralPieces_LemQ_coef_sum
import Theorems.Thm_GeneralPieces_Ring_ext_coef


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution {h : ℕ} {a : V} (ha : Le h a) : WtLe h a := by
  unfold WtLe
  refine ext_coef fun π => ?_
  rw [coef_sum]
  simp only [coef_part]
  rw [sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (mem_range.2 (by have := ha π hne; omega))
end GeneralPieces.Pcs
