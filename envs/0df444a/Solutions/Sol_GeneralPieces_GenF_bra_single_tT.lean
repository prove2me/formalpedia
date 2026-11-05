-- Prove2me | solution 1 for GeneralPieces.GenF.bra_single_tT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:49:48.366606+00:00
-- url     : https://prove2.me/submissions/edca36dc-0d64-476f-870e-63cd7622fd5b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_coeff_single_X
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (l k : ℕ) : bra {l} (tT k) = if l = k then 1 else 0 := by
  ext y : 2
  unfold tT
  rw [coeff_bra, HahnSeries.C_apply, HahnSeries.coeff_single, Multiset.toFinsupp_singleton]
  by_cases hy : y = 0
  · rw [if_pos hy, coeff_single_X, hy]
    split_ifs <;> simp
  · rw [if_neg hy, MvPolynomial.coeff_zero]
    split_ifs
    · rw [HahnSeries.coeff_one, if_neg hy]
    · rfl
end GeneralPieces.GenF
