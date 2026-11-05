-- Prove2me | solution 1 for GeneralPieces.GenF.bra_tT_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:51:45.748201+00:00
-- url     : https://prove2.me/submissions/5be648d4-8aed-4f13-8ff3-3d396251cb69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_bra_lin_mul
import Theorems.Thm_GeneralPieces_GenF_lin1_tT
import Theorems.Thm_GeneralPieces_GenF_bra_single_tT
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
theorem _root_.solution (σ : Multiset ℕ) (k : ℕ) (f : Tv) : bra σ (tT k * f) = if k ∈ σ then bra (σ.erase k) f else 0 := by
  rw [bra_lin_mul (lin1_tT k)]
  simp only [bra_single_tT, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Multiset.mem_toFinset]
end GeneralPieces.GenF
