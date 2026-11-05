-- Prove2me | solution 1 for GeneralPieces.GenF.bra_JpV_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:52:04.731313+00:00
-- url     : https://prove2.me/submissions/bb08eb61-f8aa-4155-8a28-351ff83f27a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_bra_lin_mul
import Theorems.Thm_GeneralPieces_GenF_lin1_JpV
import Theorems.Thm_GeneralPieces_GenF_bra_single_JpV
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
theorem _root_.solution (σ : Multiset ℕ) (n : ℕ) (f : Tv) :
    bra σ (JpV n * f) = ∑ l ∈ σ.toFinset, ((bet n l : ℚ) • mo 0 ((l : ℤ) - n)) * bra (σ.erase l) f := by
  rw [bra_lin_mul (lin1_JpV n)]
  simp only [bra_single_JpV]
end GeneralPieces.GenF
