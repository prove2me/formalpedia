-- Prove2me | solution 1 for GeneralPieces.GenF.braW_C_JpV_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:53:06.536757+00:00
-- url     : https://prove2.me/submissions/13f5186c-67be-4f62-9aba-09df3b03ad8b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_lin1_JpV
import Theorems.Thm_GeneralPieces_GenF_bra_single_JpV
import Theorems.Thm_GeneralPieces_GenF_braW_C_lin_mul
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
theorem _root_.solution (σ : Multiset ℕ) (n : ℕ) (w : W) :
    braW σ (MvPowerSeries.C (JpV n) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo 0 ((l : ℤ) - n)) * braW (σ.erase l) w := by
  rw [braW_C_lin_mul (lin1_JpV n)]
  simp only [bra_single_JpV]
end GeneralPieces.GenF
