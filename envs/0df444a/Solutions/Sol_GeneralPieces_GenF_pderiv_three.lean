-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:55:24.077935+00:00
-- url     : https://prove2.me/submissions/b6f94c1c-be6f-499d-a5b2-40ed3e50954a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_pderiv_expW
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
variable {Y A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (i : Y) {a b : MvPowerSeries Y A} (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (c : MvPowerSeries Y A) :
    MvPowerSeries.pderiv A i (expW a * (expW b * c)) =
      (MvPowerSeries.pderiv A i a + MvPowerSeries.pderiv A i b) * (expW a * (expW b * c)) + expW a * (expW b * MvPowerSeries.pderiv A i c) := by
  rw [Derivation.leibniz, Derivation.leibniz, pderiv_expW i ha, pderiv_expW i hb]
  simp only [smul_eq_mul]
  ring
end GeneralPieces.GenF
