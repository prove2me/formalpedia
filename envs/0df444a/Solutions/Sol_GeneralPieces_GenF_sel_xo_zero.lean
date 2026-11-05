-- Prove2me | solution 1 for GeneralPieces.GenF.sel_xo_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:47:15.086525+00:00
-- url     : https://prove2.me/submissions/cc1e17e5-5381-4cea-ae0b-06002177c2d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
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
variable {R : Type} [Zero R]
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (f g : ℕ → R) : sel rd f g (xo rd 0) = 0 := by
  cases rd <;> simp [sel, xo, z0]
end GeneralPieces.GenF
