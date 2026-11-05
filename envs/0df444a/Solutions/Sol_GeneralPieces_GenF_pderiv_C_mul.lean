-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:57:42.393255+00:00
-- url     : https://prove2.me/submissions/6f8d64c6-529b-412f-bc4d-24a6a113e051

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
namespace GeneralPieces.GenF
theorem _root_.solution (i : Y) (c : R) (F : MvPowerSeries Y R) : pderiv R i (C c * F) = C c * pderiv R i F := by
  rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
end GeneralPieces.GenF
