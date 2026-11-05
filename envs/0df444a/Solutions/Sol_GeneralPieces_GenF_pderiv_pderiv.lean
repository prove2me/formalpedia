-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:58:02.822382+00:00
-- url     : https://prove2.me/submissions/a0619bdf-d9d8-4e7d-9ac8-d71c05a74940

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
theorem _root_.solution (i j : Y) (F : MvPowerSeries Y R) : pderiv R i (pderiv R j F) = pderiv R j (pderiv R i F) := by
  by_cases h : i = j
  · rw [h]
  · ext α
    rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv, add_right_comm, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm h),
      Finsupp.single_eq_of_ne h, add_zero, add_zero]
    ring
end GeneralPieces.GenF
