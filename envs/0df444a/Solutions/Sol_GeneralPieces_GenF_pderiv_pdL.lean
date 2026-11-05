-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_pdL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:58:37.138073+00:00
-- url     : https://prove2.me/submissions/3964dfe8-4978-4294-be65-d3a191a32b3f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
import Theorems.Thm_GeneralPieces_GenF_pdL_cons
import Theorems.Thm_GeneralPieces_GenF_pderiv_pderiv

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
namespace GeneralPieces.GenF
theorem _root_.solution (i : Y) (L : List Y) (F : MvPowerSeries Y R) : pderiv R i (pdL L F) = pdL L (pderiv R i F) := by
  induction L generalizing F with
  | nil => rfl
  | cons j L ih => rw [pdL_cons, pdL_cons, ih, pderiv_pderiv]
end GeneralPieces.GenF
