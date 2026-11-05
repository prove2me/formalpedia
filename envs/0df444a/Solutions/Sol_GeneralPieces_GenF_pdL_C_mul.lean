-- Prove2me | solution 1 for GeneralPieces.GenF.pdL_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:58:31.263202+00:00
-- url     : https://prove2.me/submissions/7f55b149-812e-4a12-8bab-3ede2b39df41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
import Theorems.Thm_GeneralPieces_GenF_pdL_cons
import Theorems.Thm_GeneralPieces_GenF_pderiv_C_mul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
namespace GeneralPieces.GenF
theorem _root_.solution (L : List Y) (c : R) (F : MvPowerSeries Y R) : pdL L (C c * F) = C c * pdL L F := by
  induction L generalizing F with
  | nil => rfl
  | cons i L ih => rw [pdL_cons, pdL_cons, pderiv_C_mul, ih]
end GeneralPieces.GenF
