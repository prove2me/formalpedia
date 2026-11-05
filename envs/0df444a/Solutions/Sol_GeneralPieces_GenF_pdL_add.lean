-- Prove2me | solution 1 for GeneralPieces.GenF.pdL_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:33.564189+00:00
-- url     : https://prove2.me/submissions/c2885c10-5e69-4655-912a-ca5439e12c99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
import Theorems.Thm_GeneralPieces_GenF_pdL_cons

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
namespace GeneralPieces.GenF
theorem _root_.solution (L : List Y) (F G : MvPowerSeries Y R) : pdL L (F + G) = pdL L F + pdL L G := by
  induction L generalizing F G with
  | nil => rfl
  | cons i L ih => rw [pdL_cons, pdL_cons, pdL_cons, map_add, ih]
end GeneralPieces.GenF
