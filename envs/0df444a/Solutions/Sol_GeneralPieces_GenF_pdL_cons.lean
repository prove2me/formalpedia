-- Prove2me | solution 1 for GeneralPieces.GenF.pdL_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:27:28.073061+00:00
-- url     : https://prove2.me/submissions/b1ded532-b9b5-4f94-a947-a216b9900d07

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
theorem _root_.solution (i : Y) (L : List Y) (F : MvPowerSeries Y R) : pdL (i :: L) F = pdL L (pderiv R i F) := rfl
end GeneralPieces.GenF
