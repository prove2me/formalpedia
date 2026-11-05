-- Prove2me | solution 1 for GeneralPieces.GenF.Y.aL_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:59:59.16368+00:00
-- url     : https://prove2.me/submissions/ed2b176c-acb6-41a5-aa5e-86d0316386fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open GeneralPieces.GenF.Y
variable {Z R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF.Y
theorem _root_.solution (ι : ℕ → X) (n : ℕ) (a : List ℕ) : aL ι (n :: a) = aL ι a + Finsupp.single (ι n) 1 := by
  rw [aL, aL, List.map_cons, List.sum_cons, add_comm]
end GeneralPieces.GenF.Y
