-- Prove2me | solution 1 for GeneralPieces.GenF.pdL_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:40.911509+00:00
-- url     : https://prove2.me/submissions/2856a9ab-44c9-4530-9f80-c33fb6366797

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
theorem _root_.solution (L : List Y) : pdL L (0 : MvPowerSeries Y R) = 0 := by
  induction L with
  | nil => rfl
  | cons i L ih => rw [pdL_cons, map_zero, ih]
end GeneralPieces.GenF
