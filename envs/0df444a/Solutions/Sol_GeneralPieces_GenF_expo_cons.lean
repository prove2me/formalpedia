-- Prove2me | solution 1 for GeneralPieces.GenF.expo_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:56:51.873239+00:00
-- url     : https://prove2.me/submissions/bf8e2595-9e01-4772-982e-16c8a355fcdc

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
theorem _root_.solution (i : Y) (L : List Y) : expo (i :: L) = Finsupp.single i 1 + expo L := by simp [expo]
end GeneralPieces.GenF
