-- Prove2me | solution 1 for GeneralPieces.GenF.wtX_list_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:05:38.693411+00:00
-- url     : https://prove2.me/submissions/18d333ab-5d82-4c2b-9933-72d33727fedd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_wtX_list_xi

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (a : List ℕ) : wtX (a.map fun n => Finsupp.single (Sum.inl n : X) 1).sum = a.sum := wtX_list_xi false a
end GeneralPieces.GenF
