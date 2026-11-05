-- Prove2me | solution 1 for GeneralPieces.GenF.wtX_list_xo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:04:47.662378+00:00
-- url     : https://prove2.me/submissions/e83c2596-32fd-4df6-8457-374d22ec5fae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_wtX_xo
import Theorems.Thm_GeneralPieces_GenF_wtX_list_sum

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (a : List ℕ) : wtX (a.map fun n => Finsupp.single (xo rd n) 1).sum = a.sum := wtX_list_sum _ (wtX_xo rd) a
end GeneralPieces.GenF
