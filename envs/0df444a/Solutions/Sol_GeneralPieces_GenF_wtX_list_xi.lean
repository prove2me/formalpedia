-- Prove2me | solution 1 for GeneralPieces.GenF.wtX_list_xi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:04:23.559423+00:00
-- url     : https://prove2.me/submissions/20a21fa3-b84b-444c-bffc-4c440c645eca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_wtX_xi
import Theorems.Thm_GeneralPieces_GenF_wtX_list_sum

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (a : List ℕ) : wtX (a.map fun n => Finsupp.single (xi rd n) 1).sum = a.sum := wtX_list_sum _ (wtX_xi rd) a
end GeneralPieces.GenF
