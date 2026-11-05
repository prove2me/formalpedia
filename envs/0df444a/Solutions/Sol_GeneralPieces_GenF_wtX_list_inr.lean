-- Prove2me | solution 1 for GeneralPieces.GenF.wtX_list_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:04.170683+00:00
-- url     : https://prove2.me/submissions/f5f7f248-1737-4a38-a648-99709e31ac7a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_wtX_list_xo

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (a : List ℕ) : wtX (a.map fun n => Finsupp.single (Sum.inr n : X) 1).sum = a.sum := wtX_list_xo false a
end GeneralPieces.GenF
