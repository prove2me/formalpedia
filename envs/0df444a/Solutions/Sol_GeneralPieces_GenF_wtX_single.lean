-- Prove2me | solution 1 for GeneralPieces.GenF.wtX_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:27:39.408446+00:00
-- url     : https://prove2.me/submissions/efc6aecb-4602-411a-b28d-73a9d3e042a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (i : X) (m : ℕ) : wtX (Finsupp.single i m) = m * Sum.elim id id i := by
  rw [wtX, Finsupp.weight_single, smul_eq_mul]
end GeneralPieces.GenF
