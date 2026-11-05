-- Prove2me | solution 1 for GeneralPieces.GenF.wtX_xi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:03:21.931864+00:00
-- url     : https://prove2.me/submissions/fa1e17a2-d1ab-4a17-8414-58d0eb44c04a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_wtX_single

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (n : ℕ) : wtX (Finsupp.single (xi rd n) 1) = n := by
  rw [wtX_single, one_mul]
  cases rd <;> rfl
end GeneralPieces.GenF
