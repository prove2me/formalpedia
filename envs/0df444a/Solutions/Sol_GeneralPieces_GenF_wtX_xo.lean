-- Prove2me | solution 1 for GeneralPieces.GenF.wtX_xo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:03:42.449103+00:00
-- url     : https://prove2.me/submissions/9c151c82-6e15-4f48-900e-be3c589a5c20

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
theorem _root_.solution (rd : Bool) (n : ℕ) : wtX (Finsupp.single (xo rd n) 1) = n := by
  rw [wtX_single, one_mul]
  cases rd <;> rfl
end GeneralPieces.GenF
