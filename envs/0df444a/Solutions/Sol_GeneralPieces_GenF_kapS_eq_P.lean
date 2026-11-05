-- Prove2me | solution 1 for GeneralPieces.GenF.kapS_eq_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:04:24.590565+00:00
-- url     : https://prove2.me/submissions/c0a78cd7-5946-408e-8ab4-61d03148b8e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_Series_kappa_sum


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) : kapS p q = (Gam p q : ℚ) • epsP ^ (p + q) := kappa_sum hp hq
end GeneralPieces.GenF
