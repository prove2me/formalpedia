-- Prove2me | solution 1 for GeneralPieces.GenF.z0_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:39:12.101457+00:00
-- url     : https://prove2.me/submissions/9ba10185-2724-488a-803d-656c43f7086b

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
theorem _root_.solution {R : Type} [Zero R] (f : ℕ → R) {n : ℕ} (hn : 1 ≤ n) : z0 f n = f n := if_neg (by omega)
end GeneralPieces.GenF
