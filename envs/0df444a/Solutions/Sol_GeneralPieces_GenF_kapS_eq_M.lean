-- Prove2me | solution 1 for GeneralPieces.GenF.kapS_eq_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:05:06.564424+00:00
-- url     : https://prove2.me/submissions/507d41c1-a871-48f0-93e2-cca62aefee01

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_Series_ser_congr
import Theorems.Thm_P2M_GeneralPieces_Series_kappa__sum_5bc6c6120ed7


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) : kapS p q = (Gam q p : ℚ) • epsM ^ (q + p) := by
  rw [← kappa'_sum hq hp, kapS, sumP, sumM]
  exact ser_congr _ _ fun k => by ring
end GeneralPieces.GenF
