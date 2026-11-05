-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_expW_kap_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:07:57.44352+00:00
-- url     : https://prove2.me/submissions/866d33da-770f-4600-aae5-ada5e9160a90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_coeff_kap_false
import Theorems.Thm_GeneralPieces_GenF_coeff_expW_of_weight


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (α : X →₀ ℕ) : coeff α (expW (kap false)) = gam α • epsP ^ wtX α := by
  rw [coeff_expW_of_weight wtX epsP kapQ coeff_kap_false, Algebra.smul_def, gam]
end GeneralPieces.GenF
