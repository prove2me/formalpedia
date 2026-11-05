-- Prove2me | solution 1 for GeneralPieces.GenF.constantCoeff_GG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:02:06.30464+00:00
-- url     : https://prove2.me/submissions/ca9fae17-3071-4f0a-93bf-89437c8e8fe5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_braW
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_expD
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_expW


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (w : W) : MvPowerSeries.constantCoeff (GG rd E σ w) = bra σ (MvPowerSeries.constantCoeff w) := by
  rw [GG, constantCoeff_braW, map_mul, constantCoeff_expW (Ap rd E), one_mul, Phi, constantCoeff_expD (DD rd) w]
end GeneralPieces.GenF
