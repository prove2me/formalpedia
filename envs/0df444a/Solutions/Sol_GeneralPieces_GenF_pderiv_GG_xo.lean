-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_GG_xo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:03:01.520666+00:00
-- url     : https://prove2.me/submissions/296d0a62-8100-4511-a6d4-72acf291a678

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Theorems.Thm_GeneralPieces_GenF_mapD_zero
import Theorems.Thm_GeneralPieces_GenF_pderiv_prod
import Theorems.Thm_GeneralPieces_GenF_DD_xo
import Theorems.Thm_GeneralPieces_GenF_pderiv_braW
import Theorems.Thm_P2M_GeneralPieces_GenF_sel_xo__1f77a7ff0981


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (n : ℕ) (w : W) :
    MvPowerSeries.pderiv S (xo rd n) (GG rd E σ w) = GG rd E σ (MvPowerSeries.pderiv Tv (xo rd n) w) := by
  have h : (sel rd (fun n => (HahnSeries.C (JpU E n) : Tv)) 0 (xo rd n) : Tv) = 0 := by
    rw [sel_xo']
    unfold z0
    split_ifs <;> rfl
  rw [GG, pderiv_braW, pderiv_prod, h, DD_xo, mapD_zero, map_zero, map_zero, zero_mul, zero_add, add_zero]
  rfl
end GeneralPieces.GenF
