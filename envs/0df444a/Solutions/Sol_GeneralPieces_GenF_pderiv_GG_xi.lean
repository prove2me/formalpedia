-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_GG_xi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:01:53.903191+00:00
-- url     : https://prove2.me/submissions/cb468dad-13bb-483d-bc89-3a03e58061bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Theorems.Thm_GeneralPieces_GenF_pderiv_prod
import Theorems.Thm_GeneralPieces_GenF_DD_xi
import Theorems.Thm_GeneralPieces_GenF_braW_C_JpU_mul
import Theorems.Thm_GeneralPieces_GenF_pderiv_braW
import Theorems.Thm_GeneralPieces_GenF_sel_xi


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) {n : ℕ} (hn : 1 ≤ n) {w : W} (hw : MvPowerSeries.pderiv Tv (xi rd n) w = 0) :
    MvPowerSeries.pderiv S (xi rd n) (GG rd E σ w) =
      ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo ((l : ℤ) - n) 0) * GG rd E (σ.erase l) w + GG rd E σ (mapD (JmT n) w) := by
  rw [GG, pderiv_braW, pderiv_prod, sel_xi rd _ _ hn, DD_xi rd hn, hw, map_zero, zero_add, braW_add, braW_C_JpU_mul hσ]
  rfl
end GeneralPieces.GenF
