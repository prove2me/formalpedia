-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_add_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:28.896192+00:00
-- url     : https://prove2.me/submissions/ccb6d417-90db-4883-9241-5708c09d497e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
import Theorems.Thm_GeneralPieces_GenF_mul_natCast_succ


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (F : PS) (γ : X →₀ ℕ) (i : X) :
    MvPowerSeries.coeff (γ + Finsupp.single i 1) F = ((γ i : ℚ) + 1)⁻¹ • MvPowerSeries.coeff γ (MvPowerSeries.pderiv S i F) := by
  have h : ((γ i : ℚ) + 1) ≠ 0 := by positivity
  rw [MvPowerSeries.coeff_pderiv, mul_natCast_succ, smul_smul, inv_mul_cancel₀ h, one_smul]
end GeneralPieces.GenF
