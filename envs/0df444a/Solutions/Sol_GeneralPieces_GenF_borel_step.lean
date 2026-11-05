-- Prove2me | solution 1 for GeneralPieces.GenF.borel_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:47:36.016637+00:00
-- url     : https://prove2.me/submissions/51a007b0-ae8b-4b8a-b146-e89354d0b5c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
import Theorems.Thm_GeneralPieces_GenF_fac_add_single
import Theorems.Thm_GeneralPieces_GenF_mul_natCast_succ


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
variable [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (β : Y →₀ ℕ) (i : Y) (F : MvPowerSeries Y R) :
    fac (β + Finsupp.single i 1) • coeff (β + Finsupp.single i 1) F = fac β • coeff β (pderiv R i F) := by
  rw [coeff_pderiv, mul_natCast_succ, fac_add_single, smul_smul, mul_comm]
end GeneralPieces.GenF
