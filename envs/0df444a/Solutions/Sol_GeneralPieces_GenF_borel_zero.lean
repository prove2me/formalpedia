-- Prove2me | solution 1 for GeneralPieces.GenF.borel_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:59:12.970105+00:00
-- url     : https://prove2.me/submissions/4236828c-a068-450e-bdc1-aeabed65b19e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
import Theorems.Thm_GeneralPieces_GenF_borel
import Theorems.Thm_GeneralPieces_GenF_fac_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
variable [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (L : List Y) (F : MvPowerSeries Y R) : fac (expo L) • coeff (expo L) F = constantCoeff (pdL L F) := by
  have h := borel L 0 F
  rwa [zero_add, fac_zero, one_smul, coeff_zero_eq_constantCoeff_apply] at h
end GeneralPieces.GenF
