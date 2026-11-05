-- Prove2me | solution 1 for GeneralPieces.GenF.map_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:36:13.236795+00:00
-- url     : https://prove2.me/submissions/e23d7ec2-9535-46da-8f4b-cee0efb143ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_coeff_lin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {Y A : Type} [CommRing A]
namespace GeneralPieces.GenF
theorem _root_.solution {A' : Type} [CommRing A'] (φ : A →+* A') (c : Y → A) : MvPowerSeries.map φ (lin c) = lin fun i => φ (c i) := by
  ext α
  rw [MvPowerSeries.coeff_map, coeff_lin, coeff_lin]
  split_ifs
  · rw [map_sum]
  · rw [map_zero]
end GeneralPieces.GenF
