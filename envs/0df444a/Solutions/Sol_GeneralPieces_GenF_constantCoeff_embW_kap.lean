-- Prove2me | solution 1 for GeneralPieces.GenF.constantCoeff_embW_kap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:52:37.043227+00:00
-- url     : https://prove2.me/submissions/27dfa1a2-e2cc-40b0-bd46-73cddf7c5982

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
import Theorems.Thm_GeneralPieces_GenF_kap_eq
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_bil


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) : constantCoeff (embW (kap rd)) = 0 := by
  rw [embW, constantCoeff_map, kap_eq, constantCoeff_bil, map_zero]
end GeneralPieces.GenF
