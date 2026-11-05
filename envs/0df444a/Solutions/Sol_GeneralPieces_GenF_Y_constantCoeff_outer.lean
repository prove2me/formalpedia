-- Prove2me | solution 1 for GeneralPieces.GenF.Y.constantCoeff_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:00:32.736704+00:00
-- url     : https://prove2.me/submissions/9558656b-58bb-493f-b12e-90bb4aeca9b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_expW
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_ket


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
open GeneralPieces.GenF.Y
namespace GeneralPieces.GenF.Y
theorem _root_.solution (rd : Bool) (σ' : Multiset ℕ) : constantCoeff (outer rd σ') = (σ'.map tT).prod := by
  rw [outer, map_mul, constantCoeff_expW (Bp rd), one_mul, constantCoeff_ket]
end GeneralPieces.GenF.Y
