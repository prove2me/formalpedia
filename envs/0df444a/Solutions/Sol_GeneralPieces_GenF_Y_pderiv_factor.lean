-- Prove2me | solution 1 for GeneralPieces.GenF.Y.pderiv_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:01:26.874498+00:00
-- url     : https://prove2.me/submissions/6affc4ea-f66a-429b-8c4d-0fd9936f6906

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_GeneralPieces_GenF_Y_pderiv_rat_smul
import Theorems.Thm_GeneralPieces_GenF_Y_C_rat_smul
import Theorems.Thm_GeneralPieces_GenF_Y_emb_rat_smul
import Theorems.Thm_GeneralPieces_GenF_Y_embW_lin
import Theorems.Thm_GeneralPieces_GenF_pderiv_lin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
open GeneralPieces.GenF.Y
namespace GeneralPieces.GenF.Y
theorem _root_.solution (rd : Bool) (i : X) (k : ℕ) : pderiv Tv i (C (tT k) + (k : ℚ) • embW (sfB' rd k)) = C (emb ((k : ℚ) • cB rd k i)) := by
  rw [map_add, pderiv_C, zero_add, pderiv_rat_smul (R := Tv), sfB', embW_lin, pderiv_lin, emb_rat_smul, C_rat_smul (R := Tv)]
  rfl
end GeneralPieces.GenF.Y
