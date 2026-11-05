-- Prove2me | solution 1 for GeneralPieces.GenF.Y.embW_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:00:00.229046+00:00
-- url     : https://prove2.me/submissions/505d87c6-2534-4457-b6aa-c179094d0721

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_GeneralPieces_GenF_map_lin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
open GeneralPieces.GenF.Y
namespace GeneralPieces.GenF.Y
theorem _root_.solution (c : X → S) : embW (lin c) = lin fun i => emb (c i) := by
  have h := map_lin (Y := X) (A := S) (A' := Tv) emb c
  exact h
end GeneralPieces.GenF.Y
