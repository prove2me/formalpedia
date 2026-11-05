-- Prove2me | solution 1 for GeneralPieces.GenF.Y.emb_rat_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:38:50.178271+00:00
-- url     : https://prove2.me/submissions/2cd303a2-e978-4bbf-9b3f-7ac857d70915

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
open GeneralPieces.GenF.Y
namespace GeneralPieces.GenF.Y
theorem _root_.solution (q : ℚ) (s : S) : emb (q • s) = q • emb s := by
  have h := map_rat_smul emb.toAddMonoidHom q s
  exact h
end GeneralPieces.GenF.Y
