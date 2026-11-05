-- Prove2me | solution 1 for GeneralPieces.GenF.Normal.mapD_embW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:58:29.090505+00:00
-- url     : https://prove2.me/submissions/53ad414b-9ebb-4b28-a6b5-639877c2610f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_Normal_DD_emb
import Theorems.Thm_GeneralPieces_GenF_coeff_mapD


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
namespace Normal
theorem _root_.solution (rd : Bool) (i : X) (e : PS) : mapD (DD rd i) (embW e) = 0 := by
  ext1 α
  refine (coeff_mapD (DD rd i) (embW e) α).trans ?_
  rw [embW, MvPowerSeries.coeff_map, Normal.DD_emb, map_zero]
end Normal
end GeneralPieces.GenF
