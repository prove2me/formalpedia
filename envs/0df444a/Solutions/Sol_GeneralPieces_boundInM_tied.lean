-- Prove2me | solution 1 for GeneralPieces.boundInM_tied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:27:38.379715+00:00
-- url     : https://prove2.me/submissions/763d3198-61ed-44e7-bea2-2c7f273530eb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Half_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Theorems.Thm_GeneralPieces_thmRunningTime_c_m_tied


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half
namespace GeneralPieces
theorem _root_.solution (hB : AppRunningTime.ThmHalfPieces) : Tied.BoundInM := by
  obtain ⟨c, P, A', val, h, ht⟩ := hB
  exact ⟨c, P, A', val, ⟨h, ht⟩, thmRunningTime_c_m_tied h⟩
end GeneralPieces
