-- Prove2me | solution 1 for GeneralPieces.thmRunningTimeCm_tied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:40.984093+00:00
-- url     : https://prove2.me/submissions/fd028bb6-e181-44f2-8598-1c973f00e6dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Half_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Theorems.Thm_GeneralPieces_thmRunningTime_c_m_tied_at


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half
namespace GeneralPieces
theorem _root_.solution : Tied.ThmRunningTimeCm := fun _ _ _ _ _ _ h hx hc => thmRunningTime_c_m_tied_at h hx hc
end GeneralPieces
