-- Prove2me | solution 1 for GeneralPieces.thmHalfPieces_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:53:15.069588+00:00
-- url     : https://prove2.me/submissions/39a5c7ef-0fc0-4005-a1b4-fc3648adca76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Half_Main
import Definitions.Def_GeneralPieces_Tied_Bound

set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half
namespace GeneralPieces
theorem _root_.solution : AppRunningTime.ThmHalfPieces ↔ ∃ c P A val, Tied.IsPiecesB c P A val := Iff.rfl
end GeneralPieces
