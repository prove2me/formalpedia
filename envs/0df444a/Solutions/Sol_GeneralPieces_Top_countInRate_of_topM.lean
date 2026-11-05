-- Prove2me | solution 1 for GeneralPieces.Top.countInRate_of_topM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:08:25.80167+00:00
-- url     : https://prove2.me/submissions/a29f6940-83c9-42b2-a8cb-03986d0b6c4f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_InOut
import Definitions.Def_GeneralPieces_Top_EndM

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Top
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat ClauseBound.Alg ClauseBound.Alg.End
namespace GeneralPieces.Top
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {r : ℕ → ℝ} (h : Tied.TopM S pick r) : SatM.CountInRate r :=
  let ⟨N, _, C, hfin, _, hc⟩ := h.machine
  ⟨N, C, hfin, hc⟩
end GeneralPieces.Top
