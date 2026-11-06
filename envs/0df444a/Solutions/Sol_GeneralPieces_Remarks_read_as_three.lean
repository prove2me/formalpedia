-- Prove2me | solution 1 for GeneralPieces.Remarks.read_as_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:32.403308+00:00
-- url     : https://prove2.me/submissions/467dc2d8-ecb2-4072-b507-f1c584dc8f2a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Num_Remarks

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Remarks
open Finset Levels.Gen ClauseBound.Gen AppRunningTime
namespace GeneralPieces.Remarks
theorem _root_.solution {k n : ℕ} (φ : Sat3.CNF n) (hk : k ≤ 3) (h : SatK.IsKCNF k φ) : SatK.IsKCNF 3 φ :=
  ⟨fun C hC => le_trans (h.1 C hC) hk, h.2⟩
end GeneralPieces.Remarks
