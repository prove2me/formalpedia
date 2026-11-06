-- Prove2me | solution 1 for GeneralPieces.Remarks.K_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:24:03.243907+00:00
-- url     : https://prove2.me/submissions/b7ac5eed-e06f-4dbd-b918-667e4da465cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Num_Remarks
import Theorems.Thm_GeneralPieces_Remarks_K_le_Xi

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Remarks
open Finset Levels.Gen ClauseBound.Gen AppRunningTime
namespace GeneralPieces.Remarks
theorem _root_.solution (x₀ l lam B : ℕ) (hlam : 1 ≤ lam) : K x₀ l ^ g x₀ l ≤ (g x₀ l ^ 2 * (lam + B)) ^ g x₀ l :=
  Nat.pow_le_pow_left (K_le_Xi x₀ l lam B hlam) _
end GeneralPieces.Remarks
