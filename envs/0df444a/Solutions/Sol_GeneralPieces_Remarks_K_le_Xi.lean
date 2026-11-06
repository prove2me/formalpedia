-- Prove2me | solution 1 for GeneralPieces.Remarks.K_le_Xi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:46.104009+00:00
-- url     : https://prove2.me/submissions/8e2db8ca-44d8-4fde-a5e6-227aa4942f54

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
theorem _root_.solution (x₀ l lam B : ℕ) (hlam : 1 ≤ lam) : K x₀ l ≤ g x₀ l ^ 2 * (lam + B) := by
  have h1 : K x₀ l ≤ g x₀ l := by
    rw [g]; exact Nat.le_mul_of_pos_left _ (by positivity)
  calc K x₀ l ≤ g x₀ l := h1
    _ ≤ g x₀ l ^ 2 := Nat.le_self_pow (by norm_num) _
    _ ≤ g x₀ l ^ 2 * (lam + B) := Nat.le_mul_of_pos_right _ (by omega)
end GeneralPieces.Remarks
