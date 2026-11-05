-- Prove2me | solution 1 for GeneralPieces.PartAUse.e_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:17:53.422608+00:00
-- url     : https://prove2.me/submissions/6d263a66-ab75-4c84-a10e-4434ebca64e4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (l : ℕ) : e ρ x₀ l ≤ 1 := by
  have h1 := (hA.e_bounds l).2
  have h2 : ρ ^ l ≤ 1 := pow_le_one₀ hρ hρ1
  linarith
end GeneralPieces.PartAUse
