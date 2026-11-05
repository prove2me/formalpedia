-- Prove2me | solution 1 for GeneralPieces.PartA.exp_half_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:58:18.677315+00:00
-- url     : https://prove2.me/submissions/c259c517-163d-4831-9f9c-9365d82d6f35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution : Real.exp (1 / 2) * 0.51 < 0.85 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have h4 : Real.exp (1 / 2) < 1.66 := by
    by_contra hc
    have hc' : 1.66 ≤ Real.exp (1 / 2) := not_lt.mp hc
    nlinarith
  linarith
end GeneralPieces.PartA
