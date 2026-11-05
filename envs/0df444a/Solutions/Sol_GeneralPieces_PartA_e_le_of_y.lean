-- Prove2me | solution 1 for GeneralPieces.PartA.e_le_of_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:35:45.232956+00:00
-- url     : https://prove2.me/submissions/0624dae3-e18a-4d43-aa9d-68c619f17d3f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_y_lt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) : e ρ x₀ l ≤ 0.85 * ρ ^ l := by
  have hr : 0 < ρ ^ l := by have : 0 < ρ := by linarith
                            positivity
  have h := (y_lt ρ x₀ l hρ hx).le
  rwa [y, div_le_iff₀ hr] at h
end GeneralPieces.PartA
