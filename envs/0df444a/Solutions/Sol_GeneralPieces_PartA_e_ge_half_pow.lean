-- Prove2me | solution 1 for GeneralPieces.PartA.e_ge_half_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:36:23.644284+00:00
-- url     : https://prove2.me/submissions/72988c7b-9cab-4ac6-b314-3762a2eb5b9a

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
theorem _root_.solution (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) : 1 / 2 * ρ ^ l ≤ e ρ x₀ l := by
  have hρ0 : 0 < ρ := by linarith
  induction l with
  | zero => simp [e]
  | succ l ih =>
    have he : 0 ≤ e ρ x₀ l := le_trans (by positivity) ih
    have hz : 0 < zeta l := by unfold zeta; positivity
    have hK : (0 : ℝ) ≤ 3 / K x₀ l := by positivity
    have h1 : ρ * (1 / 2 * ρ ^ l) ≤ ρ * e ρ x₀ l := mul_le_mul_of_nonneg_left ih hρ0.le
    have h2 : 0 ≤ 3 * zeta l * e ρ x₀ l := by positivity
    rw [e, pow_succ]
    nlinarith
end GeneralPieces.PartA
