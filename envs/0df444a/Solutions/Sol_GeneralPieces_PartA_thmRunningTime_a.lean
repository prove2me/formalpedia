-- Prove2me | solution 1 for GeneralPieces.PartA.thmRunningTime_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:37:46.764425+00:00
-- url     : https://prove2.me/submissions/6e187bd9-e49d-4ca7-b907-063f6bdc9cbf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_logK_formula
import Theorems.Thm_GeneralPieces_PartA_e_ge_half_pow
import Theorems.Thm_GeneralPieces_PartA_e_le_of_y
import Theorems.Thm_GeneralPieces_PartA_rho_pow_le

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (ρ : ℝ) (x₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) : TheoremAa ρ x₀ where
  logK := logK_formula x₀
  K_lt_le := fun l => K_lt_le x₀ l (by omega)
  e_bounds := fun l => ⟨e_ge_half_pow ρ x₀ l hρ, e_le_of_y ρ x₀ l hρ hx⟩
  rho_pow := fun l => rho_pow_le ρ x₀ l (by linarith) hρ1.le (by omega)
end GeneralPieces.PartA
