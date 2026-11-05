-- Prove2me | solution 1 for GeneralPieces.Asymptotic.between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:37:48.703321+00:00
-- url     : https://prove2.me/submissions/5fd78a0f-2276-45d0-b2f9-158ff74441a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Theorems.Thm_GeneralPieces_PartA_e_ge_half_pow
import Theorems.Thm_GeneralPieces_PartA_e_le_of_y


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Asymptotic
open Levels.Gen ClauseBound.Gen GeneralPieces.PartA
namespace GeneralPieces.Asymptotic
theorem _root_.solution (ρ : ℝ) (x₀ l : ℕ) (t : ℝ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (h1 : 0.85 * ρ ^ l ≤ t) (h2 : t ≤ ρ ^ l) :
    e ρ x₀ l ≤ t ∧ t ≤ 2 * e ρ x₀ l :=
  ⟨le_trans (e_le_of_y ρ x₀ l hρ hx) h1, by linarith [e_ge_half_pow ρ x₀ l hρ]⟩
end GeneralPieces.Asymptotic
