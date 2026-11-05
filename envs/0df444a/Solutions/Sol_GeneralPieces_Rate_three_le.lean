-- Prove2me | solution 1 for GeneralPieces.Rate.three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:17.755461+00:00
-- url     : https://prove2.me/submissions/0760f7b2-d71d-4e4f-a876-f166d22a5588

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_ClauseBound_Gen_K_cast
import Theorems.Thm_ClauseBound_Gen_zeta_pos
import Theorems.Thm_GeneralPieces_PartAUse_e_nonneg
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hA : PartA.TheoremAa ρ x₀) (hρ : 0 ≤ ρ) (l : ℕ) : 3 ≤ e ρ x₀ (l + 1) * K x₀ l := by
  have hK : (0 : ℝ) < K x₀ l := by rw [K_cast]; positivity
  have h1 : 0 ≤ (ρ + 3 * zeta l) * e ρ x₀ l * K x₀ l :=
    mul_nonneg (mul_nonneg (by have := zeta_pos l; linarith) (PartAUse.e_nonneg hA hρ l)) hK.le
  have h2 : e ρ x₀ (l + 1) * K x₀ l = (ρ + 3 * zeta l) * e ρ x₀ l * K x₀ l + 3 := by rw [e]; field_simp
  linarith
end GeneralPieces.Rate
