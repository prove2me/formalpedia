-- Prove2me | solution 1 for GeneralPieces.Rate.size_cnt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:47.191979+00:00
-- url     : https://prove2.me/submissions/83a70611-f68a-486b-bc66-949a7c023f03

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_size_nPat_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_mul_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_nPat_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B cnt : ℕ) (hlam : 1 ≤ lam) :
    (Nat.size (cnt * nPat P (step P x₀ l) lam) : ℝ) ≤
      Nat.size cnt + (c * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + 1) := by
  have H1 : (Nat.size (cnt * nPat P (step P x₀ l) lam) : ℝ) ≤ Nat.size cnt + Nat.size (nPat P (step P x₀ l) lam) := by
    exact_mod_cast size_mul_le cnt _
  have H1r := size_nPat_le hP hx l lam B hlam
  linarith
end GeneralPieces.Rate
