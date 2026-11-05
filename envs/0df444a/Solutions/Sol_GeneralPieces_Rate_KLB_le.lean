-- Prove2me | solution 1 for GeneralPieces.Rate.KLB_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:40.338902+00:00
-- url     : https://prove2.me/submissions/9db5a50c-3853-4e14-8fc7-b3f1718055ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_L_le
import Theorems.Thm_P2M_GeneralPieces_Rate_B__le_18a470b66aae
import Theorems.Thm_GeneralPieces_Rate_crude_aux
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    K x₀ l * (lamNextG P (step P x₀ l) lam + bNextG P (step P x₀ l) lam B) ≤ (g x₀ l ^ 2 * (lam + B)) ^ (c + 5) := by
  have hK := big_le_K hx l
  have hg := K_le_g x₀ l
  exact (crude_aux (K x₀ l) (g x₀ l) c lam B _ _ hlam hg (by omega) (L_le hP hm hx l lam hlam) (B'_le hP hm hx l lam B hlam)).2
end GeneralPieces.Rate
