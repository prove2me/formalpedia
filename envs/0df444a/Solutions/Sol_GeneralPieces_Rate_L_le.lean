-- Prove2me | solution 1 for GeneralPieces.Rate.L_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:41.509044+00:00
-- url     : https://prove2.me/submissions/d4cea156-00c6-4e45-ab3e-0646b884fb27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_capSum_le_four
import Theorems.Thm_GeneralPieces_Rate_L_aux
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_four_nRect_le
import Theorems.Thm_ClauseBound_Gen_Rate_lamNext_eq
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam : ℕ) (hlam : 1 ≤ lam) :
    lamNextG P (step P x₀ l) lam ≤ g x₀ l ^ 4 * lam + 1 := by
  rw [lamNext_eq, hm]
  have hK := big_le_K hx l
  have hg : 1 ≤ g x₀ l := le_trans (by omega) (K_le_g x₀ l)
  refine Nat.add_le_add_right (L_aux _ _ _ _ _ _ _ ?_ (by omega) ?_ (four_nRect_le _) (capSum_le_four hP hm lam hlam)) 1
  · have : 1 ≤ 2 ^ (l + 4) := Nat.one_le_two_pow
    omega
  · calc g x₀ l * (g x₀ l - 1) * g x₀ l * lam ≤ g x₀ l * g x₀ l * g x₀ l * lam := by gcongr; exact Nat.sub_le _ _
      _ = 1 * g x₀ l ^ 3 * lam := by ring
      _ ≤ g x₀ l * g x₀ l ^ 3 * lam := by gcongr
      _ = g x₀ l ^ 4 * lam := by ring
end GeneralPieces.Rate
