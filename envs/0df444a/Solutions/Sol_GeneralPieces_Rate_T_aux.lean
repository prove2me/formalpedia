-- Prove2me | solution 1 for GeneralPieces.Rate.T_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:16.738195+00:00
-- url     : https://prove2.me/submissions/2ea40367-e04f-452d-9b4f-33f3c229e323

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (e0 r N k2 G4 L c lam' lg C : ℝ) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1)
    (H3 : k2 * lam' ≤ r * N + c / 4 * G4 * L + k2) (H4 : lg ≤ (c + 5) * L) (hL : 1 ≤ L) (hk2 : 0 ≤ k2) (hG : 0 ≤ G4) (hc : 0 ≤ c) (hC : 0 ≤ C) :
    e0 * k2 * lam' + C * k2 * lg ≤ e0 * r * N + (c / 4 * G4 + k2 + (c + 5) * C * k2) * L := by
  have a1 : e0 * (k2 * lam') ≤ e0 * (r * N + c / 4 * G4 * L + k2) := mul_le_mul_of_nonneg_left H3 he0
  have a2 : e0 * (c / 4 * G4 * L + k2) ≤ c / 4 * G4 * L + k2 := mul_le_of_le_one_left (by positivity) he1
  have a4 : C * k2 * lg ≤ C * k2 * ((c + 5) * L) := mul_le_mul_of_nonneg_left H4 (by positivity)
  have a5 : k2 ≤ k2 * L := le_mul_of_one_le_right hk2 hL
  nlinarith
end GeneralPieces.Rate
