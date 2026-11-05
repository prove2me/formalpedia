-- Prove2me | solution 1 for GeneralPieces.Rate.exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:44.967561+00:00
-- url     : https://prove2.me/submissions/f4d472f7-62a2-4058-baea-f2ba63c2ee38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_T_aux
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (e0 e' r N k2 G4 L c lam' lg : ℝ) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hre : r * e0 ≤ e') (hN : 0 ≤ N)
    (H3 : k2 * lam' ≤ r * N + c / 4 * G4 * L + k2) (H4 : lg ≤ (c + 5) * L) (H5 : 2 * ((c + 5) * k2) ≤ G4) (hL : 1 ≤ L)
    (hk2 : 0 ≤ k2) (hkG : k2 ≤ G4) (hG : 1 ≤ G4) (hc : 0 ≤ c) :
    (c * G4 * L + 1) + (1 + ((c + 3) * L + 1)) + (e0 * k2 * lam' + (6 * c + 14) * k2 * lg) ≤ e' * N + (6 * c + 14) * G4 * L := by
  have a1 := T_aux e0 r N k2 G4 L c lam' lg (6 * c + 14) he0 he1 H3 H4 hL hk2 (by linarith) hc (by linarith)
  have a3 : r * e0 * N ≤ e' * N := mul_le_mul_of_nonneg_right hre hN
  have a2 : k2 * L ≤ G4 * L := mul_le_mul_of_nonneg_right hkG (by linarith)
  have a5 : 2 * ((c + 5) * k2) * ((3 * c + 7) * L) ≤ G4 * ((3 * c + 7) * L) := mul_le_mul_of_nonneg_right H5 (by positivity)
  have hGL : L ≤ G4 * L := le_mul_of_one_le_left (by linarith) hG
  have hGL' : G4 ≤ G4 * L := le_mul_of_one_le_right (by linarith) hL
  have a6 : (c + 3) * L ≤ (c + 3) * (G4 * L) := mul_le_mul_of_nonneg_left hGL (by linarith)
  have a7 : 0 ≤ c * (G4 * L) := mul_nonneg hc (by linarith)
  nlinarith
end GeneralPieces.Rate
