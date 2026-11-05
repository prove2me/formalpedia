-- Prove2me | solution 1 for GeneralPieces.Rate.tab_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:51:38.528958+00:00
-- url     : https://prove2.me/submissions/d667036e-fdd6-4afa-95df-f2af69b9e963

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
theorem _root_.solution (k v r N c G4 L e' : ℝ) (hk : 1 ≤ k) (hv : k * v ≤ r * N + c / 4 * G4 * L + k ^ 2) (hr : r ≤ 2) (hc : 0 ≤ c)
    (h3 : 3 ≤ e' * k) (hN : 0 ≤ N) (hkG : k ≤ G4) (hL : 1 ≤ L) : v ≤ e' * N + (6 * c + 14) * G4 * L := by
  have hG0 : 0 ≤ G4 := by linarith
  have h1 : r * N ≤ e' * k * N := mul_le_mul_of_nonneg_right (by linarith) hN
  have hGL : G4 ≤ G4 * L := le_mul_of_one_le_right hG0 hL
  have hGL0 : 0 ≤ G4 * L := by linarith
  have hcGL : 0 ≤ c * (G4 * L) := mul_nonneg hc hGL0
  have h2 : 6 * (c * (G4 * L)) ≤ k * (6 * (c * (G4 * L))) := le_mul_of_one_le_left (by linarith) hk
  have h3 : k * k ≤ k * (G4 * L) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h4 : 0 ≤ k * (G4 * L) := mul_nonneg (by linarith) hGL0
  have h : k * v ≤ k * (e' * N + (6 * c + 14) * G4 * L) := by nlinarith
  exact le_of_mul_le_mul_left h (by linarith)
end GeneralPieces.Rate
