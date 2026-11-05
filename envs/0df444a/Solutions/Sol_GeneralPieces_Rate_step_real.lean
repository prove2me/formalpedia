-- Prove2me | solution 1 for GeneralPieces.Rate.step_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:41.377872+00:00
-- url     : https://prove2.me/submissions/76474cf4-8a52-49dc-96f9-d342442d64d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_le_of_K_mul
import Theorems.Thm_GeneralPieces_Rate_tab_aux
import Theorems.Thm_GeneralPieces_Rate_exponent_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (nd sz' sc' sP lg L vt vs vg lam' sc sz vn e' e0 r k G4 lm cc : ℝ)
    (hIH : nd ≤ sc' + sz' + (e0 * k ^ 2 * lam' + (6 * cc + 14) * k ^ 2 * lg))
    (H1 : sc' ≤ sc + (cc * G4 * L + 1)) (HP : sP ≤ cc * G4 * L + 1) (H2 : sz' ≤ sz + 1 + ((cc + 3) * L + 1))
    (H3 : k ^ 2 * lam' ≤ r * (G4 * lm) + cc / 4 * G4 * L + k ^ 2) (H4 : lg ≤ (cc + 5) * L) (H5 : 2 * ((cc + 5) * k ^ 2) ≤ G4)
    (hk1 : 1 ≤ k) (hkG : k ≤ G4) (hc0 : 0 ≤ cc) (hlm : 1 ≤ lm) (hL1 : 1 ≤ L) (h3 : 3 ≤ e' * k)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (he'0 : 0 ≤ e') (hre : r * e0 ≤ e') (hr2 : r ≤ 2) (hneed : k * vn ≤ G4 * lm) (hgK : vg ≤ G4)
    (hst : k * vs ≤ 3 * (G4 * lm)) (htab : vt ≤ k * lam') (p1 : 0 ≤ sc) (p2 : 0 ≤ sz) :
    max (max (max vn sP) (max vg vs)) (max (max vt 0) nd) ≤ sc + sz + (e' * (G4 * lm) + (6 * cc + 14) * G4 * L) := by
  have hG1 : 1 ≤ G4 := hk1.trans hkG
  have hk2 : 0 ≤ k ^ 2 := by positivity
  have hk2G : k ^ 2 ≤ G4 := by
    have : 0 ≤ cc * k ^ 2 := mul_nonneg hc0 hk2
    linarith
  have hN : 0 ≤ G4 * lm := mul_nonneg (by linarith) (by linarith)
  have heN : 0 ≤ e' * (G4 * lm) := mul_nonneg he'0 hN
  have hGL : G4 ≤ G4 * L := le_mul_of_one_le_right (by linarith) hL1
  have hcGL : 0 ≤ cc * (G4 * L) := mul_nonneg hc0 (by linarith)
  have hT : (6 * cc + 14) * G4 * L = 6 * (cc * (G4 * L)) + 14 * (G4 * L) := by ring
  have hcc : cc * G4 * L = cc * (G4 * L) := by ring
  have b2 : vn ≤ e' * (G4 * lm) := le_of_K_mul k vn (G4 * lm) e' (by linarith) h3 hN (by linarith)
  have b5 : vs ≤ e' * (G4 * lm) := le_of_K_mul k vs (G4 * lm) e' (by linarith) h3 hN hst
  have b6 : vt ≤ e' * (G4 * lm) + (6 * cc + 14) * G4 * L := by
    apply tab_aux k vt r (G4 * lm) cc G4 L e' hk1 _ hr2 hc0 h3 hN hkG hL1
    calc k * vt ≤ k * (k * lam') := mul_le_mul_of_nonneg_left htab (by linarith)
      _ = k ^ 2 * lam' := by ring
      _ ≤ _ := H3
  have b8 := exponent_le e0 e' r (G4 * lm) (k ^ 2) G4 L cc lam' lg he0 he1 hre hN H3 H4 H5 hL1 hk2 hk2G hG1 hc0
  rw [hT] at b6 b8 ⊢
  rw [hcc] at H1 HP b8
  refine max_le (max_le (max_le ?_ ?_) (max_le ?_ ?_)) (max_le (max_le ?_ ?_) ?_) <;> linarith
end GeneralPieces.Rate
