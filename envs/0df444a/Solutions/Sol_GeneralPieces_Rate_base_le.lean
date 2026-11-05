-- Prove2me | solution 1 for GeneralPieces.Rate.base_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:14.908693+00:00
-- url     : https://prove2.me/submissions/e509c794-a2b6-4b67-bfd8-0cbef0778ab4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_brute_le
import Theorems.Thm_GeneralPieces_Rate_first_le
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_log
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (needG P (K x₀ 0) lam B cnt z (sched P x₀ 0) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ 0 lam B := by
  have hfirst := first_le (ρ := ρ) (c := c) hρ hρ1 hx 0 lam B cnt z hlam
  rw [show sched P x₀ 0 = [] from rfl, needG, Nat.cast_max]
  refine max_le hfirst ?_
  have hL1 := one_le_log hx 0 lam B hlam
  have h2 := brute_le ρ x₀ lam
  have p1 : (0 : ℝ) ≤ Nat.size cnt := by positivity
  have p2 : (0 : ℝ) ≤ Nat.size (z + Nat.size cnt) := by positivity
  have p3 : 0 ≤ (6 * (c : ℝ) + 14) * (K x₀ 0 : ℝ) ^ 2 * Real.logb 2 ((K x₀ 0 : ℝ) * (lam + B)) := by
    have : 0 ≤ Real.logb 2 ((K x₀ 0 : ℝ) * (lam + B)) := by linarith
    positivity
  unfold Bd
  linarith
end GeneralPieces.Rate
