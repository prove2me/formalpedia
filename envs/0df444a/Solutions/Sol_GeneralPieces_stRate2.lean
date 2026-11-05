-- Prove2me | solution 1 for GeneralPieces.stRate2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:40:52.467341+00:00
-- url     : https://prove2.me/submissions/304c5516-1450-44b3-9079-d19d5a9a85aa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_main_le
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_log
import Theorems.Thm_ClauseBound_Gen_Rate_size_le_self
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
namespace GeneralPieces
theorem _root_.solution : StRate2 := by
  intro c
  refine ⟨6 * c + 17, fun P ρ x₀ hρ hρ1 hP hm hx hc l lam B hlam _ => ?_⟩
  have h := Rate.main_le hρ hρ1 hP hm hx hc l lam B 1 1 hlam
  have s1 : Nat.size 1 ≤ 1 := size_le_self 1
  have s2 : Nat.size (1 + Nat.size 1) ≤ 2 := (size_le_self _).trans (by omega)
  have s1' : (Nat.size 1 : ℝ) ≤ 1 := by exact_mod_cast s1
  have s2' : (Nat.size (1 + Nat.size 1) : ℝ) ≤ 2 := by exact_mod_cast s2
  have hL := one_le_log hx l lam B hlam
  have hk1 : (1 : ℝ) ≤ K x₀ l := by
    have := big_le_K hx l
    exact_mod_cast (by omega : 1 ≤ K x₀ l)
  have hk2 : (1 : ℝ) ≤ (K x₀ l : ℝ) ^ 2 := one_le_pow₀ hk1
  have h3 : (1 : ℝ) ≤ (K x₀ l : ℝ) ^ 2 * Real.logb 2 ((K x₀ l : ℝ) * (lam + B)) := by nlinarith
  unfold Bd at h
  push_cast
  linarith
end GeneralPieces
