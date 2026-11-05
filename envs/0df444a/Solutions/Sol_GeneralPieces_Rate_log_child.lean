-- Prove2me | solution 1 for GeneralPieces.Rate.log_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:33.310904+00:00
-- url     : https://prove2.me/submissions/a0154680-8a3f-4c0e-8124-3c56d964e0e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_KLB_le
import Theorems.Thm_ClauseBound_Gen_Rate_X_cast
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_lamNext
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
    Real.logb 2 ((K x₀ l : ℝ) * ((lamNextG P (step P x₀ l) lam : ℝ) + (bNextG P (step P x₀ l) lam B : ℝ))) ≤
      (c + 5) * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) := by
  have h3 := big_le_K hx l
  have hn := KLB_le hP hm hx l lam B hlam
  have hpos : 0 < K x₀ l * (lamNextG P (step P x₀ l) lam + bNextG P (step P x₀ l) lam B) :=
    Nat.mul_pos (by omega) (by have := one_le_lamNext P (step P x₀ l) lam; omega)
  have hr : ((K x₀ l * (lamNextG P (step P x₀ l) lam + bNextG P (step P x₀ l) lam B) : ℕ) : ℝ) ≤
      (((g x₀ l ^ 2 * (lam + B)) ^ (c + 5) : ℕ) : ℝ) := by exact_mod_cast hn
  have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hpos) hr
  rw [Nat.cast_pow, Real.logb_pow, X_cast] at h5
  push_cast at h5
  exact h5
end GeneralPieces.Rate
