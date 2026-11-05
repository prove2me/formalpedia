-- Prove2me | solution 1 for GeneralPieces.Rate.size_nPat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:26.404532+00:00
-- url     : https://prove2.me/submissions/fe2a45ca-a20a-4bc0-a13a-c8ae6a2e6f5a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_nPat_le_quarter
import Theorems.Thm_ClauseBound_Gen_Rate_X_cast
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_log
import Theorems.Thm_ClauseBound_Gen_Rate_size_cast_le
import Theorems.Thm_ClauseBound_Gen_Rate_two_lam_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    (Nat.size (nPat P (step P x₀ l) lam) : ℝ) ≤ c * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + 1 := by
  have hX1 : 1 ≤ g x₀ l ^ 2 * (lam + B) := by have := two_lam_le hx l lam B; omega
  have h := size_cast_le hX1 (nPat_le_quarter hP hx l lam B hlam)
  rw [X_cast] at h
  have hL := one_le_log hx (l + 1) lam B hlam
  have hR : ((c * (g x₀ l ^ 4 / 4) : ℕ) : ℝ) ≤ c * (g x₀ l : ℝ) ^ 4 := by
    exact_mod_cast Nat.mul_le_mul_left c (Nat.div_le_self (g x₀ l ^ 4) 4)
  have := mul_le_mul_of_nonneg_right hR (by linarith : 0 ≤ Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)))
  linarith
end GeneralPieces.Rate
