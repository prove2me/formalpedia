-- Prove2me | solution 1 for GeneralPieces.Level.Lof_le_lamNext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:38.348931+00:00
-- url     : https://prove2.me/submissions/f02a8a9e-1b86-4a1b-a835-956c16252414

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level
import Theorems.Thm_ClauseBound_Alg_Level_le_mul_div_succ
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Level
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset
namespace GeneralPieces.Level
theorem _root_.solution {P : PiecesF} {s : Step} {lam : ℕ} (hL : LevelOK2 P s lam) (Uv : ℕ) (hU : Uv ≤ ubarG P s lam) :
    AppRunningTime.Lof s.K s.p (zetaOf s) (P.m * (s.p * s.d ^ 2 * lam)) Uv ≤ lamNextG P s lam := by
  have hD0 : 0 < s.D * s.K ^ 2 := by
    have h1 := hL.D_ge
    have h2 := hL.two_le
    positivity
  have hβ : s.D * Uv + 3 * s.p ^ 2 * (s.d ^ 2 * (P.m * lam)) ≤ s.D * s.K ^ 2 * lamNextG P s lam :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hU) _).trans (le_mul_div_succ _ hD0)
  have hβr : (s.D : ℝ) * Uv + 3 * (s.p : ℝ) ^ 2 * ((s.d : ℝ) ^ 2 * (P.m * lam)) ≤ s.D * (s.K : ℝ) ^ 2 * lamNextG P s lam := by exact_mod_cast hβ
  have hDr : (0 : ℝ) < s.D := by exact_mod_cast (by have := hL.D_ge; omega : 0 < s.D)
  have hKr : (0 : ℝ) < s.K := by exact_mod_cast (by have := hL.two_le; omega : 0 < s.K)
  unfold AppRunningTime.Lof zetaOf
  rw [Nat.ceil_le, div_le_iff₀ (by positivity)]
  push_cast
  have e3 : (s.D : ℝ) * ((Uv : ℝ) + 2 * (3 / (2 * (s.D : ℝ))) * s.p * (P.m * (s.p * (s.d : ℝ) ^ 2 * lam))) =
      s.D * Uv + 3 * (s.p : ℝ) ^ 2 * ((s.d : ℝ) ^ 2 * (P.m * lam)) := by field_simp
  refine le_of_mul_le_mul_left ?_ hDr
  rw [e3]
  linarith
end GeneralPieces.Level
