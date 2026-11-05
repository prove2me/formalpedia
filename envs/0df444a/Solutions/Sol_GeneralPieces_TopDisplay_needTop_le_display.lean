-- Prove2me | solution 1 for GeneralPieces.TopDisplay.needTop_le_display
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:12.144202+00:00
-- url     : https://prove2.me/submissions/cce89de3-245f-4df7-b156-364f54e709e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_nine_le_log
import Theorems.Thm_GeneralPieces_TopDisplay_solver_terms_le
import Theorems.Thm_ClauseBound_Alg_TopArith_P_mul_le
import Theorems.Thm_ClauseBound_Alg_TopArith_one_le_B
import Theorems.Thm_ClauseBound_Alg_TopArith_one_le_lam
import Theorems.Thm_ClauseBound_Alg_TopArith_size_le_two_logb
import Theorems.Thm_ClauseBound_Alg_TopArith_sq_mul_lam_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hm : S.K i ^ 9 ≤ m)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ 2 * e * k * m + (2 * C₀ + 15 : ℕ) *
      ((k : ℝ) * m / S.K i + (S.K i : ℝ) ^ 8 * Real.logb 2 (S.K i) + (S.K i : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) := by
  unfold needTop
  have hr := hrate _ _ (one_le_lam (k := k) (m := m) hK) (one_le_B (k := k) (m := m) hK)
  generalize S.need (i, List.replicate (lamTopK (S.K i) (3 * S.K i ^ 8) k m) (),
    List.replicate (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i)) ()) = N at hr ⊢
  clear hrate
  generalize S.K i = K at *
  have hκ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h9 := nine_le_log hK hk hm
  have h1 := solver_terms_le e C₀ he0 he1 hK hk hm
  have p0 : 0 ≤ 2 * e * k * m := by positivity
  have p1 : 0 ≤ (k : ℝ) * m / K := by positivity
  have p2 : 0 ≤ (K : ℝ) ^ 8 * Real.logb 2 K :=
    mul_nonneg (by positivity) (Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ K)))
  have p3 : 0 ≤ (K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m) := mul_nonneg (by positivity) (by linarith)
  have hC : (0 : ℝ) ≤ C₀ := by positivity
  have T1 : ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 6 * ((K : ℝ) ^ 8 * Real.logb 2 K) := by
    push_cast
    have := size_le_two_logb K hK
    have h8 : (0 : ℝ) ≤ 3 * (K : ℝ) ^ 8 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h8]
  have T2 : ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ 15 * ((k : ℝ) * m / K) := by
    rw [← mul_div_assoc, le_div_iff₀ hκ]
    exact_mod_cast P_mul_le hK hk hm
  have T3 : (((K - 1) * lamTopK K (3 * K ^ 8) k m : ℕ) : ℝ) ≤ 8 * ((k : ℝ) * m / K) := by
    rw [← mul_div_assoc, le_div_iff₀ hκ]
    have : (K - 1) * lamTopK K (3 * K ^ 8) k m * K ≤ 8 * (k * m) :=
      calc (K - 1) * lamTopK K (3 * K ^ 8) k m * K ≤ K * lamTopK K (3 * K ^ 8) k m * K :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
        _ = K ^ 2 * lamTopK K (3 * K ^ 8) k m := by ring
        _ ≤ 8 * (k * m) := sq_mul_lam_le hK hk hm
    exact_mod_cast this
  have T4 := le_trans hr h1
  have q1 := mul_nonneg hC p1
  have q2 := mul_nonneg hC p2
  have q3 := mul_nonneg hC p3
  have hA : ((2 * C₀ + 15 : ℕ) : ℝ) = 2 * C₀ + 15 := by push_cast; ring
  rw [Nat.cast_max, Nat.cast_max, Nat.cast_max, hA]
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> nlinarith
end GeneralPieces.TopDisplay
