-- Prove2me | solution 1 for GeneralPieces.TopDisplay.solver_terms_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:55.213814+00:00
-- url     : https://prove2.me/submissions/3dcc53b4-e233-4da0-afca-9e01c4ca3845

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_sq_L_le
import Theorems.Thm_GeneralPieces_TopDisplay_arg_le_km
import Theorems.Thm_GeneralPieces_TopDisplay_nine_le_log
import Theorems.Thm_ClauseBound_Alg_TopArith_g_mul_P_le
import Theorems.Thm_ClauseBound_Alg_TopArith_one_le_lam


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
variable {K k m : ℕ}
namespace GeneralPieces.TopDisplay
theorem _root_.solution (e : ℝ) (C₀ : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    e * (K : ℝ) ^ 2 * lamTopK K (3 * K ^ 8) k m +
      C₀ * (K : ℝ) ^ 2 * Real.logb 2 (K * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ))) ≤
    2 * e * k * m + 5 * ((k : ℝ) * m / K) + (2 * C₀ + 1) * ((K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) := by
  have hκ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h9 := nine_le_log hK hk hm
  have hL := sq_L_le (k := k) (m := m) hK
  have hG : ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) ≤ 5 * ((k : ℝ) * m) := by exact_mod_cast g_mul_P_le hK hk hm
  have hG' : ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) / K ≤ 5 * ((k : ℝ) * m / K) := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hG hκ.le
  have hkm : (0 : ℝ) < (k : ℝ) * m := by
    have : 0 < k * m := Nat.mul_pos hk (lt_of_lt_of_le (by positivity) hm)
    exact_mod_cast this
  -- the argument of the logarithm
  have harg : (K : ℝ) * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ)) ≤ 2 ^ 5 * ((k : ℝ) * m) := by
    have := arg_le_km hK hk hm
    exact_mod_cast this
  have hpos : 0 < (K : ℝ) * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ lamTopK K (3 * K ^ 8) k m := by exact_mod_cast one_le_lam (k := k) (m := m) hK
    positivity
  have hlog : Real.logb 2 (K * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ))) ≤
      2 * Real.logb 2 ((k : ℝ) * m) := by
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos harg
    have e5 : Real.logb 2 (2 ^ 5 * ((k : ℝ) * m)) = 5 + Real.logb 2 ((k : ℝ) * m) := by
      rw [Real.logb_mul (by positivity) hkm.ne', Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
    rw [e5] at h1
    linarith
  generalize Real.logb 2 (K * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ))) = X at hlog ⊢
  generalize ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) / K = G at hL hG'
  generalize (lamTopK K (3 * K ^ 8) k m : ℝ) = L at hL ⊢
  generalize Real.logb 2 ((k : ℝ) * m) = Y at h9 hlog ⊢
  have hq : 0 ≤ (k : ℝ) * m / K := by positivity
  generalize (k : ℝ) * m / K = q at hG' hq ⊢
  have hκ2 : 0 < (K : ℝ) ^ 2 := by positivity
  generalize (K : ℝ) ^ 2 = κ2 at hL hκ2 ⊢
  have hG0 : κ2 * L - 2 * k * m ≤ κ2 + 5 * q := by linarith
  have a1 : e * κ2 * L ≤ 2 * e * k * m + (κ2 + 5 * q) := by
    have h0 : 0 ≤ κ2 + 5 * q := by positivity
    have : e * (κ2 * L - 2 * k * m) ≤ 1 * (κ2 + 5 * q) := by
      rcases le_total 0 (κ2 * L - 2 * k * m) with hs | hs
      · exact mul_le_mul he1 hG0 hs (by norm_num)
      · have : e * (κ2 * L - 2 * k * m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he0 hs
        linarith
    linarith
  have a2 : (C₀ : ℝ) * κ2 * X ≤ C₀ * κ2 * (2 * Y) := mul_le_mul_of_nonneg_left hlog (by positivity)
  have a3 : κ2 * 1 ≤ κ2 * Y := mul_le_mul_of_nonneg_left (by linarith) hκ2.le
  nlinarith
end GeneralPieces.TopDisplay
