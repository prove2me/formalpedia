-- Prove2me | solution 1 for GeneralPieces.TopDisplay.terms_le_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:15:17.165203+00:00
-- url     : https://prove2.me/submissions/2fe041ab-f198-4eec-b129-e3e332b4fd60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_logb_le_two_mul
import Theorems.Thm_GeneralPieces_TopDisplay_root_pow
import Theorems.Thm_GeneralPieces_TopDisplay_root_pow_pred
import Theorems.Thm_GeneralPieces_TopDisplay_root_le
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (K k m d : ℕ) (hK : 2 ≤ K) (hk : 1 ≤ k) (hd : 2 ≤ d) (hm : K ^ 9 ≤ m) (hm' : m ≤ K ^ (9 * d)) :
    (k : ℝ) * m / K ≤ k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)) ∧
    (K : ℝ) ^ 8 * Real.logb 2 K ≤ 2 * d * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ))) ∧
    (K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m) ≤ (2 + 18 * d) * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ))) := by
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_pow _ _ (by omega)) hm
  have ht1 : 1 ≤ (m : ℝ) ^ (1 / (9 * d : ℝ)) := Real.one_le_rpow (by exact_mod_cast hm1) (by positivity)
  have htK := root_le K m d (by omega) hm'
  have h90 := root_pow m d (by omega)
  rw [root_pow_pred m d (by omega)]
  have hK9 : (K : ℝ) ^ 9 ≤ m := by exact_mod_cast hm
  generalize (m : ℝ) ^ (1 / (9 * d : ℝ)) = t at *
  rw [← h90] at hK9 ⊢
  have hκ1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd0 : (0 : ℝ) ≤ d := by positivity
  generalize (K : ℝ) = κ at *
  generalize (k : ℝ) = q at *
  have ht0 : 0 < t := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ10 : κ ≤ t ^ d := by
    have : κ ^ 9 ≤ (t ^ d) ^ 9 := by rw [← pow_mul, mul_comm d 9]; exact hK9
    exact (pow_le_pow_iff_left₀ hκ0.le (by positivity) (by norm_num)).mp this
  have hlt : Real.logb 2 t ≤ 2 * t := logb_le_two_mul t ht1
  have hlt0 : 0 ≤ Real.logb 2 t := Real.logb_nonneg (by norm_num) ht1
  have p81 : t ^ (d * 8 + 1) ≤ t ^ (9 * d - 1) := pow_le_pow_right₀ ht1 (by omega)
  have p20 : t ^ (d * 2) ≤ t ^ (9 * d - 1) := pow_le_pow_right₀ ht1 (by omega)
  have p21 : t ^ (d * 2 + 1) ≤ t ^ (9 * d - 1) := pow_le_pow_right₀ ht1 (by omega)
  have p89 : 0 < t ^ (9 * d - 1) := by positivity
  have e90 : t ^ (9 * d) = t ^ (9 * d - 1) * t := by rw [← pow_succ]; congr 1; omega
  have a2 : 1 * t ^ (9 * d - 1) ≤ q * t ^ (9 * d - 1) := mul_le_mul_of_nonneg_right hk1 p89.le
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hκ0, e90]
    have : t ^ (9 * d - 1) * t ≤ t ^ (9 * d - 1) * κ := mul_le_mul_of_nonneg_left htK p89.le
    have h2 : q * (t ^ (9 * d - 1) * t) ≤ q * (t ^ (9 * d - 1) * κ) := mul_le_mul_of_nonneg_left this (by linarith)
    linarith
  · have h1 : Real.logb 2 κ ≤ 2 * d * t := by
      have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hκ0 hκ10
      rw [Real.logb_pow] at this
      have h3 : (d : ℝ) * Real.logb 2 t ≤ d * (2 * t) := mul_le_mul_of_nonneg_left hlt hd0
      linarith
    have h2 : κ ^ 8 ≤ t ^ (d * 8) := by
      calc κ ^ 8 ≤ (t ^ d) ^ 8 := pow_le_pow_left₀ hκ0.le hκ10 8
        _ = t ^ (d * 8) := by rw [← pow_mul]
    calc κ ^ 8 * Real.logb 2 κ ≤ t ^ (d * 8) * (2 * d * t) :=
          mul_le_mul h2 h1 (Real.logb_nonneg (by norm_num) hκ1) (by positivity)
      _ = 2 * d * t ^ (d * 8 + 1) := by ring
      _ ≤ 2 * d * (q * t ^ (9 * d - 1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have h1 : Real.logb 2 (q * t ^ (9 * d)) ≤ 2 * q + 18 * d * t := by
      rw [Real.logb_mul (by linarith) (by positivity), Real.logb_pow]
      push_cast
      have h3 : 9 * (d : ℝ) * Real.logb 2 t ≤ 9 * d * (2 * t) := mul_le_mul_of_nonneg_left hlt (by positivity)
      linarith [logb_le_two_mul q hk1]
    have h0 : 0 ≤ Real.logb 2 (q * t ^ (9 * d)) :=
      Real.logb_nonneg (by norm_num) (one_le_mul_of_one_le_of_one_le hk1 (one_le_pow₀ ht1))
    have h2 : κ ^ 2 ≤ t ^ (d * 2) := by
      calc κ ^ 2 ≤ (t ^ d) ^ 2 := pow_le_pow_left₀ hκ0.le hκ10 2
        _ = t ^ (d * 2) := by rw [← pow_mul]
    have a1 : q * t ^ (d * 2) ≤ q * t ^ (9 * d - 1) := mul_le_mul_of_nonneg_left p20 (by linarith)
    have a3 : (d : ℝ) * t ^ (d * 2 + 1) ≤ d * (q * t ^ (9 * d - 1)) := mul_le_mul_of_nonneg_left (by linarith) hd0
    calc κ ^ 2 * Real.logb 2 (q * t ^ (9 * d)) ≤ t ^ (d * 2) * (2 * q + 18 * d * t) := mul_le_mul h2 h1 h0 (by positivity)
      _ = 2 * (q * t ^ (d * 2)) + 18 * (d * t ^ (d * 2 + 1)) := by ring
      _ ≤ (2 + 18 * d) * (q * t ^ (9 * d - 1)) := by linarith
end GeneralPieces.TopDisplay
