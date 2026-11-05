-- Prove2me | solution 1 for GeneralPieces.TopDisplay.kme_of_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:29.551994+00:00
-- url     : https://prove2.me/submissions/95be80e6-a993-47cd-93ed-f2d41965cb52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_root_pow
import Theorems.Thm_GeneralPieces_TopDisplay_root_pow_pred
import Theorems.Thm_GeneralPieces_TopDisplay_one_le_mul_root
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (K C₀ k m d A' : ℕ) (e X : ℝ) (hK : 2 ≤ K) (hd : 1 ≤ d) (hm : K ^ 9 ≤ m) (he : 1 / Real.logb 2 K ^ C₀ ≤ e)
    (h : X ≤ 2 * e * k * m + (A' : ℝ) * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)))) :
    X ≤ ((2 + A' * (d ^ C₀ * (C₀.factorial * 2 ^ C₀)) : ℕ) : ℝ) * k * m * e := by
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_pow _ _ (by omega)) hm
  have ht1 : 1 ≤ (m : ℝ) ^ (1 / (9 * d : ℝ)) := Real.one_le_rpow (by exact_mod_cast hm1) (by positivity)
  have h90 := root_pow m d hd
  have hK9 : (K : ℝ) ^ 9 ≤ m := by exact_mod_cast hm
  rw [root_pow_pred m d hd] at h
  generalize (m : ℝ) ^ (1 / (9 * d : ℝ)) = t at *
  have hκ0 : (0 : ℝ) ≤ K := by positivity
  have hKt : (K : ℝ) ≤ t ^ d := by
    have : (K : ℝ) ^ 9 ≤ (t ^ d) ^ 9 := by rw [← pow_mul, mul_comm d 9, h90]; exact hK9
    exact (pow_le_pow_iff_left₀ hκ0 (by positivity) (by norm_num)).mp this
  have hB := one_le_mul_root K C₀ d t e ht1 hK hKt he
  have e90 : t ^ (9 * d) = t ^ (9 * d - 1) * t := by rw [← pow_succ]; congr 1; omega
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = ((d ^ C₀ * (C₀.factorial * 2 ^ C₀) : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hBc] at hB
  have hp : 0 ≤ (k : ℝ) * t ^ (9 * d - 1) := by positivity
  have h5 : (k : ℝ) * t ^ (9 * d - 1) ≤ Bc * (k * m * e) :=
    calc (k : ℝ) * t ^ (9 * d - 1) = k * t ^ (9 * d - 1) * 1 := (mul_one _).symm
      _ ≤ k * t ^ (9 * d - 1) * (Bc * e * t) := mul_le_mul_of_nonneg_left hB hp
      _ = Bc * (k * (t ^ (9 * d - 1) * t) * e) := by ring
      _ = Bc * (k * m * e) := by rw [← e90, h90]
  have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg A' : (0 : ℝ) ≤ A')
  have h7 : ((2 + A' * (d ^ C₀ * (C₀.factorial * 2 ^ C₀)) : ℕ) : ℝ) = 2 + (A' : ℝ) * Bc := by rw [hBc]; push_cast; ring
  rw [h7]
  linarith
end GeneralPieces.TopDisplay
