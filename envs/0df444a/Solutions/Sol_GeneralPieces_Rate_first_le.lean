-- Prove2me | solution 1 for GeneralPieces.Rate.first_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:03.379049+00:00
-- url     : https://prove2.me/submissions/0395ea3b-ffd8-49b7-9313-ef43809ad796

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_log
import Theorems.Thm_ClauseBound_Gen_Rate_size_cast_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_first_le
import Theorems.Thm_ClauseBound_Gen_Rate_small_le_sq
import Theorems.Thm_GeneralPieces_PartAUse_one_le_e_mul_K
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (l lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    ((max (Nat.size (cnt * instLen (K x₀ l) lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size (K x₀ l)))) : ℕ) : ℝ) ≤
      Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ l lam B := by
  have hK := big_le_K hx l
  have hL1 := one_le_log hx l lam B hlam
  have hX : ((K x₀ l * (lam + B) : ℕ) : ℝ) = (K x₀ l : ℝ) * (lam + B) := by push_cast; ring
  have hX1 : 1 ≤ K x₀ l * (lam + B) := Nat.mul_pos (by omega) (by omega)
  have hs := small_le_sq (K x₀ l) lam B (by omega) hlam
  have s1 := size_cast_le hX1 hs.1
  have s2 := size_cast_le hX1 hs.2
  have s3 : (Nat.size B : ℝ) ≤ (1 : ℕ) * Real.logb 2 ((K x₀ l * (lam + B) : ℕ) : ℝ) + 1 := by
    apply size_cast_le hX1
    rw [pow_one]
    calc B ≤ lam + B := Nat.le_add_left _ _
      _ ≤ K x₀ l * (lam + B) := Nat.le_mul_of_pos_left _ (by omega)
  have s4 : (Nat.size (K x₀ l) : ℝ) ≤ (1 : ℕ) * Real.logb 2 ((K x₀ l * (lam + B) : ℕ) : ℝ) + 1 := by
    apply size_cast_le hX1
    rw [pow_one]
    exact Nat.le_mul_of_pos_right _ (by omega)
  rw [hX] at s1 s2 s3 s4
  have hf : (Nat.size (cnt * instLen (K x₀ l) lam B + 8 * z + 4 * lam + 40) : ℝ) ≤
      Nat.size cnt + Nat.size z + (((K x₀ l - 1) * lam : ℕ) : ℝ) + Nat.size (4 * lam + K x₀ l * (3 * B + 14) + 10) + Nat.size (4 * lam + 40) + 4 := by
    exact_mod_cast size_first_le (K x₀ l) lam B cnt z
  have hz : (Nat.size z : ℝ) ≤ Nat.size (z + Nat.size cnt) := by exact_mod_cast Nat.size_le_size (Nat.le_add_right _ _)
  have hkl : (((K x₀ l - 1) * lam : ℕ) : ℝ) ≤ (K x₀ l : ℝ) * lam := by
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hk1 : (1 : ℝ) ≤ K x₀ l := by exact_mod_cast (by omega : 1 ≤ K x₀ l)
  have hlm : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have he : (K x₀ l : ℝ) * lam ≤ e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam := by
    have h := mul_le_mul_of_nonneg_right (PartAUse.one_le_e_mul_K (PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx) hρ hx l) (by positivity : (0 : ℝ) ≤ (K x₀ l : ℝ) * lam)
    calc (K x₀ l : ℝ) * lam = 1 * ((K x₀ l : ℝ) * lam) := by ring
      _ ≤ e ρ x₀ l * K x₀ l * ((K x₀ l : ℝ) * lam) := h
      _ = e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam := by ring
  have hl' : (lam : ℝ) ≤ (K x₀ l : ℝ) * lam := le_mul_of_one_le_left (by positivity) hk1
  unfold Bd
  generalize Real.logb 2 ((K x₀ l : ℝ) * (lam + B)) = L at *
  have hCL : 10 * L ≤ (6 * c + 14) * (K x₀ l : ℝ) ^ 2 * L := by
    have h1 : (1 : ℝ) ≤ (K x₀ l : ℝ) ^ 2 := one_le_pow₀ hk1
    have h2 : (0 : ℝ) ≤ c := by positivity
    have h3 : (10 : ℝ) ≤ (6 * c + 14) * (K x₀ l : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right h3 (by linarith)
  have p1 : (0 : ℝ) ≤ Nat.size cnt := by positivity
  have p2 : (0 : ℝ) ≤ Nat.size (z + Nat.size cnt) := by positivity
  push_cast at s1 s2 s3 s4
  rw [Nat.cast_max, Nat.cast_max, Nat.cast_max]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_)) <;> linarith
end GeneralPieces.Rate
