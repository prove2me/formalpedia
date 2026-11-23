-- Prove2me | solution 1 for GlobalTheory.PerronPsi.near_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:05.18727+00:00
-- url     : https://prove2.me/submissions/19a01e6c-85a1-4bf3-ae4d-a3d1a009c24e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
import Theorems.Thm_GlobalTheory_PerronPsi_half_le_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi
namespace GlobalTheory.PerronPsi
theorem _root_.solution {u T C E : ℝ} {n : ℕ} (hu : 2 ≤ u) (hT : 0 < T) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (h0 : E ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (h : E * (T * |Real.log (u / n)|) ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (hf1 : u / 2 < n) (hf2 : n < 2 * u) :
    Real.log n * E ≤ C * (16 * Real.log u * w ⌊u⌋₊ (2 * u / T) n) := by
  have hu0 : 0 < u := by linarith
  have hL := half_le_log hu
  set L := Real.log u with hLdef
  have hL0 : 0 < L := by linarith
  set N := ⌊u⌋₊ with hN
  set B := 2 * u / T with hB
  have hB0 : 0 ≤ B := div_nonneg (by linarith) hT.le
  have hn1 : (1 : ℝ) < n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1.le
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hu
  have hlogn : Real.log n ≤ 2 * L := by
    have h2 : Real.log n ≤ Real.log (2 * u) := Real.log_le_log hn0 hf2.le
    rw [Real.log_mul (by norm_num) hu0.ne'] at h2
    linarith
  have hM : (u / n) ^ (1 + 1 / L) ≤ 6 := by
    have hr : u / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
    have hσ : 0 ≤ 1 + 1 / L := by have := one_div_pos.2 hL0; linarith
    calc (u / n) ^ (1 + 1 / L) ≤ (2 : ℝ) ^ (1 + 1 / L) :=
          Real.rpow_le_rpow (div_nonneg hu0.le hn0.le) hr hσ
      _ = 2 * Real.exp (Real.log 2 * (1 / L)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_def_of_pos (by norm_num)]
      _ ≤ 2 * Real.exp 1 := by
          gcongr
          rw [mul_one_div, div_le_one hL0]
          exact hlog2
      _ ≤ 6 := by have := Real.exp_one_lt_d9; linarith
  have hCM : C * (u / n) ^ (1 + 1 / L) ≤ 6 * C := by
    have := mul_le_mul_of_nonneg_left hM hC
    linarith
  have hCL : 0 ≤ C * L := mul_nonneg hC hL0.le
  have hwdef : w N B n = (if n = N then 1 else 0) + (if n = N + 1 then 1 else 0)
      + B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ)) := rfl
  have hrest : 0 ≤ B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ)) :=
    mul_nonneg hB0 (by positivity)
  have caseA : 1 ≤ w N B n → Real.log n * E ≤ C * (16 * L * w N B n) := by
    intro hw1
    have h1 : Real.log n * E ≤ 2 * L * (6 * C) :=
      mul_le_mul hlogn (h0.trans hCM) hE (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hw1 hCL]
  have core : ∀ k : ℝ, 0 < k → k / (2 * u) ≤ |Real.log (u / n)| → B * (1 / k) ≤ w N B n →
      Real.log n * E ≤ C * (16 * L * w N B n) := by
    intro k hk hlog hwk
    have h1 : E * (T * (k / (2 * u))) ≤ 6 * C :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hT.le) hE) (h.trans hCM)
    have h2 : E * k = E * (T * (k / (2 * u))) * B := by
      rw [hB]
      field_simp
    have h3 : E * k ≤ 6 * C * B := by
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 hB0
    have h4 : Real.log n * E * k ≤ 2 * L * (6 * C * B) := by
      rw [mul_assoc]
      exact mul_le_mul hlogn h3 (mul_nonneg hE hk.le) (by linarith)
    have h5 : Real.log n * E ≤ 12 * C * L * (B * (1 / k)) := by
      rw [show 12 * C * L * (B * (1 / k)) = (12 * C * L * B) / k by ring, le_div_iff₀ hk]
      linarith
    have hbk : 0 ≤ B * (1 / k) := mul_nonneg hB0 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hwk hCL, mul_nonneg hCL hbk]
  have hNu : (N : ℝ) ≤ u := Nat.floor_le hu0.le
  have huN : u < (N : ℝ) + 1 := Nat.lt_floor_add_one u
  rcases lt_trichotomy n N with hlt | heq | hgt
  · have hlt' : (n : ℝ) < N := by exact_mod_cast hlt
    have hk : (0 : ℝ) < (N : ℝ) - n := sub_pos.2 hlt'
    apply core ((N : ℝ) - n) hk
    · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hu0 hn0)
      rw [inv_div] at h1
      have e1 : 1 - n / u = (u - n) / u := by field_simp
      have e2 : ((N : ℝ) - n) / (2 * u) ≤ (u - n) / (2 * u) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have e3 : (u - n) / (2 * u) ≤ (u - n) / u :=
        div_le_div_of_nonneg_left (by linarith) hu0 (by linarith)
      rw [e1] at h1
      exact e2.trans (e3.trans (h1.trans (le_abs_self _)))
    · have hcast : ((N - n : ℕ) : ℝ) = (N : ℝ) - n := Nat.cast_sub hlt.le
      rw [hwdef, hcast, if_neg hlt.ne, if_neg (by omega), mul_add]
      have : 0 ≤ B * (1 / ((n - (N + 1) : ℕ) : ℝ)) := mul_nonneg hB0 (by positivity)
      linarith
  · apply caseA
    rw [hwdef, if_pos heq]
    have : (0 : ℝ) ≤ if n = N + 1 then 1 else 0 := by split_ifs <;> norm_num
    linarith
  · rcases Nat.lt_or_ge (N + 1) n with hgt2 | hle
    · have hgt2' : (N : ℝ) + 1 < n := by exact_mod_cast hgt2
      have hk : (0 : ℝ) < (n : ℝ) - (N + 1) := by linarith
      apply core ((n : ℝ) - (N + 1)) hk
      · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hu0)
        rw [inv_div] at h1
        have e1 : 1 - u / n = (n - u) / n := by field_simp
        have e2 : ((n : ℝ) - (N + 1)) / (2 * u) ≤ (n - u) / (2 * u) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        have e3 : ((n : ℝ) - u) / (2 * u) ≤ (n - u) / n :=
          div_le_div_of_nonneg_left (by linarith) hn0 hf2.le
        rw [e1] at h1
        have habs : Real.log (n / u) ≤ |Real.log (u / n)| := by
          rw [Real.log_div hu0.ne' hn0.ne', abs_sub_comm, ← Real.log_div hn0.ne' hu0.ne']
          exact le_abs_self _
        exact e2.trans (e3.trans (h1.trans habs))
      · have hcast : ((n - (N + 1) : ℕ) : ℝ) = (n : ℝ) - (N + 1) := by
          rw [Nat.cast_sub hgt2.le]
          push_cast
          ring
        rw [hwdef, hcast, if_neg (by omega), if_neg (by omega), mul_add]
        have : 0 ≤ B * (1 / ((N - n : ℕ) : ℝ)) := mul_nonneg hB0 (by positivity)
        linarith
    · have heq1 : n = N + 1 := by omega
      apply caseA
      rw [hwdef, if_neg (by omega), if_pos heq1]
      linarith
end GlobalTheory.PerronPsi
