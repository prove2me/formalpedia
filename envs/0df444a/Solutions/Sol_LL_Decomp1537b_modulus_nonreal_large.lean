-- Prove2me | solution 1 for LL_Decomp1537b.modulus_nonreal_large
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:23:41.866486+00:00
-- url     : https://prove2.me/submissions/bfbf0eff-26ce-426c-a824-32258e2be4e0

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SolLinnikHelpers

private theorem log_kernel_sublinear {x L : ℝ}
    (hx : 1 ≤ x) (hL : 0 < L) (hxL : x ≤ 2 * L) :
    (x * Real.log x) ^ ((3 : ℝ) / 4) ≤ 12 * L ^ ((7 : ℝ) / 8) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ 6 * x ^ ((1 : ℝ) / 6) := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 6)
    norm_num [div_eq_mul_inv] at h
    nlinarith
  have hprod : x * Real.log x ≤ 6 * x ^ ((7 : ℝ) / 6) := by
    calc
      x * Real.log x ≤ x * (6 * x ^ ((1 : ℝ) / 6)) :=
        mul_le_mul_of_nonneg_left hlog hx0.le
      _ = 6 * x ^ ((1 : ℝ) + 1 / 6) := by
        rw [Real.rpow_add hx0]
        simp only [Real.rpow_one]
        ring
      _ = 6 * x ^ ((7 : ℝ) / 6) := by norm_num
  have h6 : (6 : ℝ) ^ ((3 : ℝ) / 4) ≤ 6 := by
    calc
      (6 : ℝ) ^ ((3 : ℝ) / 4) ≤ (6 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 6 := Real.rpow_one _
  have h2 : (2 : ℝ) ^ ((7 : ℝ) / 8) ≤ 2 := by
    calc
      (2 : ℝ) ^ ((7 : ℝ) / 8) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  calc
    (x * Real.log x) ^ ((3 : ℝ) / 4)
        ≤ (6 * x ^ ((7 : ℝ) / 6)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (mul_nonneg hx0.le hlog0) hprod (by norm_num)
    _ = (6 : ℝ) ^ ((3 : ℝ) / 4) * x ^ ((7 : ℝ) / 8) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6)
        (Real.rpow_nonneg hx0.le _)]
      rw [← Real.rpow_mul hx0.le]
      norm_num
    _ ≤ 6 * x ^ ((7 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hx0.le _)
    _ ≤ 6 * (2 * L) ^ ((7 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hx0.le hxL (by norm_num)) (by norm_num)
    _ = 6 * ((2 : ℝ) ^ ((7 : ℝ) / 8) * L ^ ((7 : ℝ) / 8)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL.le]
    _ ≤ 6 * (2 * L ^ ((7 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hL.le _)) (by norm_num)
    _ = 12 * L ^ ((7 : ℝ) / 8) := by ring

private theorem absorb_kernel {H L : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hpow : (960000 * H) ^ (8 : ℕ) ≤ L) :
    12 * L ^ ((7 : ℝ) / 8) ≤ L / (80000 * H) := by
  set d : ℝ := 80000 * H
  have hd : 0 < d := by positivity
  have h12d : 0 ≤ 12 * d := by positivity
  have hpow' : (12 * d) ^ (8 : ℝ) ≤ L := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc
      (12 * d) ^ (8 : ℕ) = (960000 * H) ^ (8 : ℕ) := by dsimp [d]; ring
      _ ≤ L := hpow
  have hroot : 12 * d ≤ L ^ ((1 : ℝ) / 8) := by
    calc
      12 * d = ((12 * d) ^ (8 : ℝ)) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_mul h12d]
        norm_num
      _ ≤ L ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (Real.rpow_nonneg h12d _) hpow' (by norm_num)
  have hmul : 12 * d * L ^ ((7 : ℝ) / 8) ≤ L := by
    calc
      12 * d * L ^ ((7 : ℝ) / 8) ≤ L ^ ((1 : ℝ) / 8) * L ^ ((7 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hL.le _)
      _ = L ^ ((1 : ℝ) / 8 + 7 / 8) := by rw [← Real.rpow_add hL]
      _ = L := by norm_num
  rw [le_div_iff₀ hd]
  linarith

private theorem finish_from_kernel_bound {H L A B σ T : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hD : 0 < A + B)
    (hlower : 1 - H / L ≤ σ)
    (hupper : σ ≤ 1 - 1 / (40000 * (A + B)))
    (hB : B ≤ L / (80000 * H))
    (hT : 80000 * H * T ≤ L) : T ≤ A := by
  have hden : 0 < 40000 * (A + B) := by positivity
  have hd : 0 < 80000 * H := by positivity
  have hrecip : 1 / (40000 * (A + B)) ≤ H / L := by linarith
  have hcross := (div_le_div_iff₀ hden hL).mp hrecip
  have hBmul := (le_div_iff₀ hd).mp hB
  have hmul : (80000 * H) * T ≤ (80000 * H) * A := by
    nlinarith
  exact le_of_mul_le_mul_left hmul hd

end SolLinnikHelpers

theorem solution {H : ℝ} (hH : 0 < H) (T : ℝ) :
    ∃ Y : ℝ, ∀ N : ℝ, 4 ≤ N → Y ≤ Real.log N → ∀ r' r t σ : ℝ, 1 ≤ r' → 3 ≤ r → r ≤ N →
      |t| ≤ Real.sqrt N → 1 - H / Real.log N ≤ σ →
      σ ≤ 1 - 1 / (4 * 10 ^ 4 * (Real.log (2 * r') +
        (Real.log (r * (|t| + 2)) * Real.log (Real.log (r * (|t| + 2)))) ^ ((3 : ℝ) / 4))) →
      T ≤ Real.log (2 * r') := by
  refine ⟨max 2 (max (80000 * H * max T 0) ((960000 * H) ^ (8 : ℕ))), ?_⟩
  intro N hN4 hYN r' r t σ hr' hr3 hrN ht hlower hupper
  set L : ℝ := Real.log N
  set A : ℝ := Real.log (2 * r')
  set ell : ℝ := Real.log (r * (|t| + 2))
  set B : ℝ := (ell * Real.log ell) ^ ((3 : ℝ) / 4)
  have hY2 : 2 ≤ L := le_trans (le_max_left _ _) hYN
  have hL : 0 < L := by linarith
  have hYT : 80000 * H * max T 0 ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hYN
  have hYpow : (960000 * H) ^ (8 : ℕ) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hYN
  have hsqrt : Real.sqrt N + 2 ≤ N := by
    have hsq : Real.sqrt N ≤ N - 2 :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    linarith
  have harg_lower : 4 ≤ r * (|t| + 2) := by
    have htabs : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have harg_upper : r * (|t| + 2) ≤ N ^ 2 := by
    have htabs : 0 ≤ |t| := abs_nonneg t
    have ht2 : |t| + 2 ≤ N := by linarith
    nlinarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog4 : 1 ≤ Real.log 4 := by
    have h4 : Real.log (4 : ℝ) = Real.log (2 * 2) := by norm_num
    rw [h4, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hell_ge : 1 ≤ ell := by
    have h4le : Real.log 4 ≤ Real.log (r * (|t| + 2)) :=
      Real.log_le_log (by norm_num) harg_lower
    exact le_trans hlog4 h4le
  have hell_le : ell ≤ 2 * L := by
    have hN0 : 0 < N := by linarith
    have harg0 : 0 < r * (|t| + 2) := by linarith
    have hle : Real.log (r * (|t| + 2)) ≤ Real.log (N ^ 2) :=
      Real.log_le_log harg0 harg_upper
    rw [Real.log_pow] at hle
    simpa [ell, L] using hle
  have hA : 0 < A := Real.log_pos (by linarith)
  have hB0 : 0 ≤ B := Real.rpow_nonneg (mul_nonneg (by linarith) (Real.log_nonneg hell_ge)) _
  have hD : 0 < A + B := by linarith
  have hB_sub : B ≤ 12 * L ^ ((7 : ℝ) / 8) :=
    SolLinnikHelpers.log_kernel_sublinear hell_ge hL hell_le
  have hB_abs : 12 * L ^ ((7 : ℝ) / 8) ≤ L / (80000 * H) :=
    SolLinnikHelpers.absorb_kernel hH hL hYpow
  have hB : B ≤ L / (80000 * H) := le_trans hB_sub hB_abs
  have hT : 80000 * H * T ≤ L := by
    have h1 : 80000 * H * T ≤ 80000 * H * max T 0 :=
      mul_le_mul_of_nonneg_left (le_max_left T 0) (by positivity)
    exact le_trans h1 hYT
  have hupper' : σ ≤ 1 - 1 / (40000 * (A + B)) := by
    have h40k : (4 : ℝ) * 10 ^ 4 = 40000 := by norm_num
    rw [h40k] at hupper
    exact hupper
  exact SolLinnikHelpers.finish_from_kernel_bound hH hL hD hlower hupper' hB hT
