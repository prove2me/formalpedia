-- Prove2me | solution 1 for Kyprianou.Ch01.branchingRenewalHomogeneousVanish
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-23T15:14:11.182799+00:00
-- url     : https://prove2.me/submissions/260805ed-4b26-4948-aae4-cd12e9cd7fe3

import Mathlib

open Finset MeasureTheory
open scoped BigOperators Interval NNReal ENNReal
set_option autoImplicit false
set_option linter.unusedVariables false

lemma catalan_real (n : ℕ) :
    (catalan n : ℝ) = (Nat.centralBinom n : ℝ) / ((n : ℝ) + 1) := by
  rw [catalan_eq_centralBinom_div,
    Nat.cast_div (Nat.succ_dvd_centralBinom n) (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0),
    Nat.cast_succ]

lemma catalan_succ_ratio (n : ℕ) :
    (catalan (n + 1) : ℝ) =
      (catalan n : ℝ) * (2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 2) := by
  rw [catalan_real, catalan_real]
  push_cast
  have hstep := Nat.succ_mul_centralBinom_succ n
  have hcast : (↑n + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * ↑n + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast hstep
  have hn : (↑n + 1 : ℝ) ≠ 0 := by positivity
  have hcentral : (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * ↑n + 1) * (Nat.centralBinom n : ℝ) / (↑n + 1) :=
    (eq_div_iff hn).mpr (by simpa [mul_comm] using hcast)
  rw [hcentral]
  field_simp [hn]
  ring

lemma half_pow_ratio_le (a : ℝ) (ha : 1 ≤ a) :
    (2 * a - 1) / (2 * (a + 1)) ≤ (a / (a + 1)) ^ (3 / 2 : ℝ) := by
  have hap : 0 < a + 1 := by linarith
  have hbase : 0 ≤ a / (a + 1) := by positivity
  have hsq : ((2 * a - 1) / 2) ^ 2 ≤ a ^ 3 / (a + 1) := by
    rw [div_pow, show ((2 : ℝ) ^ 2) = 4 by norm_num, div_le_div_iff₀ (by norm_num) hap]
    nlinarith
  have hsqrt : (2 * a - 1) / 2 ≤ Real.sqrt (a ^ 3 / (a + 1)) :=
    (Real.le_sqrt (by linarith : (0 : ℝ) ≤ (2 * a - 1) / 2)
      (by positivity : (0 : ℝ) ≤ a ^ 3 / (a + 1))).mpr hsq
  have hsplit : Real.sqrt (a ^ 3 / (a + 1)) = Real.sqrt (a ^ 3) / Real.sqrt (a + 1) :=
    Real.sqrt_div (by positivity : (0 : ℝ) ≤ a ^ 3) (a + 1)
  have hform : (a / (a + 1)) ^ (3 / 2 : ℝ) =
      Real.sqrt (a ^ 3) / ((a + 1) * Real.sqrt (a + 1)) := by
    calc
      (a / (a + 1)) ^ (3 / 2 : ℝ)
          = ((a / (a + 1)) ^ (3 : ℝ)) ^ (1 / 2 : ℝ) := by
            rw [show (3 / 2 : ℝ) = (3 : ℝ) * (1 / 2) by norm_num, Real.rpow_mul hbase]
      _ = Real.sqrt ((a / (a + 1)) ^ (3 : ℝ)) := by rw [← Real.sqrt_eq_rpow]
      _ = Real.sqrt ((a / (a + 1)) ^ 3) := by
            congr 1
            exact (Real.rpow_natCast (a / (a + 1)) 3)
      _ = Real.sqrt (a ^ 3 / (a + 1) ^ 3) := by
            congr 1
            field_simp
      _ = Real.sqrt (a ^ 3) / Real.sqrt ((a + 1) ^ 3) :=
            Real.sqrt_div (by positivity : (0 : ℝ) ≤ a ^ 3) ((a + 1) ^ 3)
      _ = Real.sqrt (a ^ 3) / ((a + 1) * Real.sqrt (a + 1)) := by
            congr 1
            rw [show (a + 1) ^ 3 = (a + 1) ^ 2 * (a + 1) by ring,
              Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (a + 1) ^ 2),
              Real.sqrt_sq (by linarith : (0 : ℝ) ≤ a + 1)]
  rw [hform, div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (a + 1))
    (by positivity : (0 : ℝ) < (a + 1) * Real.sqrt (a + 1))]
  have hcancel : (2 * a - 1) * Real.sqrt (a + 1) ≤ 2 * Real.sqrt (a ^ 3) := by
    have hstep : (2 * a - 1) / 2 ≤ Real.sqrt (a ^ 3) / Real.sqrt (a + 1) := by
      rwa [← hsplit]
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hap)] at hstep
    have hmul := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 2)
    have hleft : (2 * a - 1) * Real.sqrt (a + 1) =
        2 * ((2 * a - 1) / 2 * Real.sqrt (a + 1)) := by ring
    rw [hleft]
    exact hmul
  have hmul := mul_le_mul_of_nonneg_left hcancel (by linarith : (0 : ℝ) ≤ a + 1)
  convert hmul using 1 <;> ring

lemma catalan_rpow_bound (n : ℕ) :
    (catalan n : ℝ) ≤ (4 : ℝ) ^ n / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
  induction n with
  | zero =>
      simp [catalan_zero, pow_zero, Real.one_rpow]
  | succ n ih =>
      rw [catalan_succ_ratio]
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      have hratio : (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 4) ≤
          (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ (3 / 2 : ℝ) := by
        have h := half_pow_ratio_le ((n : ℝ) + 1)
          (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
        have hL : (2 * ((n : ℝ) + 1) - 1) / (2 * (((n : ℝ) + 1) + 1)) =
            (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 4) := by ring
        have hR : (((n : ℝ) + 1) / (((n : ℝ) + 1) + 1)) =
            ((n : ℝ) + 1) / ((n : ℝ) + 2) := by ring
        rw [hL, hR] at h
        exact h
      have hcoeff : (2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 2) ≤
          4 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ (3 / 2 : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4)
        have hL : 4 * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 4)) =
            (2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 2) := by
          field_simp
          ring
        rw [← hL]
        exact hmul
      have hstep : (catalan n : ℝ) * (2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 2) ≤
          ((4 : ℝ) ^ n / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) *
            ((2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 2)) := by
        have hc : 0 ≤ (2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 2) := by positivity
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_right ih hc
      have hposA : 0 ≤ (4 : ℝ) ^ n / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hcoeff hposA
      have hclose : (4 : ℝ) ^ n / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) *
            (4 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ (3 / 2 : ℝ)) =
          (4 : ℝ) ^ (n + 1) / ((n : ℝ) + 2) ^ (3 / 2 : ℝ) := by
        rw [Real.div_rpow (by positivity) (by positivity)]
        field_simp
        ring
      exact (hstep.trans hmul).trans_eq hclose

lemma one_div_shift_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
  have hfull : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_rpow).mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :=
    (summable_nat_add_iff 1).mpr hfull
  simpa [Nat.cast_add, Nat.cast_one] using hshift

lemma catalan_scaled_summable :
    Summable (fun n : ℕ => (catalan n : ℝ) / (4 : ℝ) ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) one_div_shift_summable
  · positivity
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ n)]
    simpa [div_eq_mul_inv, mul_comm] using catalan_rpow_bound n

noncomputable def catalanSeries (x : ℝ) : ℝ :=
  ∑' n, (catalan n : ℝ) * x ^ n

lemma catalan_pow_summable {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) :
    Summable (fun n : ℕ => (catalan n : ℝ) * x ^ n) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx n))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hx4 n) (Nat.cast_nonneg _))
    ?_
  convert catalan_scaled_summable using 2 with n
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv]

lemma catalan_antidiagonal (n : ℕ) :
    ∑ ij ∈ antidiagonal n, (catalan ij.1 : ℝ) * catalan ij.2 = (catalan (n + 1) : ℝ) := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (catalan_succ' n)
  rw [Nat.cast_sum] at h
  simp only [Nat.cast_mul] at h
  exact h.symm

lemma catalan_square_series {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) :
    catalanSeries x ^ 2 = ∑' n, (catalan (n + 1) : ℝ) * x ^ n := by
  have hs := catalan_pow_summable hx hx4
  have hnorm : Summable (fun n => ‖(catalan n : ℝ) * x ^ n‖) := by
    have habs : ∀ n, ‖(catalan n : ℝ) * x ^ n‖ = (catalan n : ℝ) * x ^ n := by
      intro n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx n))]
    simpa [habs] using hs
  have hcauchy :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := fun n => (catalan n : ℝ) * x ^ n)
      (g := fun n => (catalan n : ℝ) * x ^ n) hnorm hnorm
  unfold catalanSeries
  rw [pow_two, hcauchy]
  refine tsum_congr ?_
  intro n
  calc
    ∑ ij ∈ antidiagonal n,
        ((catalan ij.1 : ℝ) * x ^ ij.1) * ((catalan ij.2 : ℝ) * x ^ ij.2)
        = ∑ ij ∈ antidiagonal n, (catalan ij.1 : ℝ) * catalan ij.2 * x ^ (ij.1 + ij.2) := by
          refine sum_congr rfl ?_
          intro ij _
          calc
            ((catalan ij.1 : ℝ) * x ^ ij.1) * ((catalan ij.2 : ℝ) * x ^ ij.2)
                = (catalan ij.1 : ℝ) * catalan ij.2 * (x ^ ij.1 * x ^ ij.2) := by ring
            _ = (catalan ij.1 : ℝ) * catalan ij.2 * x ^ (ij.1 + ij.2) := by rw [← pow_add]
    _ = ∑ ij ∈ antidiagonal n, (catalan ij.1 : ℝ) * catalan ij.2 * x ^ n := by
          refine sum_congr rfl ?_
          intro ij hij
          rw [show ij.1 + ij.2 = n from (mem_antidiagonal.mp hij)]
    _ = (∑ ij ∈ antidiagonal n, (catalan ij.1 : ℝ) * catalan ij.2) * x ^ n := by
          rw [← sum_mul]
    _ = (catalan (n + 1) : ℝ) * x ^ n := by rw [catalan_antidiagonal]

lemma catalan_series_shift {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) :
    catalanSeries x = 1 + x * ∑' n, (catalan (n + 1) : ℝ) * x ^ n := by
  have hs := catalan_pow_summable hx hx4
  rw [catalanSeries, hs.tsum_eq_zero_add]
  simp [catalan_zero, pow_zero]
  rw [← tsum_mul_left]
  refine tsum_congr ?_
  intro n
  rw [pow_succ]
  ring

lemma catalan_series_quadratic {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) :
    catalanSeries x = 1 + x * catalanSeries x ^ 2 := by
  conv_lhs => rw [catalan_series_shift hx hx4]
  rw [catalan_square_series hx hx4]

lemma catalanSeries_quarter : catalanSeries (1 / 4) = 2 := by
  have hid := catalan_series_quadratic (x := 1 / 4) (by norm_num) (by norm_num)
  have hpoly : (catalanSeries (1 / 4) - 2) ^ 2 = 0 := by nlinarith [hid]
  linarith [(sq_eq_zero_iff).mp hpoly]

lemma catalanSeries_le {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) : catalanSeries x ≤ 2 := by
  have hterm : ∀ n, (catalan n : ℝ) * x ^ n ≤ (catalan n : ℝ) * (1 / 4) ^ n :=
    fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hx4 n) (Nat.cast_nonneg _)
  have hsum := (catalan_pow_summable hx hx4).tsum_le_tsum hterm
    (catalan_pow_summable (by norm_num) (by norm_num))
  have h14 : ∑' n, (catalan n : ℝ) * (1 / 4) ^ n = 2 := by
    simpa [catalanSeries] using catalanSeries_quarter
  simpa [catalanSeries] using hsum.trans_eq h14

lemma catalanSeries_closed {x : ℝ} (hx : 0 < x) (hx4 : x ≤ 1 / 4) :
    catalanSeries x = (1 - Real.sqrt (1 - 4 * x)) / (2 * x) := by
  have hid := catalan_series_quadratic hx.le hx4
  have hle := catalanSeries_le hx.le hx4
  set G := catalanSeries x
  have hsq : (2 * x * G - 1) ^ 2 = 1 - 4 * x := by nlinarith [hid]
  have hsqrt : (Real.sqrt (1 - 4 * x)) ^ 2 = 1 - 4 * x := Real.sq_sqrt (by linarith)
  have hdisj : 2 * x * G - 1 = Real.sqrt (1 - 4 * x) ∨
      2 * x * G - 1 = -Real.sqrt (1 - 4 * x) :=
    (sq_eq_sq_iff_eq_or_eq_neg).mp (by rw [hsq, hsqrt])
  have hnonpos : 2 * x * G - 1 ≤ 0 := by nlinarith
  have hneg : 2 * x * G - 1 = -Real.sqrt (1 - 4 * x) := by
    rcases hdisj with hpos | hneg
    · have hle0 : Real.sqrt (1 - 4 * x) ≤ 0 := by linarith
      have hz : Real.sqrt (1 - 4 * x) = 0 := le_antisymm hle0 (Real.sqrt_nonneg _)
      rw [hpos, hz, neg_zero]
    · exact hneg
  rw [eq_div_iff (by positivity : (2 * x) ≠ 0), mul_comm]
  linarith

noncomputable def sibuya (n : ℕ) : ℝ :=
  if n = 0 then 0 else (catalan (n - 1) : ℝ) / (2 : ℝ) ^ (2 * n - 1)

lemma sibuya_nonneg (n : ℕ) : 0 ≤ sibuya n := by
  unfold sibuya
  split_ifs <;> positivity

lemma sibuya_zero : sibuya 0 = 0 := by simp [sibuya]

lemma sibuya_succ (m : ℕ) :
    sibuya (m + 1) = (catalan m : ℝ) * (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ m := by
  rw [sibuya, if_neg (Nat.succ_ne_zero m)]
  have hsub : (m + 1) - 1 = m := by omega
  rw [hsub]
  have htwo : (2 : ℝ) ^ (2 * (m + 1) - 1) = 2 * (4 : ℝ) ^ m := by
    have hpow : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [hpow, pow_add, pow_one, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
    ring
  rw [htwo, div_eq_mul_inv, mul_inv]
  have hinv : ((4 : ℝ) ^ m)⁻¹ = (1 / 4) ^ m := by
    rw [← inv_pow, show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
  have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hinv, hhalf]
  ring

lemma sibuya_summable : Summable sibuya := by
  have htail : Summable (fun m : ℕ => sibuya (m + 1)) := by
    have hfun : (fun m : ℕ => sibuya (m + 1)) =
        fun m => (1 / 2 : ℝ) * ((catalan m : ℝ) / (4 : ℝ) ^ m) := by
      funext m
      rw [sibuya_succ, show (1 / 4 : ℝ) ^ m = (4 : ℝ)⁻¹ ^ m by rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num],
        inv_pow, div_eq_mul_inv]
      ring
    simpa [hfun] using catalan_scaled_summable.mul_left (1 / 2 : ℝ)
  exact (summable_nat_add_iff 1).mp htail

lemma sibuya_tsum : ∑' n, sibuya n = 1 := by
  rw [sibuya_summable.tsum_eq_zero_add, sibuya_zero, zero_add]
  have hfun : ∑' m, sibuya (m + 1) = (1 / 2 : ℝ) * catalanSeries (1 / 4) := by
    unfold catalanSeries
    rw [← tsum_mul_left]
    refine tsum_congr ?_
    intro m
    rw [sibuya_succ]
    ring
  rw [hfun, catalanSeries_quarter]
  norm_num

lemma sibuya_series_summable {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (fun n => sibuya n * s ^ n) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sibuya_nonneg n) (pow_nonneg hs n))
    (fun n => by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ (n := n) hs hs1) (sibuya_nonneg n))
    sibuya_summable

lemma sibuya_pgf {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑' n, sibuya n * s ^ n = 1 - Real.sqrt (1 - s) := by
  by_cases hs0 : s = 0
  · subst hs0
    have hsum : ∑' n, sibuya n * (0 : ℝ) ^ n = 0 := by
      rw [tsum_eq_single 0]
      · simp [sibuya_zero]
      · intro n hn
        simp [zero_pow hn]
    rw [hsum, show (1 : ℝ) - 0 = 1 by ring, Real.sqrt_one]
    ring
  · have hsum := sibuya_series_summable hs hs1
    rw [hsum.tsum_eq_zero_add, sibuya_zero, zero_mul, zero_add]
    have htail : ∑' m, sibuya (m + 1) * s ^ (m + 1) =
        (s / 2) * catalanSeries (s / 4) := by
      unfold catalanSeries
      rw [← tsum_mul_left]
      refine tsum_congr ?_
      intro m
      rw [sibuya_succ, pow_succ]
      have hmul : (1 / 4 : ℝ) ^ m * s ^ m = (s / 4) ^ m := by
        rw [← mul_pow]
        congr 1
        ring
      calc
        (catalan m : ℝ) * (1 / 2) * (1 / 4) ^ m * (s ^ m * s)
            = (s / 2) * ((catalan m : ℝ) * ((1 / 4) ^ m * s ^ m)) := by ring
        _ = (s / 2) * ((catalan m : ℝ) * (s / 4) ^ m) := by rw [hmul]
    rw [htail]
    have hx : 0 < s / 4 := by positivity
    have hx4 : s / 4 ≤ 1 / 4 := by linarith
    rw [catalanSeries_closed hx hx4]
    have hdisc : 1 - 4 * (s / 4) = 1 - s := by ring
    rw [hdisc]
    field_simp [hs0]
    ring

noncomputable def offspringCounter : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (sibuya n), by
    have hsum : ∑' n, ENNReal.ofReal (sibuya n) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sibuya_nonneg n) sibuya_summable,
        sibuya_tsum, ENNReal.ofReal_one]
    have hhas : HasSum (fun n => ENNReal.ofReal (sibuya n))
        (∑' n, ENNReal.ofReal (sibuya n)) := ENNReal.summable.hasSum
    rwa [hsum] at hhas⟩

noncomputable def eta (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * (2 - Real.exp (-t / 2))

noncomputable def etaDeriv (t : ℝ) : ℝ :=
  -(Real.exp (-t / 2) * (1 - Real.exp (-t / 2)))

noncomputable def mass (y : ℕ) (t : ℝ) : ℝ :=
  1 - eta t ^ y

noncomputable def phi (y : ℕ) (t : ℝ) : ℝ :=
  1 - eta t ^ (y - 1) * Real.exp (-t / 2)

noncomputable def defect (y : ℕ) (t : ℝ≥0) (_k : ℕ) : ℝ :=
  mass y (t : ℝ)

lemma hasDerivAt_halfExp (t : ℝ) :
    HasDerivAt (fun u => Real.exp (-u / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
  have hlin : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2) t := by
    simpa using ((hasDerivAt_id t).neg.div_const (2 : ℝ))
  have hcomp := (Real.hasDerivAt_exp (-t / 2)).comp t hlin
  have hfun : (Real.exp ∘ fun u => -u / 2) = fun u => Real.exp (-u / 2) := by
    funext u
    rfl
  rw [hfun] at hcomp
  exact hcomp

lemma hasDerivAt_eta (t : ℝ) : HasDerivAt eta (etaDeriv t) t := by
  have he := hasDerivAt_halfExp t
  have hsub := (hasDerivAt_const t (2 : ℝ)).sub he
  have hmul := he.mul hsub
  have hderiv :
      Real.exp (-t / 2) * (-1 / 2) * (2 - Real.exp (-t / 2)) +
        Real.exp (-t / 2) * (0 - Real.exp (-t / 2) * (-1 / 2)) = etaDeriv t := by
    unfold etaDeriv
    ring
  have heq : eta =ᶠ[nhds t]
      ((fun u => Real.exp (-u / 2)) * fun u => 2 - Real.exp (-u / 2)) := by
    refine Filter.EventuallyEq.of_eq ?_
    funext u
    unfold eta
    simp [Pi.mul_apply]
  exact (hmul.congr_deriv hderiv).congr_of_eventuallyEq heq.symm

lemma hasDerivAt_mass (y : ℕ) (t : ℝ) :
    HasDerivAt (mass y) (-((y : ℝ) * eta t ^ (y - 1) * etaDeriv t)) t := by
  have hsub := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_eta t).pow y)
  have hderiv : 0 - (y : ℝ) * eta t ^ (y - 1) * etaDeriv t =
      -((y : ℝ) * eta t ^ (y - 1) * etaDeriv t) := by ring
  have heq : mass y =ᶠ[nhds t] ((fun _ : ℝ => (1 : ℝ)) - eta ^ y) := by
    refine Filter.EventuallyEq.of_eq ?_
    funext u
    unfold mass
    rfl
  exact (hsub.congr_deriv hderiv).congr_of_eventuallyEq heq.symm

lemma exp_half_le_one {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  linarith

lemma eta_bounds {t : ℝ} (ht : 0 ≤ t) : 0 < eta t ∧ eta t ≤ 1 := by
  have hepos : 0 < Real.exp (-t / 2) := Real.exp_pos _
  have hele := exp_half_le_one ht
  have hform : eta t = 1 - (1 - Real.exp (-t / 2)) ^ 2 := by
    unfold eta
    ring
  constructor
  · rw [hform]
    have hsq : (1 - Real.exp (-t / 2)) ^ 2 < 1 := by
      have hlt : 1 - Real.exp (-t / 2) < 1 := by linarith [hepos]
      have hnn : 0 ≤ 1 - Real.exp (-t / 2) := by linarith
      nlinarith
    linarith
  · rw [hform]
    linarith [sq_nonneg (1 - Real.exp (-t / 2))]

lemma mass_bounds (y : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ mass y t ∧ mass y t ≤ 1 := by
  have he := eta_bounds ht
  have hpow_nonneg : 0 ≤ eta t ^ y := pow_nonneg he.1.le y
  have hpow_le : eta t ^ y ≤ 1 := pow_le_one₀ he.1.le he.2
  unfold mass
  constructor <;> linarith

lemma mass_ode (y : ℕ) (hy : 0 < y) (t : ℝ) :
    -((y : ℝ) * eta t ^ (y - 1) * etaDeriv t) + (y : ℝ) * mass y t = (y : ℝ) * phi y t := by
  set e := Real.exp (-t / 2)
  have hpow : eta t ^ y = eta t ^ (y - 1) * eta t := by
    conv_lhs => rw [← Nat.sub_add_cancel hy]
    exact pow_succ (eta t) (y - 1)
  have hp : eta t = e * (2 - e) := by
    unfold eta
    ring
  have hd : etaDeriv t = -(e * (1 - e)) := by
    unfold etaDeriv
    ring
  have hpow' : (e * (2 - e)) ^ y = (e * (2 - e)) ^ (y - 1) * (e * (2 - e)) := by
    conv_lhs => rw [← Nat.sub_add_cancel hy]
    exact pow_succ _ _
  unfold mass phi
  rw [hp, hd, hpow']
  ring

lemma hasDerivAt_factor (y : ℕ) (hy : 0 < y) (t : ℝ) :
    HasDerivAt (fun u => Real.exp ((y : ℝ) * u) * mass y u)
      (Real.exp ((y : ℝ) * t) * (y : ℝ) * phi y t) t := by
  have hlin : HasDerivAt (fun u => (y : ℝ) * u) (y : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (y : ℝ)
  have hexp0 := (Real.hasDerivAt_exp ((y : ℝ) * t)).comp t hlin
  have hfun : (Real.exp ∘ fun u => (y : ℝ) * u) = fun u => Real.exp ((y : ℝ) * u) := by
    funext u
    rfl
  have hexp : HasDerivAt (fun u => Real.exp ((y : ℝ) * u))
      (Real.exp ((y : ℝ) * t) * (y : ℝ)) t := by
    simpa [hfun, mul_comm] using hexp0
  have hmul := hexp.mul (hasDerivAt_mass y t)
  have hprod : (fun u => Real.exp ((y : ℝ) * u)) * mass y =
      fun u => Real.exp ((y : ℝ) * u) * mass y u := by
    funext u
    rfl
  have hshifted := hmul.congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq hprod)
  have hderiv :
      Real.exp ((y : ℝ) * t) * (y : ℝ) * mass y t +
        Real.exp ((y : ℝ) * t) * -((y : ℝ) * eta t ^ (y - 1) * etaDeriv t) =
      Real.exp ((y : ℝ) * t) * (y : ℝ) * phi y t := by
    have hode := mass_ode y hy t
    linear_combination Real.exp ((y : ℝ) * t) * hode
  exact hshifted.congr_deriv hderiv

lemma continuous_halfExp : Continuous (fun u : ℝ => Real.exp (-u / 2)) :=
  Real.continuous_exp.comp (continuous_id.neg.div_const 2)

lemma continuous_eta : Continuous eta := by
  unfold eta
  exact continuous_halfExp.mul (continuous_const.sub continuous_halfExp)

lemma continuous_phi (y : ℕ) : Continuous (phi y) := by
  unfold phi
  exact continuous_const.sub ((continuous_eta.pow (y - 1)).mul continuous_halfExp)

lemma sqrt_one_sub_eta {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (1 - eta u) = 1 - Real.exp (-u / 2) := by
  have hdelta : 1 - eta u = (1 - Real.exp (-u / 2)) ^ 2 := by
    unfold eta
    ring
  have hnn : 0 ≤ 1 - Real.exp (-u / 2) := by linarith [exp_half_le_one hu]
  rw [hdelta, Real.sqrt_sq hnn]

lemma offspring_series (y : ℕ) (hy : 0 < y) (u : ℝ) (hu : 0 ≤ u) :
    ∑' j, sibuya j * mass ((y - 1) + j) u = phi y u := by
  have he := eta_bounds hu
  have hmass : ∀ j, mass ((y - 1) + j) u = 1 - eta u ^ (y - 1) * eta u ^ j := by
    intro j
    simp [mass, pow_add]
  let c : ℝ := eta u ^ (y - 1)
  have hc0 : 0 ≤ c := pow_nonneg he.1.le _
  have hc1 : c ≤ 1 := pow_le_one₀ he.1.le he.2
  have hg : Summable (fun j => sibuya j * (c * eta u ^ j)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ sibuya_summable
    · intro j
      exact mul_nonneg (sibuya_nonneg j) (mul_nonneg hc0 (pow_nonneg he.1.le j))
    · intro j
      have hpow : eta u ^ j ≤ 1 := pow_le_one₀ he.1.le he.2
      have hprod : c * eta u ^ j ≤ 1 := mul_le_one₀ hc1 (pow_nonneg he.1.le j) hpow
      simpa using mul_le_mul_of_nonneg_left hprod (sibuya_nonneg j)
  have hdiff : Summable (fun j => sibuya j - sibuya j * (c * eta u ^ j)) :=
    sibuya_summable.sub hg
  have hsplit := sibuya_summable.tsum_sub hg
  have hcomm : ∀ j, sibuya j * (c * eta u ^ j) = c * (sibuya j * eta u ^ j) := by
    intro j
    ring
  have hscaled : ∑' j, sibuya j * (c * eta u ^ j) = c * ∑' j, sibuya j * eta u ^ j := by
    simp_rw [hcomm, tsum_mul_left]
  have hpgf : ∑' j, sibuya j * eta u ^ j = 1 - Real.sqrt (1 - eta u) :=
    sibuya_pgf he.1.le he.2
  have hsqrt : 1 - Real.sqrt (1 - eta u) = Real.exp (-u / 2) := by
    linarith [sqrt_one_sub_eta hu]
  have hrewrite : ∀ j, 1 - eta u ^ (y - 1) * eta u ^ j = 1 - c * eta u ^ j := by
    intro j
    simp [c]
  have hterm : ∀ j, sibuya j * (1 - c * eta u ^ j) =
      sibuya j - sibuya j * (c * eta u ^ j) := by
    intro j
    ring
  calc
    ∑' j, sibuya j * mass ((y - 1) + j) u
        = ∑' j, sibuya j * (1 - c * eta u ^ j) := by simp_rw [hmass, hrewrite]
    _ = ∑' j, (sibuya j - sibuya j * (c * eta u ^ j)) := by simp_rw [hterm]
    _ = ∑' j, sibuya j - ∑' j, sibuya j * (c * eta u ^ j) := hsplit
    _ = 1 - c * ∑' j, sibuya j * eta u ^ j := by rw [sibuya_tsum, hscaled]
    _ = 1 - c * Real.exp (-u / 2) := by rw [hpgf, hsqrt]
    _ = phi y u := by unfold phi c; ring

lemma mass_as_integral (y : ℕ) (hy : 0 < y) {T : ℝ} (hT : 0 ≤ T) :
    mass y T = ∫ s in (0 : ℝ)..T, ↑y * Real.exp (-(↑y * s)) * phi y (T - s) := by
  let F : ℝ → ℝ := fun u => Real.exp ((y : ℝ) * u) * mass y u
  let F' : ℝ → ℝ := fun u => Real.exp ((y : ℝ) * u) * (y : ℝ) * phi y u
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) T, HasDerivAt F (F' u) u := by
    intro u _
    simpa [F, F'] using hasDerivAt_factor y hy u
  have hcont : Continuous F' := by
    have hmul : Continuous ((fun u => Real.exp ((y : ℝ) * u)) * fun u => (y : ℝ) * phi y u) :=
      (Real.continuous_exp.comp (continuous_id.const_mul (y : ℝ))).mul
        ((continuous_phi y).const_mul (y : ℝ))
    exact (continuous_congr (fun u => by unfold F'; simp [Pi.mul_apply, mul_assoc])).mp hmul
  have hint : IntervalIntegrable F' volume 0 T := hcont.intervalIntegrable 0 T
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have heta0 : eta 0 = 1 := by
    unfold eta
    rw [show (-0 : ℝ) / 2 = 0 by norm_num, Real.exp_zero]
    norm_num
  have hmass0 : mass y 0 = 0 := by
    simp [mass, heta0, one_pow]
  have hF0 : F 0 = 0 := by
    simp [F, hmass0, Real.exp_zero]
  have hFT : F T = Real.exp ((y : ℝ) * T) * mass y T := rfl
  have hne : Real.exp ((y : ℝ) * T) ≠ 0 := Real.exp_ne_zero _
  have hcancel : Real.exp (-((y : ℝ) * T)) * (Real.exp ((y : ℝ) * T) * mass y T) = mass y T := by
    rw [← mul_assoc, ← Real.exp_add]
    have hzero : -((y : ℝ) * T) + (y : ℝ) * T = 0 := by ring
    rw [hzero, Real.exp_zero, one_mul]
  have hcomp : ∫ s in (0 : ℝ)..T, Real.exp ((y : ℝ) * (T - s)) * (y : ℝ) * phi y (T - s) =
      ∫ u in (0 : ℝ)..T, F' u := by
    simpa [F'] using
      intervalIntegral.integral_comp_sub_left
        (fun u => Real.exp ((y : ℝ) * u) * (y : ℝ) * phi y u) T (a := 0) (b := T)
  have hint_eq : ∫ u in (0 : ℝ)..T, F' u = Real.exp ((y : ℝ) * T) * mass y T := by
    rw [heq, hF0, hFT, sub_zero]
  have hmass : mass y T = Real.exp (-((y : ℝ) * T)) * ∫ u in (0 : ℝ)..T, F' u := by
    rw [hint_eq]
    rw [← mul_assoc, ← Real.exp_add]
    have hzero : -((y : ℝ) * T) + (y : ℝ) * T = 0 := by ring
    rw [hzero, Real.exp_zero, one_mul]
  rw [hmass, ← hcomp, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro s _
  have hexp : Real.exp (-((y : ℝ) * T)) * Real.exp ((y : ℝ) * (T - s)) =
      Real.exp (-((y : ℝ) * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-((y : ℝ) * T)) * (Real.exp ((y : ℝ) * (T - s)) * (y : ℝ) * phi y (T - s))
        = (Real.exp (-((y : ℝ) * T)) * Real.exp ((y : ℝ) * (T - s))) * (y : ℝ) *
            phi y (T - s) := by ring
    _ = Real.exp (-((y : ℝ) * s)) * (y : ℝ) * phi y (T - s) := by rw [hexp]
    _ = (y : ℝ) * Real.exp (-((y : ℝ) * s)) * phi y (T - s) := by ring

lemma defect_bound : ∀ y : ℕ, ∀ t : ℝ≥0, ∀ k : ℕ, |defect y t k| ≤ 1 := by
  intro y t k
  have hb := mass_bounds y (NNReal.coe_nonneg t)
  rw [defect, abs_of_nonneg hb.1]
  exact hb.2

lemma defect_zero : ∀ t : ℝ≥0, ∀ k : ℕ, defect 0 t k = 0 := by
  intro t k
  simp [defect, mass, pow_zero]

lemma mass_one_ne : mass 1 1 ≠ 0 := by
  have he : Real.exp (-(1 : ℝ) / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hform : eta 1 = 1 - (1 - Real.exp (-(1 : ℝ) / 2)) ^ 2 := by
    unfold eta
    ring
  have hlt : eta 1 < 1 := by
    rw [hform]
    have hpos : 0 < 1 - Real.exp (-(1 : ℝ) / 2) := by linarith
    nlinarith
  simp [mass, pow_one]
  linarith

lemma defect_equation (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    IntervalIntegrable
        (fun s : ℝ =>
          ((1 : ℝ) * (y : ℝ)) * Real.exp (-(((1 : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspringCounter j).toReal *
              defect ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k)
        volume 0 (t : ℝ) ∧
      defect y t k =
        ∫ s in (0 : ℝ)..(t : ℝ),
          ((1 : ℝ) * (y : ℝ)) * Real.exp (-(((1 : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspringCounter j).toReal *
              defect ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k := by
  have hT : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
  let closed : ℝ → ℝ := fun s => ↑y * Real.exp (-(↑y * s)) * phi y ((t : ℝ) - s)
  have hclosed_cont : Continuous closed := by
    have hexp : Continuous (fun s => Real.exp (-((y : ℝ) * s))) :=
      Real.continuous_exp.comp ((continuous_id.const_mul (y : ℝ)).neg)
    have hphi : Continuous (fun s => phi y ((t : ℝ) - s)) :=
      (continuous_phi y).comp (continuous_const.sub continuous_id)
    have hmul : Continuous
        ((fun s => (y : ℝ) * Real.exp (-((y : ℝ) * s))) * fun s => phi y ((t : ℝ) - s)) :=
      (hexp.const_mul (y : ℝ)).mul hphi
    exact (continuous_congr (fun s => by unfold closed; simp [Pi.mul_apply])).mp hmul
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ),
      ((1 : ℝ) * (y : ℝ)) * Real.exp (-(((1 : ℝ) * (y : ℝ)) * s)) *
        ∑' j : ℕ, (offspringCounter j).toReal *
          defect ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k =
      closed s := by
    intro s hs
    have hs0 : 0 ≤ (t : ℝ) - s := by linarith [hs.2]
    have hcoe : ((Real.toNNReal ((t : ℝ) - s) : ℝ≥0) : ℝ) = (t : ℝ) - s :=
      Real.coe_toNNReal ((t : ℝ) - s) hs0
    have htoReal : ∀ j, (offspringCounter j).toReal = sibuya j := by
      intro j
      change (ENNReal.ofReal (sibuya j)).toReal = sibuya j
      exact ENNReal.toReal_ofReal (sibuya_nonneg j)
    simp only [defect, hcoe, htoReal, one_mul]
    rw [offspring_series y hy ((t : ℝ) - s) hs0]
  have hcont_int : IntervalIntegrable closed volume 0 (t : ℝ) :=
    hclosed_cont.intervalIntegrable 0 (t : ℝ)
  have heqOn : Set.EqOn
      (fun s : ℝ =>
        ((1 : ℝ) * (y : ℝ)) * Real.exp (-(((1 : ℝ) * (y : ℝ)) * s)) *
          ∑' j : ℕ, (offspringCounter j).toReal *
            defect ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k)
      closed (Set.uIoc 0 (t : ℝ)) := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := by
      rcases (Set.mem_uIoc).mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_of_lt h1, h2⟩
      · exact absurd (lt_of_lt_of_le h1 h2) (not_lt.mpr hT)
    exact hpoint s hsIcc
  have heqIcc : Set.EqOn
      (fun s : ℝ =>
        ((1 : ℝ) * (y : ℝ)) * Real.exp (-(((1 : ℝ) * (y : ℝ)) * s)) *
          ∑' j : ℕ, (offspringCounter j).toReal *
            defect ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k)
      closed (Set.uIcc 0 (t : ℝ)) := by
    rw [Set.uIcc_of_le hT]
    intro s hs
    exact hpoint s hs
  refine ⟨?_, ?_⟩
  · exact (intervalIntegrable_congr heqOn).mpr hcont_int
  · rw [intervalIntegral.integral_congr heqIcc]
    have hmass := mass_as_integral y hy hT
    have hclosed_int : ∫ s in (0 : ℝ)..(t : ℝ), closed s =
        ∫ s in (0 : ℝ)..(t : ℝ), ↑y * Real.exp (-(↑y * s)) * phi y ((t : ℝ) - s) := rfl
    rw [hclosed_int, ← hmass]
    rfl

set_option linter.unusedVariables false in
theorem solution :
    ¬ (∀ (rate : ℝ) (hrate : 0 < rate) (offspring : PMF ℕ)
        (h : ℕ → ℝ≥0 → ℕ → ℝ)
        (hBound : ∀ y : ℕ, ∀ t : ℝ≥0, ∀ k : ℕ, |h y t k| ≤ 1)
        (hZero : ∀ t : ℝ≥0, ∀ k : ℕ, h 0 t k = 0)
        (hEq : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
          IntervalIntegrable
              (fun s : ℝ =>
                (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
                  ∑' j : ℕ, (offspring j).toReal *
                    h ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k)
              volume 0 (t : ℝ) ∧
            h y t k =
              ∫ s in (0 : ℝ)..(t : ℝ),
                (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
                  ∑' j : ℕ, (offspring j).toReal *
                    h ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k),
        ∀ y : ℕ, ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ, h y t k = 0) := by
  intro H
  have hfalse := H 1 (by norm_num) offspringCounter defect defect_bound defect_zero
    (by
      intro y hy t ht k
      simpa using defect_equation y hy t ht k)
    1 (1 : ℝ≥0) (by norm_num) 0
  exact mass_one_ne (by simpa [defect] using hfalse)
