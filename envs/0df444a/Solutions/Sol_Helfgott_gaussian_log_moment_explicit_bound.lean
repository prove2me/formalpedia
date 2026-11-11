-- Prove2me | solution 1 for Helfgott.gaussian_log_moment_explicit_bound
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T00:47:05.662216+00:00
-- url     : https://prove2.me/submissions/ed327fa1-1488-4ad1-92d6-26ed45869de2

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open MeasureTheory Finset
open scoped BigOperators

private lemma continuous_pow_mul_log (n : ℕ) (hn : 0 < n) :
    Continuous (fun t : ℝ => t ^ n * Real.log t) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h : Continuous (fun t : ℝ => t ^ k * (t * Real.log t)) :=
    (continuous_id.pow k).mul Real.continuous_mul_log
  simpa only [pow_succ, mul_assoc] using h

private lemma integral_pow_neg_log (n : ℕ) (hn : 0 < n) :
    (∫ t in (0 : ℝ)..1, t ^ n * (-Real.log t)) = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hc : Continuous (fun t : ℝ => -(t ^ n * Real.log t)) :=
    (continuous_pow_mul_log n hn).neg
  have hci : IntervalIntegrable (fun t : ℝ => t ^ n * (-Real.log t)) volume 0 1 := by
    simpa only [mul_neg, Pi.neg_apply] using hc.intervalIntegrable 0 1
  have hnp : (n : ℝ) + 1 ≠ 0 := by positivity
  have hcont : Continuous (fun t : ℝ =>
      -(t ^ (n + 1) * Real.log t) / ((n : ℝ) + 1) +
        t ^ (n + 1) / ((n : ℝ) + 1) ^ 2) :=
    (((continuous_pow_mul_log (n + 1) (by omega)).neg).div_const _).add
      ((continuous_id.pow (n + 1)).div_const _)
  have hd (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ =>
        -(t ^ (n + 1) * Real.log t) / ((n : ℝ) + 1) +
          t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
        (t ^ n * (-Real.log t)) t := by
    convert! (((((hasDerivAt_id t).pow (n + 1)).mul
      (Real.hasDerivAt_log (ne_of_gt ht.1))).neg).div_const ((n : ℝ) + 1)).add
      (((hasDerivAt_id t).pow (n + 1)).div_const (((n : ℝ) + 1) ^ 2)) using 1
    all_goals try dsimp
    all_goals try simp only [Nat.cast_add, Nat.cast_one, mul_one, pow_succ]
    all_goals try field_simp [ne_of_gt ht.1, hnp]
    all_goals first | rfl | ring
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn hd hci
  simpa using heq

private noncomputable def momentPolynomial (t : ℝ) : ℝ :=
  (∑ m ∈ range 7, ((-1 : ℝ) ^ m / (2 ^ m * (m.factorial : ℝ))) *
    (t ^ (2 * m + 2) * (-Real.log t))) +
      (1 / 564480 : ℝ) * (t ^ 16 * (-Real.log t))

private lemma gaussian_le_polynomial (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t ^ 2 * Real.exp (-(t ^ 2) / 2) * (-Real.log t) ≤ momentPolynomial t := by
  have ht2 : t ^ 2 ≤ 1 := by
    nlinarith [ht.1, ht.2, mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have habs : |-(t ^ 2) / 2| = t ^ 2 / 2 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg t])]
    ring
  have he := (abs_sub_le_iff.mp (Real.exp_bound
    (x := -(t ^ 2) / 2) (by rw [habs]; nlinarith) (n := 7) (by norm_num))).1
  rw [habs] at he
  have hl : 0 ≤ -Real.log t := by
    have := Real.log_nonpos ht.1 ht.2
    linarith
  have hmul := mul_le_mul_of_nonneg_right he (mul_nonneg (sq_nonneg t) hl)
  unfold momentPolynomial
  norm_num [Finset.sum_range_succ, Nat.factorial] at hmul ⊢
  nlinarith only [hmul]

private lemma polynomial_integral :
    (∫ t in (0 : ℝ)..1, momentPolynomial t) ≤ (46713 / 500000 : ℝ) := by
  have hi (n : ℕ) (hn : 0 < n) :
      IntervalIntegrable (fun t : ℝ => t ^ n * (-Real.log t)) volume 0 1 := by
    have h : Continuous (fun t : ℝ => -(t ^ n * Real.log t)) :=
      (continuous_pow_mul_log n hn).neg
    simpa only [mul_neg] using h.intervalIntegrable 0 1
  unfold momentPolynomial
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul]
      have h (m : ℕ) : (∫ t in (0 : ℝ)..1, t ^ (2 * m + 2) * (-Real.log t)) =
          1 / (((2 * m + 2 : ℕ) : ℝ) + 1) ^ 2 := integral_pow_neg_log _ (by omega)
      simp_rw [h]
      rw [integral_pow_neg_log 16 (by norm_num)]
      norm_num [Finset.sum_range_succ, Nat.factorial]
    · intro m hm
      exact (hi _ (by omega)).const_mul _
  · have h : IntervalIntegrable
        (∑ m ∈ range 7, fun t : ℝ => ((-1 : ℝ) ^ m / (2 ^ m * (m.factorial : ℝ))) *
          (t ^ (2 * m + 2) * (-Real.log t))) volume 0 1 :=
      IntervalIntegrable.sum _ (fun m hm => (hi (2 * m + 2) (by omega)).const_mul _)
    convert h using 1
    ext t
    simp only [Finset.sum_apply]
  · exact (hi 16 (by norm_num)).const_mul _

private lemma gaussian_log_continuous :
    Continuous (fun t : ℝ => t ^ 2 * Real.exp (-(t ^ 2) / 2) * (-Real.log t)) := by
  convert ((continuous_pow_mul_log 2 (by norm_num)).neg).mul
    (Real.continuous_exp.comp (((continuous_id.pow 2).neg).div_const 2)) using 1
  ext t
  dsimp
  ring

private lemma full_moment_upper :
    (∫ t in (0 : ℝ)..1, t ^ 2 * Real.exp (-(t ^ 2) / 2) * (-Real.log t)) ≤
      (46713 / 500000 : ℝ) := by
  have hp : Continuous momentPolynomial := by
    unfold momentPolynomial
    apply Continuous.add
    · apply continuous_finsetSum
      intro m hm
      have h : Continuous (fun t : ℝ => -(t ^ (2 * m + 2) * Real.log t)) :=
        (continuous_pow_mul_log (2 * m + 2) (by omega)).neg
      exact continuous_const.mul (by simpa only [mul_neg] using h)
    · have h : Continuous (fun t : ℝ => -(t ^ 16 * Real.log t)) :=
        (continuous_pow_mul_log 16 (by norm_num)).neg
      exact continuous_const.mul (by simpa only [mul_neg] using h)
  exact (intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (gaussian_log_continuous.intervalIntegrable 0 1) (hp.intervalIntegrable 0 1)
    gaussian_le_polynomial).trans polynomial_integral

-- This includes a = 0 and a = 1, and supplies the normalized constant in (7.31).
theorem solution (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ t in a..1, t ^ 2 * Real.exp (-(t ^ 2) / 2) * (-Real.log t)) ≤
      (46713 / 500000 : ℝ) ∧
    (∫ t in a..1, t ^ 2 * Real.exp (-(t ^ 2) / 2) * (-Real.log t)) /
      Real.sqrt (Real.pi / 2) ≤ (1491 / 20000 : ℝ) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t : ℝ => t ^ 2 * Real.exp (-(t ^ 2) / 2) * (-Real.log t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (mul_nonneg (sq_nonneg t) (Real.exp_pos _).le)
      (neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2))
  have hupper := (intervalIntegral.integral_mono_interval ha0 ha1 le_rfl hnonneg
    (gaussian_log_continuous.intervalIntegrable 0 1)).trans full_moment_upper
  refine ⟨hupper, ?_⟩
  have hpi : 0 < Real.pi / 2 := by positivity
  have hsqrt : (3133 / 2500 : ℝ) ≤ Real.sqrt (Real.pi / 2) := by
    have hsq := Real.sq_sqrt hpi.le
    have hpos := Real.sqrt_nonneg (Real.pi / 2)
    nlinarith [Real.pi_gt_d4]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hpi)).2
  nlinarith
