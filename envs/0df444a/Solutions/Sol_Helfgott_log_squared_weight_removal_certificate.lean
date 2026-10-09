-- Prove2me | solution 1 for Helfgott.log_squared_weight_removal_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T19:38:48.523143+00:00
-- url     : https://prove2.me/submissions/1c000edc-c47b-4639-b7d8-b61429eb0b55

import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma log_weight_sum_zero_remove (c : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 0 N, c d * Real.log (d : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 N, c d * Real.log (d : ℝ) ^ 2 := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, Real.log_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add]
  rfl

lemma log_weight_sum_Ioc_difference (c : ℕ → ℝ) (A N : ℕ) (hAN : A ≤ N) :
    (∑ d ∈ Finset.Ioc A N, c d) =
      (∑ d ∈ Finset.Icc 1 N, c d) - ∑ d ∈ Finset.Icc 1 A, c d := by
  have h := Finset.sum_Ioc_consecutive c (Nat.zero_le A) hAN
  simp only [← Finset.Icc_succ_left_eq_Ioc, Order.succ_eq_add_one, zero_add] at h
  simp only [← Finset.Icc_succ_left_eq_Ioc, Order.succ_eq_add_one] at ⊢
  linarith

lemma hasDerivAt_log_inv_sq (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => (Real.log t ^ 2)⁻¹)
      (-(2 / (t * Real.log t ^ 3))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := ((Real.hasDerivAt_log ht0).pow 2).inv (pow_ne_zero 2 hl0)
  convert hd using 1
  all_goals first | rfl | (simp only [Pi.pow_apply]; field_simp [hl0, ht0]; ring)

lemma log_weight_deriv_continuous (a x : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => -(2 / (t * Real.log t ^ 3))) (Set.Icc a x) := by
  have ht0 : ∀ t ∈ Set.Icc a x, t ≠ 0 := by
    intro t ht; linarith [ht.1]
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => ht0 t ht)
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht; exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  exact (continuousOn_const.div (continuousOn_id.mul (hl.pow 3))
    (fun t ht => mul_ne_zero (ht0 t ht) (pow_ne_zero 3 (hl0 t ht)))).neg

lemma log_weight_kernel_intervalIntegrable (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x := by
  have hf : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 3)⁻¹) (Set.Icc a x) := by
    have ht0 : ∀ t ∈ Set.Icc a x, t ≠ 0 := by intro t ht; linarith [ht.1]
    have hl : ContinuousOn Real.log (Set.Icc a x) :=
      Real.continuousOn_log.mono (fun t ht => ht0 t ht)
    exact (continuousOn_id.mul (hl.pow 3)).inv₀ (fun t ht =>
      mul_ne_zero (ht0 t ht) (pow_ne_zero 3 (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
  have h := integrableOn_mul_sum_Icc (fun d => c d * Real.log (d : ℝ) ^ 2)
    (by linarith : 0 ≤ a) hf.integrableOn_Icc (m := 1)
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem log_squared_weight_removal_identity (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) := by
  have hd : ∀ t ∈ Set.Icc a x,
      DifferentiableAt ℝ (fun t : ℝ => (Real.log t ^ 2)⁻¹) t := by
    intro t ht; exact (hasDerivAt_log_inv_sq t (lt_of_lt_of_le ha ht.1)).differentiableAt
  have hdv : ∀ t ∈ Set.Icc a x,
      deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹) t = -(2 / (t * Real.log t ^ 3)) := by
    intro t ht; exact (hasDerivAt_log_inv_sq t (lt_of_lt_of_le ha ht.1)).deriv
  have hi : IntegrableOn (deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹)) (Set.Icc a x) :=
    ((log_weight_deriv_continuous a x ha).integrableOn_Icc).congr_fun
      (fun t ht => (hdv t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun d => c d * Real.log (d : ℝ) ^ 2) (by linarith : 0 ≤ a) hax hd hi
  simp_rw [log_weight_sum_zero_remove c] at h
  have hleft :
      (∑ d ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊,
        (Real.log (d : ℝ) ^ 2)⁻¹ * (c d * Real.log (d : ℝ) ^ 2)) =
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) - ∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d := by
    rw [← log_weight_sum_Ioc_difference c _ _ (Nat.floor_le_floor hax)]
    apply Finset.sum_congr rfl
    intro d hd
    have hda : a < (d : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ a)).mp (Finset.mem_Ioc.mp hd).1
    have hl : Real.log (d : ℝ) ≠ 0 := (Real.log_pos (lt_trans ha hda)).ne'
    field_simp
  rw [hleft] at h
  have hint :
      (∫ t in Set.Ioc a x, deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹) t *
        ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) =
      -(2 * ∫ t in a..x,
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
          (t * Real.log t ^ 3)) := by
    rw [← intervalIntegral.integral_of_le hax]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    dsimp only
    rw [hdv t ht]
    ring
  rw [hint] at h
  simp only [div_eq_mul_inv, mul_comm ((Real.log _) ^ 2)⁻¹] at h ⊢
  linarith

lemma log_squared_weight_removal_bound (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by
  let M : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d
  let W : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2
  have hden : ∀ t ∈ Set.Icc a x, 0 < t * Real.log t ^ 3 := by
    intro t ht
    exact mul_pos (by linarith [ht.1]) (pow_pos (Real.log_pos (lt_of_lt_of_le ha ht.1)) 3)
  have hrem : |∫ t in a..x, W t / (t * Real.log t ^ 3)| ≤
      ∫ t in a..x, |W t| / (t * Real.log t ^ 3) := by
    calc
      _ ≤ ∫ t in a..x, |W t / (t * Real.log t ^ 3)| :=
        intervalIntegral.abs_integral_le_integral_abs hax
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hax] at ht
        dsimp only
        rw [abs_div, abs_of_pos (hden t ht)]
  have hid := log_squared_weight_removal_identity c a x ha hax
  change M x = (M a - W a / Real.log a ^ 2) + W x / Real.log x ^ 2 +
    2 * ∫ t in a..x, W t / (t * Real.log t ^ 3) at hid
  change |M x| ≤ |M a - W a / Real.log a ^ 2| + |W x| / Real.log x ^ 2 +
    2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3)
  rw [hid]
  have h1 := abs_add_le (M a - W a / Real.log a ^ 2) (W x / Real.log x ^ 2)
  have h2 := abs_add_le ((M a - W a / Real.log a ^ 2) + W x / Real.log x ^ 2)
    (2 * ∫ t in a..x, W t / (t * Real.log t ^ 3))
  have hW : |W x / Real.log x ^ 2| = |W x| / Real.log x ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos (Real.log_pos (lt_of_lt_of_le ha hax)) 2)]
  have h3 : |2 * ∫ t in a..x, W t / (t * Real.log t ^ 3)| ≤
      2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hrem (by norm_num)
  rw [hW] at h1
  linarith

theorem log_squared_weight_removal_certificate_complete (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x ∧
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) ∧
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by
  exact ⟨log_weight_kernel_intervalIntegrable c a x ha hax,
    log_squared_weight_removal_identity c a x ha hax,
    log_squared_weight_removal_bound c a x ha hax⟩

end Helfgott
end

open Helfgott Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

theorem solution  (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x ∧
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) ∧
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := Helfgott.log_squared_weight_removal_certificate_complete c a x ha hax

#print axioms solution
