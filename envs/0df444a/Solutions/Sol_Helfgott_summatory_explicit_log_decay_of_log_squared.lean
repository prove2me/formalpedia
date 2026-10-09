-- Prove2me | solution 1 for Helfgott.summatory_explicit_log_decay_of_log_squared
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:57:17.944985+00:00
-- url     : https://prove2.me/submissions/a6e6e9e4-76ba-4dbe-8ea2-8f96ee1754e8

import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

theorem log_squared_weight_removal_certificate (c : ℕ → ℝ) (a x : ℝ)
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

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma hasDerivAt_log_weight_majorant (α t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => α * u / Real.log u ^ 2)
      (α * (Real.log t - 2) / Real.log t ^ 3) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := ((hasDerivAt_id t).const_mul α).div
    ((Real.hasDerivAt_log ht0).pow 2) (pow_ne_zero 2 hl0)
  convert hd using 1 <;>
    (try simp only [Pi.div_apply, Pi.pow_apply, id_eq, mul_one, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]) <;>
    first | rfl | (field_simp [hl0, ht0] <;> ring)

lemma log_weight_envelope_integral_bound (α β a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hβα : 2 * α ≤ β) :
    (∫ t in a..x, (α * Real.log t - β) / Real.log t ^ 3) ≤
      α * x / Real.log x ^ 2 - α * a / Real.log a ^ 2 := by
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => by
      change t ≠ 0
      linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht
    exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  have hcont : ContinuousOn (fun t : ℝ =>
      (α * Real.log t - β) / Real.log t ^ 3) (Set.Icc a x) :=
    ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 3)
      (fun t ht => pow_ne_zero 3 (hl0 t ht))
  have hdcont : ContinuousOn (fun t : ℝ =>
      α * (Real.log t - 2) / Real.log t ^ 3) (Set.Icc a x) :=
    (continuousOn_const.mul (hl.sub continuousOn_const)).div (hl.pow 3)
      (fun t ht => pow_ne_zero 3 (hl0 t ht))
  have hdi : IntervalIntegrable (fun t : ℝ =>
      α * (Real.log t - 2) / Real.log t ^ 3) volume a x :=
    hdcont.intervalIntegrable_of_Icc hax
  have hderiv : ∀ t ∈ Set.uIcc a x,
      HasDerivAt (fun u : ℝ => α * u / Real.log u ^ 2)
        (α * (Real.log t - 2) / Real.log t ^ 3) t := by
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    exact hasDerivAt_log_weight_majorant α t (lt_of_lt_of_le ha ht.1)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hdi
  rw [← hi]
  apply intervalIntegral.integral_mono_on hax (hcont.intervalIntegrable_of_Icc hax) hdi
  intro t ht
  apply (div_le_div_iff_of_pos_right
    (pow_pos (Real.log_pos (lt_of_lt_of_le ha ht.1)) 3)).mpr
  nlinarith

theorem log_squared_weight_removal_quantitative (c : ℕ → ℝ) (α β a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hβα : 2 * α ≤ β)
    (hstart :
      |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, c n * Real.log (n : ℝ) ^ 2) / Real.log a ^ 2| ≤
          2 * α * a / Real.log a ^ 2)
    (hW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| ≤
        t * (α * Real.log t - β)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
      x * (α * Real.log x - (β - 2 * α)) / Real.log x ^ 2 := by
  let W : ℝ → ℝ := fun t => ∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2
  have hden : ∀ t ∈ Set.Icc a x, 0 < t * Real.log t ^ 3 := by
    intro t ht
    exact mul_pos (by linarith [ht.1])
      (pow_pos (Real.log_pos (lt_of_lt_of_le ha ht.1)) 3)
  have hcont : ContinuousOn (fun t : ℝ =>
      (α * Real.log t - β) / Real.log t ^ 3) (Set.Icc a x) := by
    have hl : ContinuousOn Real.log (Set.Icc a x) :=
      Real.continuousOn_log.mono (fun t ht => by
        change t ≠ 0
        linarith [ht.1])
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 3)
      (fun t ht => pow_ne_zero 3 (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne')
  have habs : IntervalIntegrable (fun t : ℝ =>
      |W t| / (t * Real.log t ^ 3)) volume a x := by
    apply (intervalIntegrable_congr (g := fun t : ℝ =>
      |W t / (t * Real.log t ^ 3)|) ?_).mpr
    · exact (log_weight_kernel_intervalIntegrable c a x ha hax).abs
    · intro t ht
      have ht' : t ∈ Set.Icc a x := by
        rw [Set.uIoc_of_le hax] at ht
        exact ⟨ht.1.le, ht.2⟩
      change |W t| / (t * Real.log t ^ 3) = |W t / (t * Real.log t ^ 3)|
      rw [abs_div, abs_of_pos (hden t ht')]
  have himono : (∫ t in a..x, |W t| / (t * Real.log t ^ 3)) ≤
      ∫ t in a..x, (α * Real.log t - β) / Real.log t ^ 3 := by
    apply intervalIntegral.integral_mono_on hax habs
      (hcont.intervalIntegrable_of_Icc hax)
    intro t ht
    calc
      _ ≤ (t * (α * Real.log t - β)) / (t * Real.log t ^ 3) :=
        div_le_div_of_nonneg_right (hW t ht) (hden t ht).le
      _ = _ := by
        have ht0 : t ≠ 0 := by linarith [ht.1]
        field_simp
  have hi := himono.trans (log_weight_envelope_integral_bound α β a x ha hax hβα)
  have hWx : |W x| / Real.log x ^ 2 ≤
      x * (α * Real.log x - β) / Real.log x ^ 2 :=
    div_le_div_of_nonneg_right (hW x ⟨hax, le_rfl⟩) (sq_nonneg _)
  have hb := log_squared_weight_removal_bound c a x ha hax
  change |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
    |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) - W a / Real.log a ^ 2| +
      |W x| / Real.log x ^ 2 +
      2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3) at hb
  have hcancel :
      2 * α * a / Real.log a ^ 2 + x * (α * Real.log x - β) / Real.log x ^ 2 +
        2 * (α * x / Real.log x ^ 2 - α * a / Real.log a ^ 2) =
          x * (α * Real.log x - (β - 2 * α)) / Real.log x ^ 2 := by ring
  rw [← hcancel]
  dsimp only [W] at *
  linarith

theorem summatory_explicit_log_decay_of_log_squared_complete (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x)
    (hstart :
      |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, c n * Real.log (n : ℝ) ^ 2) / Real.log a ^ 2| ≤
          13 * a / (500 * Real.log a ^ 2))
    (hW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| ≤
        t * ((13 / 1000 : ℝ) * Real.log t - 18 / 125)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
      x * ((13 / 1000 : ℝ) * Real.log x - 59 / 500) / Real.log x ^ 2 := by
  have hbase :
      |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, c n * Real.log (n : ℝ) ^ 2) / Real.log a ^ 2| ≤
          2 * (13 / 1000 : ℝ) * a / Real.log a ^ 2 := by
    convert hstart using 1 <;> ring
  have h := log_squared_weight_removal_quantitative c (13 / 1000) (18 / 125)
    a x ha hax (by norm_num) hbase hW
  convert h using 1 <;> ring

end Helfgott
end

open Helfgott Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

theorem solution  (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x)
    (hstart :
      |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, c n * Real.log (n : ℝ) ^ 2) / Real.log a ^ 2| ≤
          13 * a / (500 * Real.log a ^ 2))
    (hW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| ≤
        t * ((13 / 1000 : ℝ) * Real.log t - 18 / 125)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
      x * ((13 / 1000 : ℝ) * Real.log x - 59 / 500) / Real.log x ^ 2 := Helfgott.summatory_explicit_log_decay_of_log_squared_complete c a x ha hax hstart hW
#print axioms solution
