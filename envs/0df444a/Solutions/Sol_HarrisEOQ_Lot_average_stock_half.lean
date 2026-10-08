-- Prove2me | solution 1 for HarrisEOQ.Lot.average_stock_half
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:56:30.984081+00:00
-- url     : https://prove2.me/submissions/d01f730a-0328-4733-b116-69d843cff9ba

import Mathlib
import Definitions.Def_HarrisEOQ_Lot_Setting

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace HarrisWork
open HarrisEOQ.Lot

variable {M X : ℝ}

lemma stock_nonneg (hX : 0 < X) (t : ℝ) : 0 ≤ stockLevel M X t := by
  unfold stockLevel
  exact mul_nonneg hX.le (by linarith [Int.fract_lt_one (M * t / X)])

lemma stock_le (hX : 0 < X) (t : ℝ) : stockLevel M X t ≤ X := by
  unfold stockLevel
  nlinarith [Int.fract_nonneg (M * t / X)]

lemma stock_meas : Measurable (stockLevel M X) := by
  unfold stockLevel
  exact measurable_const.mul (measurable_const.sub (measurable_fract.comp
    ((measurable_const.mul measurable_id).div_const X)))

lemma stock_periodic (hM : 0 < M) (hX : 0 < X) : Function.Periodic (stockLevel M X) (X / M) := by
  intro t
  unfold stockLevel
  have : M * (t + X / M) / X = M * t / X + 1 := by field_simp
  rw [this, Int.fract_add_one]

lemma stock_ii (hX : 0 < X) (a b : ℝ) : IntervalIntegrable (stockLevel M X) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := X) measure_Ioc_lt_top.ne
    stock_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (stock_nonneg hX t)]
  exact stock_le hX t

lemma integral_period (hM : 0 < M) (hX : 0 < X) :
    ∫ t in (0 : ℝ)..(X / M), stockLevel M X t = X * (X / M) / 2 := by
  have hp : 0 < X / M := div_pos hX hM
  rw [intervalIntegral.integral_of_le hp.le, integral_Ioc_eq_integral_Ioo]
  have : ∫ t in Set.Ioo (0 : ℝ) (X / M), stockLevel M X t =
      ∫ t in Set.Ioo (0 : ℝ) (X / M), (X - M * t) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    obtain ⟨h0, h1⟩ := ht
    have h2 : M * t / X < 1 := by
      rw [div_lt_one hX]
      have := (lt_div_iff₀ hM).1 (show t < X / M from h1) |> fun h => h
      nlinarith [mul_lt_mul_of_pos_left h1 hM, div_mul_cancel₀ X hM.ne']
    have h3 : 0 ≤ M * t / X := by positivity
    simp only [stockLevel, Int.fract_eq_self.2 ⟨h3, h2⟩]
    field_simp
  rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hp.le]
  have hc : Continuous fun t : ℝ => M * t := by fun_prop
  have hlin : ∫ x in (0 : ℝ)..(X / M), M * x = M * ((X / M) ^ 2 / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _), hlin]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp
  ring


/-- `∫₀ᵀ stock - (X/2) T`. -/
noncomputable def Dfun (M X T : ℝ) : ℝ := (∫ t in (0 : ℝ)..T, stockLevel M X t) - X / 2 * T

lemma D_shift (hM : 0 < M) (hX : 0 < X) (s : ℝ) : Dfun M X (s + X / M) = Dfun M X s := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (stock_ii (M := M) hX 0 s)
    (stock_ii (M := M) hX s (s + X / M))
  have h2 := (stock_periodic hM hX).intervalIntegral_add_eq s 0
  rw [zero_add, integral_period hM hX] at h2
  unfold Dfun
  rw [← h1, h2]
  field_simp
  ring

lemma D_shift_nat (hM : 0 < M) (hX : 0 < X) (s : ℝ) (n : ℕ) :
    Dfun M X (s + n * (X / M)) = Dfun M X s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : s + ((n + 1 : ℕ) : ℝ) * (X / M) = (s + n * (X / M)) + X / M := by push_cast; ring
    rw [this, D_shift hM hX, ih]

lemma D_small (hX : 0 < X) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ X / M) (hM : 0 < M) :
    |Dfun M X u| ≤ 2 * X * (X / M) := by
  have hp : 0 < X / M := div_pos hX hM
  have hI : |∫ t in (0 : ℝ)..u, stockLevel M X t| ≤ X * u := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u)
      (f := stockLevel M X) (C := X) (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (stock_nonneg hX t)]; exact stock_le hX t)
    simpa [abs_of_nonneg h0] using this
  unfold Dfun
  calc |(∫ t in (0 : ℝ)..u, stockLevel M X t) - X / 2 * u|
      ≤ |∫ t in (0 : ℝ)..u, stockLevel M X t| + |X / 2 * u| := abs_sub _ _
    _ ≤ X * u + X / 2 * u := by
        gcongr
        rw [abs_of_nonneg (by positivity)]
    _ ≤ 2 * X * (X / M) := by nlinarith

theorem average_stock_half (M X : ℝ) (hM : 0 < M) (hX : 0 < X) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, stockLevel M X t) atTop (𝓝 (X / 2)) := by
  have hp0 : 0 < X / M := div_pos hX hM
  have hbound : ∀ T : ℝ, 0 ≤ T → |Dfun M X T| ≤ 2 * X * (X / M) := by
    intro T hT
    set p := X / M with hp
    have hn1 : (⌊T / p⌋₊ : ℝ) * p ≤ T := (le_div_iff₀ hp0).1 (Nat.floor_le (div_nonneg hT hp0.le))
    have hn2 : T < ((⌊T / p⌋₊ : ℝ) + 1) * p := (div_lt_iff₀ hp0).1 (Nat.lt_floor_add_one _)
    have hu : T = (T - ⌊T / p⌋₊ * p) + ⌊T / p⌋₊ * (X / M) := by rw [← hp]; ring
    rw [hu, D_shift_nat hM hX]
    exact D_small hX (by linarith) (by linarith) hM
  have hlim : Tendsto (fun T : ℝ => ((1 / T) * ∫ t in (0 : ℝ)..T, stockLevel M X t) - X / 2)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_nhds (x := 2 * X * (X / M)).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with T hT
    have : (1 / T) * (∫ t in (0 : ℝ)..T, stockLevel M X t) - X / 2 = Dfun M X T / T := by
      unfold Dfun; field_simp
    rw [this, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT, id]
    exact div_le_div_of_nonneg_right (hbound T hT.le) hT.le
  simpa using hlim.add_const (X / 2)

end HarrisWork

open HarrisEOQ.Lot

theorem solution (M X : ℝ) (hM : 0 < M) (hX : 0 < X) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, stockLevel M X t) atTop (𝓝 (X / 2)) :=
  HarrisWork.average_stock_half M X hM hX

#print axioms solution
