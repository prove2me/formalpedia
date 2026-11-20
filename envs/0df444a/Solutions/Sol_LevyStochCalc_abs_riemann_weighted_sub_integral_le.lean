-- Prove2me | solution 1 for LevyStochCalc.abs_riemann_weighted_sub_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:56:02.129188+00:00
-- url     : https://prove2.me/submissions/431d1a37-226d-440c-9080-c0317ab1fb20

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace LevyStochCalc

open MeasureTheory

theorem _root_.solution
    {T ε δ M Kg : ℝ} (hε0 : 0 ≤ ε)
    {g h : ℝ → ℝ} (hgc : Continuous g) (hh : Measurable h)
    (hhM : ∀ s, |h s| ≤ M) (hgb : ∀ s ∈ Set.Icc (0 : ℝ) T, |g s| ≤ Kg)
    (hgmod : ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T, |x - y| ≤ δ → |g x - g y| ≤ ε)
    {m : ℕ} (t : ℕ → ℝ) (ht0 : t 0 = 0) (htm : t m = T)
    (htmono : ∀ i, i < m → t i ≤ t (i + 1)) (htmesh : ∀ i, i < m → t (i + 1) - t i ≤ δ)
    (htIcc : ∀ i, i ≤ m → t i ∈ Set.Icc (0 : ℝ) T) :
    |(∑ i ∈ Finset.range m, g (t i) * ∫ s in t i..t (i + 1), h s)
        - ∫ s in (0 : ℝ)..T, g s * h s| ≤ ε * M * T := by
  have hhI : ∀ a b : ℝ, IntervalIntegrable h volume a b := fun a b =>
    (intervalIntegrable_const (c := M)).mono_fun' hh.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by simp only [Real.norm_eq_abs]; exact hhM s)
  have hghI : ∀ a b : ℝ, IntervalIntegrable (fun s => g s * h s) volume a b := fun a b =>
    (hhI a b).continuousOn_mul hgc.continuousOn
  have hcI : ∀ (c : ℝ) (a b : ℝ), IntervalIntegrable (fun s => c * h s) volume a b :=
    fun c a b => (hhI a b).const_mul c
  have hsplit : ∫ s in (0 : ℝ)..T, g s * h s
      = ∑ i ∈ Finset.range m, ∫ s in t i..t (i + 1), g s * h s := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hghI _ _), ht0, htm]
  rw [hsplit, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range m,
      |g (t i) * (∫ s in t i..t (i + 1), h s) - ∫ s in t i..t (i + 1), g s * h s|
        ≤ ε * M * (t (i + 1) - t i) := by
    intro i hi
    have him : i < m := Finset.mem_range.1 hi
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hcI _ _ _) (hghI _ _)]
    have hle := htmono i him
    have hbound : ∀ s ∈ Set.uIoc (t i) (t (i + 1)),
        ‖g (t i) * h s - g s * h s‖ ≤ ε * M := by
      intro s hs
      rw [Set.uIoc_of_le hle] at hs
      have hi0 := htIcc i him.le
      have hi1 := htIcc (i + 1) him
      have hsI : s ∈ Set.Icc (0 : ℝ) T := ⟨hi0.1.trans hs.1.le, hs.2.trans hi1.2⟩
      have hd : |t i - s| ≤ δ := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]
        linarith [hs.2, htmesh i him]
      have hg1 := hgmod _ hi0 _ hsI hd
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      exact mul_le_mul hg1 (hhM s) (abs_nonneg _) hε0
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hle)] at this
    exact this
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
  rw [← Finset.mul_sum, Finset.sum_range_sub, htm, ht0, sub_zero]

end LevyStochCalc
