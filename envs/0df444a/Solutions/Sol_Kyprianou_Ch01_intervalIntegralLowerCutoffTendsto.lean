-- Prove2me | solution 1 for Kyprianou.Ch01.intervalIntegralLowerCutoffTendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:26:24.836885+00:00
-- url     : https://prove2.me/submissions/7479b5c0-aa93-41f2-8650-6ab018294e85

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hint : IntervalIntegrable f volume 0 R) :
    Tendsto (fun a : ℝ => ∫ x in a..R, f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in (0 : ℝ)..R, f x)) := by
  have hLocal : Set.Icc (0 : ℝ) R ∈ 𝓝[>] (0 : ℝ) := by
    have ho : Set.Iio R ∈ (𝓝 (0 : ℝ)) := isOpen_Iio.mem_nhds hR
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds ho]
      with a ha haR
    exact ⟨le_of_lt ha, le_of_lt haR⟩
  have hCont : ContinuousWithinAt
      (fun a : ℝ => ∫ x in R..a, f x) (Set.Icc (0 : ℝ) R) 0 := by
    apply intervalIntegral.continuousWithinAt_primitive
      (a := R) (b₀ := 0) (b₁ := 0) (b₂ := R) (μ := volume) (f := f)
    · simp
    · simpa [min_eq_right (le_of_lt hR)] using hint
  have hlimit :=
    (hCont.mono_of_mem_nhdsWithin hLocal).tendsto
  simpa only [← intervalIntegral.integral_symm] using hlimit.neg
