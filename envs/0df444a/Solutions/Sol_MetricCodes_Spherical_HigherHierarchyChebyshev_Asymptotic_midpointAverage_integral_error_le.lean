-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.midpointAverage_integral_error_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/db00bae8-19e8-478c-aaa5-f5da50bfd8b9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter
open scoped Topology BigOperators Interval
open MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution
    {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Icc (0 : ℝ) 1))
    {N : ℕ} (hN : 0 < N) :
    |midpointAverage f N - ∫ x in (0 : ℝ)..1, f x| ≤
      (f 0 - f 1) / N := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hscaled :
      AntitoneOn (fun x : ℝ => f (x / (N : ℝ)))
        (Set.Icc (0 : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    apply hf
    · exact ⟨div_nonneg hx.1 hN'.le, (div_le_one hN').mpr hx.2⟩
    · exact ⟨div_nonneg hy.1 hN'.le, (div_le_one hN').mpr hy.2⟩
    · exact (div_le_div_iff_of_pos_right hN').mpr hxy
  have hleft_raw := AntitoneOn.integral_le_sum (a := N) (x₀ := (0 : ℝ))
    (f := fun x : ℝ => f (x / (N : ℝ))) (by simpa using hscaled)
  have hright_raw := AntitoneOn.sum_le_integral (a := N) (x₀ := (0 : ℝ))
    (f := fun x : ℝ => f (x / (N : ℝ))) (by simpa using hscaled)
  have hintegral :
      (∫ x in (0 : ℝ)..(N : ℝ), f (x / (N : ℝ))) =
        (N : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
    rw [intervalIntegral.integral_comp_div f hN'.ne']
    simp [hN'.ne', smul_eq_mul]
  have hleft :
      (N : ℝ) * (∫ x in (0 : ℝ)..1, f x) ≤
        ∑ i ∈ Finset.range N, f ((i : ℝ) / N) := by
    simpa [hintegral] using hleft_raw
  have hright :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N)) ≤
        (N : ℝ) * (∫ x in (0 : ℝ)..1, f x) := by
    simpa [hintegral, Nat.cast_add, Nat.cast_one] using hright_raw
  have hmid_left :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N)) ≤
        ∑ i ∈ Finset.range N, f ((i : ℝ) / N) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    apply hf
    · constructor
      · positivity
      · apply (div_le_one hN').mpr
        exact_mod_cast (Nat.le_of_lt hi')
    · constructor
      · positivity
      · apply (div_le_one hN').mpr
        have hicast : (i : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hi'
        linarith
    · exact (div_le_div_iff_of_pos_right hN').mpr (by linarith)
  have hmid_right :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N)) ≤
        ∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    apply hf
    · constructor
      · positivity
      · apply (div_le_one hN').mpr
        have hicast : (i : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hi'
        linarith
    · constructor
      · positivity
      · apply (div_le_one hN').mpr
        exact_mod_cast Nat.succ_le_of_lt hi'
    · exact (div_le_div_iff_of_pos_right hN').mpr (by linarith)
  have hgap :
      (∑ i ∈ Finset.range N, f ((i : ℝ) / N)) -
        (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N)) = f 0 - f 1 := by
    rw [← Finset.sum_sub_distrib]
    have htel := Finset.sum_range_sub' (fun i : ℕ => f ((i : ℝ) / N)) N
    simpa [Nat.cast_add, Nat.cast_one, hN'.ne'] using htel
  unfold midpointAverage
  apply abs_le.mpr
  have hrewrite :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N)) / N -
          (∫ x in (0 : ℝ)..1, f x) =
        ((∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N)) -
          (N : ℝ) * (∫ x in (0 : ℝ)..1, f x)) / N := by
    rw [sub_div, mul_div_cancel_left₀ _ hN'.ne']
  constructor
  · rw [hrewrite, ← neg_div]
    apply (div_le_div_iff_of_pos_right hN').mpr
    nlinarith
  · rw [hrewrite]
    apply (div_le_div_iff_of_pos_right hN').mpr
    nlinarith
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
