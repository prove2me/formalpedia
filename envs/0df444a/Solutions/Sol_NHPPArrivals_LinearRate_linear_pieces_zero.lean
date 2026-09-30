-- Prove2me | solution 1 for NHPPArrivals.LinearRate.linear_pieces_zero
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:30:55.612378+00:00
-- url     : https://prove2.me/submissions/a705a7da-bfd5-45aa-b43e-20ff505851f5

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

open MeasureTheory
open NHPPArrivals.LinearRate

theorem solution (b T : ℝ) (k : ℕ) (hT : 0 < T) (hb : 0 < b) (hk : 1 ≤ k) :
    (∀ j ∈ Finset.Icc 1 k, ∀ t ∈ Set.Icc (0:ℝ) (T / k),
      subCum (linRate 0 b) T k j t = b * t * ((k:ℝ) * t + 2 * ((j:ℝ) - 1) * T) / (2 * k)) ∧
    (∀ j ∈ Finset.Icc 1 k, ∀ t ∈ Set.Icc (0:ℝ) 1,
      subCdf (linRate 0 b) T k j t = t * (2 * (j:ℝ) - 2 + t) / (2 * (j:ℝ) - 1)) ∧
    (∀ j ∈ Finset.Icc 1 k, weight (linRate 0 b) T k j = (2 * (j:ℝ) - 1) / (k:ℝ) ^ 2) ∧
    (∀ j ∈ Finset.Icc 2 k, subSlope 0 b T k j = k / (((j:ℝ) - 1) * T)) := by
  have hk0 : (k:ℝ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hcum0 : ∀ x : ℝ, cumRate (linRate 0 b) x = b * (x ^ 2 / 2) := by
    intro x
    simp only [cumRate, linRate, zero_add]
    rw [intervalIntegral.integral_const_mul]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := x)
      (f := fun y : ℝ => y ^ 2 / 2) (f' := fun y : ℝ => y)
      (fun y _ => by simpa using (hasDerivAt_pow 2 y).div_const 2)
      (continuous_id.intervalIntegrable 0 x)
    rw [h]
    ring
  have hsub0 : ∀ j t, subCum (linRate 0 b) T k j t =
      t * (b * (((j:ℝ) - 1) * T / k) + b * t / 2) := by
    intro j t
    rw [subCum, hcum0, hcum0]
    ring
  have h1 : ∀ j ∈ Finset.Icc 1 k, ∀ t ∈ Set.Icc (0:ℝ) (T / k),
      subCum (linRate 0 b) T k j t =
        b * t * ((k:ℝ) * t + 2 * ((j:ℝ) - 1) * T) / (2 * k) := by
    intro j hj t ht
    rw [hsub0 j t, eq_div_iff_mul_eq (mul_ne_zero two_ne_zero hk0)]
    field_simp [hk0]
    ring
  have h2 : ∀ j ∈ Finset.Icc 1 k, ∀ t ∈ Set.Icc (0:ℝ) 1,
      subCdf (linRate 0 b) T k j t = t * (2 * (j:ℝ) - 2 + t) / (2 * (j:ℝ) - 1) := by
    intro j hj t ht
    have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hv0 : 0 ≤ ((j:ℝ) - 1) * T / k := by positivity
    have hkv : (0:ℝ) < T / k := by positivity
    have hB : 0 < b * (((j:ℝ) - 1) * T / k) + b * (T / k) / 2 := by
      have h1' := mul_nonneg hb.le hv0
      have h2' : 0 < b * (T / k) / 2 := by positivity
      linarith
    have h2j1 : 0 < 2 * (j:ℝ) - 1 := by linarith
    rw [subCdf, hsub0, hsub0, div_eq_div_iff (mul_ne_zero hkv.ne' hB.ne') h2j1.ne']
    field_simp [hk0]
    ring
  have h3 : ∀ j ∈ Finset.Icc 1 k, weight (linRate 0 b) T k j = (2 * (j:ℝ) - 1) / (k:ℝ) ^ 2 := by
    intro j hj
    have hden : 0 < b * (T ^ 2 / 2) := by positivity
    rw [weight, hcum0, hcum0, hcum0,
      div_eq_div_iff hden.ne' (pow_ne_zero 2 hk0)]
    field_simp [hk0]
    ring
  have h4 : ∀ j ∈ Finset.Icc 2 k, subSlope 0 b T k j = k / (((j:ℝ) - 1) * T) := by
    intro j hj
    have hj2 : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hj1' : (0:ℝ) < (j:ℝ) - 1 := by linarith
    have hq : 0 < ((j:ℝ) - 1) * T / k := by positivity
    have hlin : 0 < b * (((j:ℝ) - 1) * T / k) := mul_pos hb hq
    have hjd : 0 < ((j:ℝ) - 1) * T := by positivity
    rw [subSlope, linRate, div_eq_div_iff (by simpa using hlin.ne') hjd.ne']
    field_simp [hk0]
    ring
  exact ⟨h1, h2, h3, h4⟩
