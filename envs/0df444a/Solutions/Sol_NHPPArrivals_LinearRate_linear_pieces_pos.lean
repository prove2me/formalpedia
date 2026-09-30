-- Prove2me | solution 1 for NHPPArrivals.LinearRate.linear_pieces_pos
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:30:06.08567+00:00
-- url     : https://prove2.me/submissions/166293ab-ca09-4778-936d-a92a497d57b7

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

open MeasureTheory
open NHPPArrivals.LinearRate

theorem solution (a b T : ℝ) (k : ℕ) (hT : 0 < T) (ha : 0 < a) (hb : 0 ≤ b)
    (hk : 1 ≤ k) (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
    (∀ t ∈ Set.Icc (0:ℝ) (T / k), subCum (linRate a b) T k j t =
      a * t * ((k:ℝ) * (2 + (b / a) * t) + 2 * ((j:ℝ) - 1) * (b / a) * T) / (2 * k)) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, subCdf (linRate a b) T k j t =
      t * (2 * k + (2 * (j:ℝ) - 2 + t) * (b / a) * T) / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) ∧
    weight (linRate a b) T k j =
      (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) / ((k:ℝ) ^ 2 * (2 + (b / a) * T)) ∧
    subSlope a b T k j = b * k / (a * (k + ((j:ℝ) - 1) * (b / a) * T)) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hk0 : (k:ℝ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjv : (0:ℝ) ≤ (j:ℝ) - 1 := by linarith
  have hv0 : 0 ≤ ((j:ℝ) - 1) * T / k := by positivity
  have hkv : (0:ℝ) < T / k := by positivity
  have hba : 0 ≤ b / a := div_nonneg hb ha.le
  have hbase : 0 < a + b * (((j:ℝ) - 1) * T / k) := by
    have := mul_nonneg hb hv0
    linarith
  have hbase2 : 0 < a + b * (((j:ℝ) - 1) * T / k) + b * (T / k) / 2 := by
    have h1 := mul_nonneg hb hv0
    have h2 : 0 ≤ b * (T / k) / 2 := by positivity
    linarith
  have hcumT : 0 < a * T + b * (T ^ 2 / 2) := by positivity
  have hdenB : 0 < 2 * (k:ℝ) + (2 * (j:ℝ) - 1) * (b / a) * T := by
    have h2j : (0:ℝ) ≤ 2 * (j:ℝ) - 1 := by linarith
    have := mul_nonneg (mul_nonneg h2j hba) hT.le
    have hk2 : (0:ℝ) < 2 * k := by positivity
    linarith
  have hk2' : ((k:ℝ) ^ 2 * (2 + (b / a) * T)) ≠ 0 := by
    have h2' : 0 < 2 + (b / a) * T := by positivity
    positivity
  have hden4 : (a * (k + ((j:ℝ) - 1) * (b / a) * T)) ≠ 0 := by
    have h2' : 0 < k + ((j:ℝ) - 1) * (b / a) * T := by positivity
    positivity
  have hcum : ∀ x : ℝ, cumRate (linRate a b) x = a * x + b * (x ^ 2 / 2) := by
    intro x
    simp only [cumRate, linRate]
    have h₁ : IntervalIntegrable (fun _ : ℝ => a) volume (0:ℝ) x :=
      continuous_const.intervalIntegrable 0 x
    have h₂ : IntervalIntegrable (fun s : ℝ => b * s) volume (0:ℝ) x :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 x
    calc ∫ s in (0:ℝ)..x, (a + b * s)
        = (∫ s in (0:ℝ)..x, a) + (∫ s in (0:ℝ)..x, b * s) :=
          intervalIntegral.integral_add (f := fun s : ℝ => a) (g := fun s : ℝ => b * s) h₁ h₂
      _ = a * (x - 0) + b * (∫ s in (0:ℝ)..x, s) := by
          rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
            smul_eq_mul]
          ring
      _ = a * x + b * (x ^ 2 / 2) := by
          have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := x)
            (f := fun y : ℝ => y ^ 2 / 2) (f' := fun y : ℝ => y)
            (fun y _ => by simpa using (hasDerivAt_pow 2 y).div_const 2)
            (continuous_id.intervalIntegrable 0 x)
          rw [h]
          ring
  have hsub : ∀ t : ℝ, subCum (linRate a b) T k j t =
      t * (a + b * (((j:ℝ) - 1) * T / k) + b * t / 2) := by
    intro t
    rw [subCum, hcum, hcum]
    ring
  have h1 : ∀ t ∈ Set.Icc (0:ℝ) (T / k), subCum (linRate a b) T k j t =
      a * t * ((k:ℝ) * (2 + (b / a) * t) + 2 * ((j:ℝ) - 1) * (b / a) * T) / (2 * k) := by
    intro t ht
    rw [hsub t, eq_div_iff_mul_eq (mul_ne_zero two_ne_zero hk0)]
    field_simp [ha']
    ring
  have h2 : ∀ t ∈ Set.Icc (0:ℝ) 1, subCdf (linRate a b) T k j t =
      t * (2 * k + (2 * (j:ℝ) - 2 + t) * (b / a) * T) /
        (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) := by
    intro t ht
    rw [subCdf, hsub, hsub,
      div_eq_div_iff (mul_ne_zero hkv.ne' hbase2.ne') hdenB.ne']
    field_simp [ha', hk0]
    ring
  have h3 : weight (linRate a b) T k j =
      (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) / ((k:ℝ) ^ 2 * (2 + (b / a) * T)) := by
    rw [weight, hcum, hcum, hcum, div_eq_div_iff hcumT.ne' hk2']
    field_simp [ha', hk0]
    ring
  have h4 : subSlope a b T k j = b * k / (a * (k + ((j:ℝ) - 1) * (b / a) * T)) := by
    rw [subSlope, linRate, div_eq_div_iff hbase.ne' hden4]
    field_simp [ha', hk0]
  exact ⟨h1, h2, h3, h4⟩
