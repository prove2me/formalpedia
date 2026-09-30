-- Prove2me | solution 1 for NHPPArrivals.LinearRate.linear_degree_pos
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:17:20.698953+00:00
-- url     : https://prove2.me/submissions/2726f5d7-2e06-48bf-a9c0-0a6234573ccb

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

open MeasureTheory
open NHPPArrivals.LinearRate

theorem solution (a b T : ℝ) (hT : 0 < T) (ha : 0 < a) (hb : 0 ≤ b) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, condCdf (linRate a b) T t =
      (t * T + (b / a) * (t * T) ^ 2 / 2) / (T + (b / a) * T ^ 2 / 2)) ∧
    IsGreatest ((fun t => |condCdf (linRate a b) T t - t|) '' Set.Icc (0:ℝ) 1)
      |condCdf (linRate a b) T (1 / 2) - 1 / 2| ∧
    degree (condCdf (linRate a b) T) = |condCdf (linRate a b) T (1 / 2) - 1 / 2| ∧
    |condCdf (linRate a b) T (1 / 2) - 1 / 2| =
      1 / 2 - (T / 2 + (b / a) * T ^ 2 / 8) / (T + (b / a) * T ^ 2 / 2) ∧
    1 / 2 - (T / 2 + (b / a) * T ^ 2 / 8) / (T + (b / a) * T ^ 2 / 2) =
      (b / a) * T / (8 + 4 * (b / a) * T) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hT' : T ≠ 0 := ne_of_gt hT
  have hcT : 0 ≤ (b / a) * T ^ 2 := by positivity
  have hD : 0 < T + (b / a) * T ^ 2 / 2 := by positivity
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
  have hcd : ∀ t : ℝ, condCdf (linRate a b) T t =
      (t * T + (b / a) * (t * T) ^ 2 / 2) / (T + (b / a) * T ^ 2 / 2) := by
    intro t
    rw [condCdf, hcum, hcum]
    field_simp
  have hform : ∀ t ∈ Set.Icc (0:ℝ) 1, |condCdf (linRate a b) T t - t|
      = ((b / a) * T ^ 2 / 2) * (t - t ^ 2) / (T + (b / a) * T ^ 2 / 2) := by
    intro t ht
    have hnum : t * T + (b / a) * (t * T) ^ 2 / 2
        = t * (T + (b / a) * T ^ 2 / 2) + ((b / a) * T ^ 2 / 2) * (t ^ 2 - t) := by
      ring
    rw [hcd t, hnum, add_div, mul_div_cancel_right₀ t (ne_of_gt hD), add_sub_cancel_left,
      abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (b / a) * T ^ 2 / 2),
      abs_of_nonpos (by nlinarith [ht.1, ht.2] : t ^ 2 - t ≤ 0), abs_of_pos hD]
    ring
  have hgreat : IsGreatest ((fun t => |condCdf (linRate a b) T t - t|) '' Set.Icc (0:ℝ) 1)
      |condCdf (linRate a b) T (1 / 2) - 1 / 2| := by
    constructor
    · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      rfl
    · rintro y ⟨t, ht, rfl⟩
      change |condCdf (linRate a b) T t - t| ≤ |condCdf (linRate a b) T (1 / 2) - 1 / 2|
      rw [hform t ht, hform (1 / 2) ⟨by norm_num, by norm_num⟩]
      have h14 : (1:ℝ) / 2 - (1 / 2) ^ 2 = 1 / 4 := by norm_num
      rw [h14]
      have ht2 : t - t ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
      have hk : (0:ℝ) ≤ (b / a) * T ^ 2 / 2 := by positivity
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht2 hk) hD.le
  have hval : |condCdf (linRate a b) T (1 / 2) - 1 / 2|
      = 1 / 2 - (T / 2 + (b / a) * T ^ 2 / 8) / (T + (b / a) * T ^ 2 / 2) := by
    rw [hcd (1 / 2)]
    have h12 : (1 / 2 : ℝ) * T + (b / a) * ((1 / 2) * T) ^ 2 / 2
        = T / 2 + (b / a) * T ^ 2 / 8 := by ring
    rw [h12]
    have hle : (T / 2 + (b / a) * T ^ 2 / 8) / (T + (b / a) * T ^ 2 / 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ hD]
      nlinarith [hcT]
    rw [abs_of_nonpos (by linarith : (T / 2 + (b / a) * T ^ 2 / 8) /
      (T + (b / a) * T ^ 2 / 2) - 1 / 2 ≤ 0)]
    ring
  have hfinal : 1 / 2 - (T / 2 + (b / a) * T ^ 2 / 8) / (T + (b / a) * T ^ 2 / 2)
      = (b / a) * T / (8 + 4 * (b / a) * T) := by
    field_simp
    ring
  exact ⟨fun t _ => hcd t, hgreat, by simpa only [degree] using hgreat.csSup_eq, hval, hfinal⟩
