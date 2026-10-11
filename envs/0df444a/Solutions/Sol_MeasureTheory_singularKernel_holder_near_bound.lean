-- Prove2me | solution 1 for MeasureTheory.singularKernel_holder_near_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:03:26.529577+00:00
-- url     : https://prove2.me/submissions/a94c48d0-caf8-45a9-af5b-cdd0f9555419

import Theorems.Thm_MeasureTheory_integral_norm_rpow_ball
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Metric
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α)
    (K g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hKm : AEStronglyMeasurable K volume) (hgm : AEStronglyMeasurable g volume)
    (C H : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hK : ∀ z, z ≠ 0 → ‖K z‖ ≤ C * ‖z‖ ^ (-(n : ℝ)))
    (hg : ∀ z, |g z| ≤ H * ‖z‖ ^ α) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z => K z * g z) (ball 0 R) ∧
      |∫ z in ball 0 R, K z * g z| ≤
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
          C * H * R ^ α / α := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hi, he⟩ := MeasureTheory.integral_norm_rpow_ball n hn α hα R hR
  have hid := hi.const_mul (C * H)
  have hne : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), z ≠ 0 := by
    simp [ae_iff]
  have hdom : ∀ᵐ z ∂volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R),
      ‖K z * g z‖ ≤ C * H * ‖z‖ ^ (α - n) := by
    filter_upwards [ae_restrict_of_ae hne] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc
      ‖K z * g z‖ = ‖K z‖ * |g z| := by simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ (C * ‖z‖ ^ (-(n : ℝ))) * (H * ‖z‖ ^ α) :=
        mul_le_mul (hK z hz) (hg z) (abs_nonneg _) (by positivity)
      _ = C * H * ‖z‖ ^ (α - n) := by
        rw [show α - n = -(n : ℝ) + α by ring, Real.rpow_add hz0]
        ring
  refine ⟨hid.mono' (hKm.mul hgm).restrict hdom, ?_⟩
  calc
    |∫ z in ball 0 R, K z * g z| ≤
        ∫ z : EuclideanSpace ℝ (Fin n) in ball 0 R, C * H * ‖z‖ ^ (α - n) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hid hdom
    _ = _ := by rw [integral_const_mul, he]; ring
