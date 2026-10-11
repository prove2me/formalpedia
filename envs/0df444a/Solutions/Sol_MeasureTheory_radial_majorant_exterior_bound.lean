-- Prove2me | solution 1 for MeasureTheory.radial_majorant_exterior_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:08:17.616801+00:00
-- url     : https://prove2.me/submissions/c14aa5d1-17aa-47ad-9327-fc4c87697dbb

import Theorems.Thm_MeasureTheory_integral_norm_rpow_exterior
import Mathlib.Tactic.Ring

open MeasureTheory Metric
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : α < 1)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hm : AEStronglyMeasurable F volume)
    (C H δ : ℝ) (hδ : 0 < δ)
    (hb : ∀ z, δ < ‖z‖ → ‖F z‖ ≤ C * H * δ * ‖z‖ ^ (α - n - 1)) :
    IntegrableOn F (closedBall 0 δ)ᶜ ∧
      |∫ z in (closedBall 0 δ)ᶜ, F z| ≤
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
          C * H * δ ^ α / (1 - α) := by
  obtain ⟨hi, he⟩ := MeasureTheory.integral_norm_rpow_exterior n hn (α - 1)
    (by linarith) δ hδ
  have hexp : α - 1 - n = α - n - 1 := by ring
  rw [hexp] at hi he
  have hid := hi.const_mul (C * H * δ)
  have hdom : ∀ᵐ z ∂volume.restrict ((closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ),
      ‖F z‖ ≤ C * H * δ * ‖z‖ ^ (α - n - 1) := by
    filter_upwards [self_mem_ae_restrict isClosed_closedBall.measurableSet.compl] with z hz
    apply hb z
    simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using hz
  refine ⟨hid.mono' hm.restrict hdom, ?_⟩
  calc
    |∫ z in (closedBall 0 δ)ᶜ, F z| ≤
        ∫ z : EuclideanSpace ℝ (Fin n) in (closedBall 0 δ)ᶜ,
          C * H * δ * ‖z‖ ^ (α - n - 1) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hid hdom
    _ = _ := by
      rw [integral_const_mul, he]
      have hp : δ * δ ^ (α - 1) = δ ^ α := by
        calc
          _ = δ ^ (1 : ℝ) * δ ^ (α - 1) := by rw [Real.rpow_one]
          _ = δ ^ (1 + (α - 1)) := (Real.rpow_add hδ _ _).symm
          _ = _ := by congr 1; ring
      calc
        _ = (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
            C * H * (δ * δ ^ (α - 1)) / (1 - α) := by ring
        _ = _ := by rw [hp]
