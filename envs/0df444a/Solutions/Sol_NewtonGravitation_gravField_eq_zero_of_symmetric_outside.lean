-- Prove2me | solution 1 for NewtonGravitation.gravField_eq_zero_of_symmetric_outside
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T12:29:58.112439+00:00
-- url     : https://prove2.me/submissions/671e20a2-a721-4da6-b2cb-8ec65f2e8e16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NewtonGravitation_Defs
import Theorems.Thm_NewtonGravitation_integrable_newtonKernel_inside_hollow
import Theorems.Thm_NewtonGravitation_gravField_eq_enclosed_mass
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsSphericallySymmetric μ) (ρ : ℝ)
    (hρ : μ (Metric.ball 0 ρ) = 0)
    (x : Space) (hx : ‖x‖ < ρ) :
    gravField μ x = 0 := by
  classical
  have hint : Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ :=
    NewtonGravitation.integrable_newtonKernel_inside_hollow μ ρ hρ x hx
  have hsubset : Metric.ball (0 : Space) ‖x‖ ⊆ Metric.ball 0 ρ := by
    intro y hy
    simp only [Metric.mem_ball, dist_zero_right] at hy ⊢
    exact lt_trans hy hx
  have hzero : μ (Metric.ball (0 : Space) ‖x‖) = 0 :=
    measure_mono_null hsubset hρ
  have hreal : μ.real (Metric.ball (0 : Space) ‖x‖) = 0 := by
    simp [Measure.real, hzero]
  have hfield := NewtonGravitation.gravField_eq_enclosed_mass μ hμ x hint
  rw [hreal] at hfield
  simpa [pointField] using hfield
