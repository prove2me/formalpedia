-- Prove2me | solution 1 for NewtonGravitation.shell_theorem_exterior
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T12:16:50.384168+00:00
-- url     : https://prove2.me/submissions/60f69f86-2cf5-48e8-a0a6-8d6bae15dbbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NewtonGravitation_Defs
import Theorems.Thm_NewtonGravitation_gravField_eq_enclosed_mass
import Theorems.Thm_NewtonGravitation_integrable_newtonKernel_outside_support
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsSphericallySymmetric μ) (R : ℝ)
    (hR : μ (Metric.closedBall 0 R)ᶜ = 0)
    (x : Space) (hx : R < ‖x‖) :
    gravField μ x = pointField (μ.real Set.univ) 0 x := by
  classical
  have hint : Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ :=
    NewtonGravitation.integrable_newtonKernel_outside_support μ R hR x hx
  have hball : Metric.closedBall (0 : Space) R ⊆ Metric.ball 0 ‖x‖ := by
    intro y hy
    have hyR : ‖y‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hyx : ‖y‖ < ‖x‖ := lt_of_le_of_lt hyR hx
    simpa [Metric.mem_ball, dist_zero_right] using hyx
  have hnull : μ (Metric.ball (0 : Space) ‖x‖)ᶜ = 0 := by
    apply measure_mono_null (Set.compl_subset_compl.mpr hball) hR
  have hmass : μ (Metric.ball (0 : Space) ‖x‖) = μ Set.univ := by
    calc
      μ (Metric.ball (0 : Space) ‖x‖) =
          μ (Metric.ball (0 : Space) ‖x‖) +
            μ (Metric.ball (0 : Space) ‖x‖)ᶜ := by simp [hnull]
      _ = μ Set.univ := measure_add_measure_compl measurableSet_ball
  have hreal : μ.real (Metric.ball (0 : Space) ‖x‖) = μ.real Set.univ := by
    simpa [Measure.real] using congrArg ENNReal.toReal hmass
  simpa only [hreal] using
    (NewtonGravitation.gravField_eq_enclosed_mass μ hμ x hint)
