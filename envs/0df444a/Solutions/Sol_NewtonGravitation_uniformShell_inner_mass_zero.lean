-- Prove2me | solution 1 for NewtonGravitation.uniformShell_inner_mass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T19:01:56.149887+00:00
-- url     : https://prove2.me/submissions/15e43c4a-4f7a-4265-b1f4-005db5ddc76f

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (M : NNReal) (a : ℝ) (ha : 0 < a) :
    (uniformShell M a) (Metric.ball (0 : Space) a) = 0 := by
  classical
  let σ : Measure (Metric.sphere (0 : Space) 1) :=
    (volume : Measure Space).toSphere
  let f : Metric.sphere (0 : Space) 1 → Space := fun u => a • (u : Space)
  have hf : Measurable f := by
    fun_prop
  have houtside : ∀ u : Metric.sphere (0 : Space) 1,
      f u ∉ Metric.ball (0 : Space) a := by
    intro u
    have hu : ‖(u : Space)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    have hnorm : ‖f u‖ = a := by
      simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu]
    intro hin
    have hlt : ‖f u‖ < a := by
      simpa only [Metric.mem_ball, dist_zero_right] using hin
    rw [hnorm] at hlt
    exact (lt_irrefl a) hlt
  have hpre : f ⁻¹' (Metric.ball (0 : Space) a) = ∅ := by
    ext u
    simp [houtside u]
  have hzero : (σ.map f) (Metric.ball (0 : Space) a) = 0 := by
    rw [Measure.map_apply hf measurableSet_ball]
    rw [hpre, measure_empty]
  change ((M : ENNReal) / σ Set.univ) *
    (σ.map f) (Metric.ball (0 : Space) a) = 0
  rw [hzero, mul_zero]
