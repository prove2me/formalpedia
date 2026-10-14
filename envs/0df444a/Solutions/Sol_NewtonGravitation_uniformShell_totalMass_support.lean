-- Prove2me | solution 1 for NewtonGravitation.uniformShell_totalMass_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T18:46:42.17267+00:00
-- url     : https://prove2.me/submissions/d8ac2aa4-c13f-4e8c-a93a-3135bf71011a

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation
open scoped ENNReal

theorem solution (M : NNReal) (a : ℝ) (ha : 0 < a) :
    (uniformShell M a).real Set.univ = (M : ℝ) ∧
      (uniformShell M a) (Metric.closedBall (0 : Space) a)ᶜ = 0 := by
  classical
  let σ : Measure (Metric.sphere (0 : Space) 1) :=
    (volume : Measure Space).toSphere
  let f : Metric.sphere (0 : Space) 1 → Space := fun u => a • (u : Space)
  have hf : Measurable f := by
    fun_prop
  have hσ0 : σ Set.univ ≠ 0 := by
    exact Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (volume : Measure Space))
  have hσtop : σ Set.univ ≠ ∞ := by
    exact ne_of_lt (measure_lt_top σ Set.univ)
  have hmap : (σ.map f) Set.univ = σ Set.univ := by
    rw [Measure.map_apply hf MeasurableSet.univ]
    simp
  have hmass : (uniformShell M a) Set.univ = (M : ENNReal) := by
    change ((M : ENNReal) / σ Set.univ) * (σ.map f) Set.univ =
      (M : ENNReal)
    rw [hmap]
    exact ENNReal.div_mul_cancel hσ0 hσtop
  have hinside : ∀ u : Metric.sphere (0 : Space) 1,
      f u ∈ Metric.closedBall (0 : Space) a := by
    intro u
    have hu : ‖(u : Space)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    have hnorm : ‖f u‖ = a := by
      simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu]
    simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using (le_refl a)
  have hpre : f ⁻¹' (Metric.closedBall (0 : Space) a)ᶜ = ∅ := by
    ext u
    simp [hinside u]
  have hzero : (σ.map f) (Metric.closedBall (0 : Space) a)ᶜ = 0 := by
    rw [Measure.map_apply hf measurableSet_closedBall.compl]
    rw [hpre, measure_empty]
  constructor
  · change ((uniformShell M a) Set.univ).toReal = (M : ℝ)
    rw [hmass]
    norm_cast
  · change ((M : ENNReal) / σ Set.univ) *
        (σ.map f) (Metric.closedBall (0 : Space) a)ᶜ = 0
    rw [hzero, mul_zero]
