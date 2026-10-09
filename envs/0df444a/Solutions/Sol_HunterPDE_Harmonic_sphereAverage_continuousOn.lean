-- Prove2me | solution 1 for HunterPDE.Harmonic.sphereAverage_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T18:55:49.000344+00:00
-- url     : https://prove2.me/submissions/d33c558d-1d2c-488d-8417-c993a36b0983

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp

open MeasureTheory Set
open HunterPDE.Harmonic

theorem solution {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 ≤ r)
    (hu : ContinuousOn u (Metric.closedBall x r)) :
    ContinuousOn (sphereAverage u x) (Icc 0 r) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let f : Icc 0 r → S → ℝ := fun t y => u (x + (t : ℝ) • (y : EuclideanSpace ℝ (Fin n)))
  have hm : ∀ t : Icc 0 r, ∀ y : S,
      x + (t : ℝ) • (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall x r := by
    intro t y
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg t.property.1]
    have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using y.property
    simpa [hy] using t.property.2
  have hf : Continuous f.uncurry := by
    apply hu.comp_continuous
    · fun_prop
    · intro p
      exact hm p.1 p.2
  have hi : Continuous (fun t : Icc 0 r => ∫ y : S, f t y ∂volume.toSphere) := by
    simpa using continuous_parametric_integral_of_continuous hf
      (isCompact_univ : IsCompact (univ : Set S))
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun t : Icc 0 r => sphereAverage u x (t : ℝ))
  simp_rw [sphereAverage, average_eq]
  exact (continuous_const : Continuous (fun _ : Icc 0 r =>
    ((volume.toSphere : Measure S).real univ)⁻¹)).smul hi
