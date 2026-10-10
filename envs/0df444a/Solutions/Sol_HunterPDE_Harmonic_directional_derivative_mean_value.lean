-- Prove2me | solution 1 for HunterPDE.Harmonic.directional_derivative_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T15:02:58.665706+00:00
-- url     : https://prove2.me/submissions/5698164b-f29c-491a-bdbc-9f53496bcc28

import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_center
import Theorems.Thm_HunterPDE_Harmonic_ball_average_eq_of_sphereAverage_eq
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Topology HunterPDE.Harmonic
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    (hu : ∀ y ∈ Ω, ContDiffAt ℝ 1 u y) (hmv : HasMeanValueProperty Ω u)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ Ω) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ u x v = (⨍ y in Metric.ball x r, fderiv ℝ u y v) ∧
      fderiv ℝ u x v = sphereAverage (fun y => fderiv ℝ u y v) x r := by
  have hx : x ∈ Ω := hball (Metric.mem_closedBall_self hr.le)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, Metric.closedBall (x + t • v) r ⊆ Ω := by
    have h := (isCompact_closedBall x r).eventually_forall_of_forall_eventually
      (x₀ := (0 : ℝ)) (P := fun t y => y + t • v ∈ Ω) ?_
    · filter_upwards [h] with t ht
      intro z hz
      have hz' : z - t • v ∈ Metric.closedBall x r := by
        simpa [Metric.mem_closedBall, dist_eq_norm, sub_sub, add_comm] using hz
      have hh := ht (z - t • v) hz'
      simpa using hh
    intro y hy
    have hc : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => p.2 + p.1 • v) := by
      fun_prop
    exact hc.continuousAt.eventually (hΩ.mem_nhds (by simpa using hball hy))
  have hsphere : ∀ s ∈ Ioc 0 r,
      sphereAverage (fun y => fderiv ℝ u y v) x s = fderiv ℝ u x v := by
    intro s hs
    have hbs := (Metric.closedBall_subset_closedBall hs.2).trans hball
    have hd := HunterPDE.Harmonic.hasDerivAt_sphereAverage_center hn hs.1
      (fun y hy => hu y (hbs hy)) v
    have heq : (fun t : ℝ => sphereAverage u (x + t • v) s) =ᶠ[𝓝 0]
        (fun t => u (x + t • v)) := by
      filter_upwards [hnear] with t ht
      exact (hmv (x + t • v) s hs.1
        ((Metric.closedBall_subset_closedBall hs.2).trans ht)).2.symm
    have hpath : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hdu : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • v) := by
      simpa using ((hu x hx).differentiableAt (by simp)).hasFDerivAt
    have hd' := hdu.comp_hasDerivAt 0 hpath
    have hd'' := hd.congr_of_eventuallyEq heq.symm
    exact hd''.unique hd'
  have hc : ContinuousOn (fun y => fderiv ℝ u y v) (Metric.closedBall x r) := by
    intro y hy
    exact (((hu y (hball hy)).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).continuousWithinAt
  exact ⟨(ball_average_eq_of_sphereAverage_eq hn hr hc hsphere).symm,
    (hsphere r ⟨hr, le_rfl⟩).symm⟩
