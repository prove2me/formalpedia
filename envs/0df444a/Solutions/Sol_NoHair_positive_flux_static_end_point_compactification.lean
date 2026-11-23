-- Prove2me | solution 1 for NoHair.positive_flux_static_end_point_compactification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:30:56.057912+00:00
-- url     : https://prove2.me/submissions/1debc0c4-7d11-42a2-90b8-aeeb6a112b8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_static_exterior_simultaneous_hansen_regularization
import Theorems.Thm_NoHair_static_minus_point_chart_from_hansen_data
import Theorems.Thm_NoHair_regular_static_lapse_adapted_end_chart
import Theorems.Thm_NoHair_regular_static_lapse_positive_monopole
import Theorems.Thm_NoHair_static_conformal_halves_nondegenerate
open NoHair Set Filter Metric MeasureTheory
open scoped Topology ContDiff
private abbrev X := ADMPoint

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (hbound : HasStaticMinusInversionBound N h) (hflux : ∃ m R : ℝ, 0 < m ∧ 0 < R ∧ ∀ r : ℝ, R < r →
      r^2 * (∫ n : ADMSphere, ∑ i : Fin 3,
        (Real.sqrt (h (r • (n:ADMPoint))).det * staticRaisedGradient N h i (r • (n:ADMPoint))) *
          (n:ADMPoint) i ∂admSurfaceMeasure) = m) :
    Nonempty (StaticMinusPointChart Ω N h) := by
  obtain ⟨μ,hμ,hm⟩:=regular_static_lapse_positive_monopole Ω W N h c
  obtain ⟨B,hB,hout⟩:=c.compactComplement.isBounded.exists_pos_norm_lt
  have inside {x : X} (hx : B<‖x‖) : x∈Ω := by
    by_contra hn
    exact (not_lt_of_ge hx.le) (hout x hn)
  have cover {x : X} (hx : B<‖x‖) := c.extendsAcross (subset_closure (inside hx))
  have good:=static_conformal_halves_nondegenerate Ω W N h c
  obtain ⟨δ,e,dp,src,tgt,cov,se,si,eo,ei,eq⟩:=regular_static_lapse_adapted_end_chart Ω W N h c
  apply static_minus_point_chart_from_hansen_data Ω N h
  apply static_exterior_simultaneous_hansen_regularization Ω N h B μ hB hμ (fun x hx => inside hx) hm
  · intro x hx
    exact ⟨(c.positiveSide x (cover hx)).mp (inside hx),(good x (subset_closure (inside hx))).2.1,
      c.positiveMetric x (cover hx)⟩
  · intro x hx
    exact ⟨c.smoothLapse.contDiffAt (c.openExtension.mem_nhds (cover hx)),
      fun i j => (c.smoothMetric i j).contDiffAt (c.openExtension.mem_nhds (cover hx))⟩
  · exact c.falloff
  · intro x hx
    exact c.equations x (subset_closure (inside hx))
  · exact ⟨δ,e,dp,src,tgt,cov,se,si,eo,ei,fun y hy => (eq y hy).1⟩
