-- Prove2me | solution 1 for NoHair.static_riemannian_gluing_with_continuous_pole
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:40:17.319477+00:00
-- url     : https://prove2.me/submissions/2bd1299b-d53e-4702-9b0b-857c1a4e5f84
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_static_negative_sheet_pole_from_lapse_monopole
import Theorems.Thm_NoHair_finite_static_horizon_reflection
import Theorems.Thm_NoHair_complete_static_double_from_reflection_and_point_chart
import Theorems.Thm_NoHair_reflected_static_double_compact_truncations
import Theorems.Thm_NoHair_static_conformal_halves_signed_lapse_equation
import Theorems.Thm_NoHair_static_exterior_simultaneous_hansen_regularization
import Theorems.Thm_NoHair_static_minus_point_chart_from_hansen_data
import Theorems.Thm_NoHair_regular_static_lapse_adapted_end_chart
import Theorems.Thm_NoHair_regular_static_lapse_positive_monopole
import Theorems.Thm_NoHair_static_conformal_halves_nondegenerate
open NoHair Set Filter Metric MeasureTheory
open scoped Topology ContDiff
private abbrev X := ADMPoint

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (hflat : ∀ x ∈ closure Ω, spatialScalarCurvature h x = 0 ∧
      ∀ s : ℝ, 1 + s * N x ≠ 0 →
        spatialScalarCurvature (staticPositiveMetric (fun y => s*N y) h) x = 0)
    (hforms : ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ frontier Ω, ∀ s : ℝ, s = 1 ∨ s = -1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (∀ i j : Fin 3, k x i j = h x i j / 16) ∧
      staticLapseGradientSq N k x = (4*κ)^2 ∧
      ∀ v w : ADMPoint, fderiv ℝ N x v = 0 → fderiv ℝ N x w = 0 →
        (∑ i : Fin 3, ∑ j : Fin 3, staticSpatialHessian N k i j x * v i * w j) / (4*κ) =
          s*8*κ*(∑ i : Fin 3, ∑ j : Fin 3, k x i j * v i * w j))
    (μ : ℝ) (hμ : 0 < μ) (hpole : HasContinuousStaticPole N h μ) :
    Nonempty (StaticConformalCompletion Ω N h) := by
  obtain ⟨ν,hν,mono⟩ := regular_static_lapse_positive_monopole Ω W N h c
  have poleν := static_negative_sheet_pole_from_lapse_monopole Ω W N h c ν mono
  have eq4 : (μ/2)^4=(ν/2)^4 := by simpa using tendsto_nhds_unique (hpole 0 0) (poleν 0 0)
  have eqhalf := (pow_left_inj₀ (by positivity : 0 ≤ μ/2) (by positivity : 0 ≤ ν/2) (by decide : 4≠0)).mp eq4
  have eqμ : μ=ν := by linarith
  have hm : HasStaticLapseMonopole N μ := eqμ.symm ▸ mono
  have chart : Nonempty (StaticMinusPointChart Ω N h) := by
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
  obtain ⟨a⟩ := chart
  obtain ⟨d⟩ := finite_static_horizon_reflection Ω W N h c hflat hforms
    (static_conformal_halves_nondegenerate Ω W N h c) (static_conformal_halves_signed_lapse_equation Ω W N h c)
  exact complete_static_double_from_reflection_and_point_chart Ω W N h c d a
    (reflected_static_double_compact_truncations Ω N h d) hpositiveEnd hmass
