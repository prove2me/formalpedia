-- Prove2me | solution 1 for NoHair.smooth_isometric_extension_of_static_double_metric_and_equations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:59:43.252379+00:00
-- url     : https://prove2.me/submissions/5d80d667-4080-437d-82bb-12f15be52de5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_smooth_completion_atlas_from_reflected_static_point_chart
import Theorems.Thm_NoHair_riemannian_metric_gluing_on_prescribed_smooth_static_completion_atlas
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) (a : StaticMinusPointChart Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (p : UniformSpace.Completion d.carrier) (off : ∀ q:d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p)
    (exhaust : ∀ w : UniformSpace.Completion d.carrier, w=p ∨ ∃ q:d.carrier, (q : UniformSpace.Completion d.carrier)=w)
    (e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier))
    (ball : e.source=Metric.ball 0 a.radius) (center : e 0=p)
    (agrees : ∀ y ∈ a.change.source, e y=((d.side false).symm (a.change y) : UniformSpace.Completion d.carrier))
    (compactEnd : ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ t → IsCompact
      (((fun x : ADMPoint => ((d.side true).symm x : UniformSpace.Completion d.carrier)) '' {x : ADMPoint | t < ‖x‖})ᶜ))
    (L : C(UniformSpace.Completion d.carrier, ℝ)) (f : OpenPartialHomeomorph (UniformSpace.Completion d.carrier) ADMPoint)
    (extension : (∀ q : d.carrier, L (q : UniformSpace.Completion d.carrier) = d.lapse q)) (atPole : L p = -1)
    (source : f.source = {z | z ≠ p ∧ 0 < L z}) (target : f.target=Ω)
    (inverse : (∀ x ∈ Ω, f.symm x = ((d.side true).symm x : UniformSpace.Completion d.carrier))) :
    ∃ ch : ChartedSpace ADMPoint (UniformSpace.Completion d.carrier), letI := ch
      ∃ sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ (UniformSpace.Completion d.carrier), letI := sm
      ∃ rb : RiemannianBundle (fun q : (UniformSpace.Completion d.carrier) => TangentSpace 𝓘(ℝ,ADMPoint) q), letI := rb
      IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : (UniformSpace.Completion d.carrier) => TangentSpace 𝓘(ℝ,ADMPoint) q) ∧
      IsRiemannianManifold 𝓘(ℝ,ADMPoint) (UniformSpace.Completion d.carrier) ∧
      (∀ t ∈ atlas ADMPoint (UniformSpace.Completion d.carrier), ∀ x ∈ t.target, spatialScalarCurvature (riemannianEndCoeffs t.symm) x = 0) ∧ ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) 2 L ({p}ᶜ) ∧
      ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f f.source ∧
      ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm f.target ∧
      (∀ x ∈ Ω, riemannianEndCoeffs f.symm x = staticPositiveMetric N h x) ∧
      (∀ e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier),
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e e.source →
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e.symm e.target →
    ∀ x ∈ e.source, e x ≠ p → L (e x) ≠ 0 →
      staticWeightedLapseDivergence (riemannianEndCoeffs e) (L ∘ e) x = 0) := by
  obtain ⟨ch,sm,compatible⟩ := smooth_completion_atlas_from_reflected_static_point_chart Ω W N h c d a hpositiveEnd hmass
    p off exhaust e ball center agrees
  refine ⟨ch,sm,?_⟩
  exact riemannian_metric_gluing_on_prescribed_smooth_static_completion_atlas Ω W N h c d a hpositiveEnd hmass
    p off exhaust e ball center agrees compactEnd L f extension atPole source target inverse ch sm compatible
