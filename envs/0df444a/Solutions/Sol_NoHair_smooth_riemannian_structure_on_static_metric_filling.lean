-- Prove2me | solution 1 for NoHair.smooth_riemannian_structure_on_static_metric_filling
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:44:56.186426+00:00
-- url     : https://prove2.me/submissions/f752c3c6-410b-4c95-b5fc-62bc3ec41bdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_signed_lapse_and_physical_chart_on_static_metric_completion
import Theorems.Thm_NoHair_smooth_scalar_flat_atlas_on_one_point_static_completion
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open UniformSpace
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
      (((fun x : ADMPoint => ((d.side true).symm x : UniformSpace.Completion d.carrier)) '' {x : ADMPoint | t < ‖x‖})ᶜ)) :
    ∃ D : StaticConformalCompletion Ω N h, ∃ j : D.carrier ≃ᵢ UniformSpace.Completion d.carrier, j D.pole=p := by
  classical
  obtain ⟨L,f,ext,lp,lower,asym,hor,src,tgt,inv,phys⟩ :=
    signed_lapse_and_physical_chart_on_static_metric_completion Ω W N h c d hpositiveEnd hmass p off
  obtain ⟨ch,sm,rb,sr,rm,enddata,sl,sf,si,metric,eq⟩ :=
    smooth_scalar_flat_atlas_on_one_point_static_completion Ω W N h c d a hpositiveEnd hmass p off exhaust e ball center agrees compactEnd
      L f ext lp src tgt inv
  letI := ch
  letI := sm
  letI := rb
  letI := sr
  letI := rm
  letI : PreconnectedSpace (Completion d.carrier) := Completion.denseRange_coe.preconnectedSpace (Completion.continuous_coe (α:=d.carrier))
  letI : ConnectedSpace (Completion d.carrier) := { toNonempty := ⟨p⟩ }
  let D : StaticConformalCompletion Ω N h := {
    carrier := Completion d.carrier, zeroMassEnd := enddata, pole := p, lapse := L,
    smoothLapse := sl, lower := lower, asymptote := asym, horizon := hor, physical := f,
    source := src, target := tgt, smoothPhysical := sf, smoothInverse := si,
    physicalMetric := fun q hq => ⟨phys q hq,metric q hq⟩, lapseEquation := eq }
  exact ⟨D,IsometryEquiv.refl _,rfl⟩
