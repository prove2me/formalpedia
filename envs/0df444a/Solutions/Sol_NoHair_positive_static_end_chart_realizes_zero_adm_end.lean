-- Prove2me | solution 1 for NoHair.positive_static_end_chart_realizes_zero_adm_end
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:51:36.257131+00:00
-- url     : https://prove2.me/submissions/b101610b-d13e-4769-b776-2106533a788f

import Theorems.Thm_NoHair_regular_static_positive_sheet_metric_falloff
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Metric MeasureTheory
private abbrev X := ADMPoint
private abbrev A := Fin 3
private abbrev I := 𝓘(ℝ,X)

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    (f : OpenPartialHomeomorph Q ADMPoint) (target : f.target=Ω)
    (forward : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f f.source)
    (backward : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm f.target)
    (coeff : ∀ x ∈ Ω, riemannianEndCoeffs f.symm x = staticPositiveMetric N h x)
    (flat : ∀ t ∈ atlas ADMPoint Q, ∀ x ∈ t.target, spatialScalarCurvature (riemannianEndCoeffs t.symm) x = 0)
    (farCompact : ∃ A : ℝ, 0<A ∧ ∀ t:ℝ, A≤t → IsCompact (f.symm '' {x : ADMPoint | t<‖x‖})ᶜ)
    (mass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    HasScalarFlatZeroADMEnd Q := by
  classical
  obtain ⟨R,C,rp,cp,bounds⟩ := regular_static_positive_sheet_metric_falloff Ω W N h c 2
  obtain ⟨S,_,tail⟩ := farCompact
  obtain ⟨B,hB⟩ := c.compactComplement.isBounded.exists_norm_le
  let T := max R (max S B)
  have tp : 0<T := rp.trans_le (le_max_left _ _)
  let V := {x : X | T<‖x‖}
  have ov : IsOpen V := isOpen_lt continuous_const continuous_norm
  have inside : V ⊆ Ω := by
    intro x hx
    by_contra no
    have big := ((le_max_right S B).trans (le_max_right R (max S B))).trans_lt (show T<‖x‖ from hx)
    exact big.not_ge (hB x no)
  let e := f.symm.restrOpen V ov
  have src : e.source=V := by
    change f.target∩V=V; rw [target]; exact inter_eq_right.mpr inside
  have same (x:X) (hx:x∈V) (i j:A) : (fun z => riemannianEndCoeffs e z i j) =ᶠ[𝓝 x] (fun z => staticPositiveMetric N h z i j) := by
    filter_upwards [ov.mem_nhds hx] with y hy
    exact congrArg (fun m:Matrix A A ℝ => m i j) (coeff y (inside hy))
  refine ⟨flat,T,C,e,tp,cp,src,fun t ht => tail t (((le_max_left S B).trans (le_max_right R (max S B))).trans ht),?_,?_,?_,?_⟩
  · apply backward.mono
    intro x hx; exact hx.1
  · apply forward.mono
    intro x hx; exact hx.1
  · intro k hk x hx i j
    rw [src] at hx
    have eq : (fun z => riemannianEndCoeffs e z i j - (1:Matrix A A ℝ) i j) =ᶠ[𝓝 x]
        (fun z => staticPositiveMetric N h z i j - (1:Matrix A A ℝ) i j) :=
      (same x hx i j).mono (fun z hz => congrArg (fun t:ℝ => t-(1:Matrix A A ℝ) i j) hz)
    rw [(eq.iteratedFDeriv ℝ k).eq_of_nhds,Nat.add_comm 1 k]
    exact bounds x ((le_max_left R (max S B)).trans_lt hx) k hk i j
  · apply mass.congr'
    filter_upwards [eventually_gt_atTop T] with r hr
    symm
    apply congrArg (fun H:ADMSphere → ℝ => (∫ n, H n ∂admSurfaceMeasure)/(16*Real.pi))
    funext n
    have unorm : ‖(n:X)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
    let x := r • (n:X)
    have xx : x∈V := by change T<‖r • (n:X)‖; simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (tp.trans hr),unorm,mul_one] using hr
    have pd (i j a:A) : spatialADMPartial a (fun y => riemannianEndCoeffs e y i j) x =
        spatialADMPartial a (fun y => staticPositiveMetric N h y i j) x :=
      congrArg (fun v:X→L[ℝ] ℝ => v (EuclideanSpace.single a 1)) (same x xx i j).fderiv_eq
    simp only [staticADMDensity,show r • (n:X)=x from rfl,pd]
