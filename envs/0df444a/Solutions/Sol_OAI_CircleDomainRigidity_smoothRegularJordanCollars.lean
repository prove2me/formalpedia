-- Prove2me | solution 1 for OAI.CircleDomainRigidity.smoothRegularJordanCollars
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:15:49.561842+00:00
-- url     : https://prove2.me/submissions/62e6d4c7-acf8-4aa5-a877-4df9a40a53e8

import Mathlib
import Definitions.Def_Q146C010

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CircleBoundaryOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two offset-circle contributions in the Stokes estimate: zero
period costs radius times oscillation, and the distinguished constant
weight costs only that constant times the period. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem constant_weight_integral_eq_period
    (u du : ℝ → ℝ) (T ρ : ℝ)
    (hu : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt u (du x) x)
    (hdu : IntervalIntegrable du volume 0 T) :
    (∫ x in (0 : ℝ)..T, ρ * du x) = ρ * (u T - u 0) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hu hdu]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactTransverseField
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit compactly supported smooth transverse field near a
compact regular scalar level, with a global Lipschitz bound. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_transverse_field {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set ℂ} (hK : IsCompact K) (hregular : ∀ z ∈ K, fderiv ℝ f z ≠ 0) :
    ∃ (V : ℂ → ℂ) (L : ℝ≥0), ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      LipschitzWith L V ∧ ∀ z ∈ K, 0 < fderiv ℝ f z (V z) := by
  obtain ⟨χ, hχ, hc, _, _, hone⟩ :=
    exists_smooth_planar_cutoff hK isOpen_univ (subset_univ _)
  let V : ℂ → ℂ := fun z => χ z • complexScalarGradient f z
  have hs : ContDiff ℝ ∞ V := hχ.smul (complexScalarGradient_smooth hf)
  have hVc : HasCompactSupport V := hc.smul_right
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  refine ⟨V, L, hs, hVc, hL, ?_⟩
  intro z hz
  have hχz := hone.self_of_nhdsSet z hz
  simpa only [V, hχz, one_smul] using complexScalarGradient_positive (hregular z hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleLifts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real lifts of circle coordinates near filling disks

The quotient `ℝ → ℝ/ℤ` is a covering map in Mathlib. Its lifting theorem
therefore gives actual continuous real branches on simply connected open
sets. Smoothness is expressed in the ordinary real quotient charts
`AddCircle.equivIco`; a continuous lift is locally one of these charts plus
an integer, so the lift is smooth. No external lifting axiom is used.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_continuous_circle_lift
    {X : Type*} [TopologicalSpace X] {U : Set X}
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (f : X → UnitAddCircle) (hf : ContinuousOn f U)
    {x₀ : X} (hx₀ : x₀ ∈ U) (r₀ : ℝ) (hr₀ : (r₀ : UnitAddCircle) = f x₀) :
    ∃ u : X → ℝ, ContinuousOn u U ∧ u x₀ = r₀ ∧
      ∀ x ∈ U, (u x : UnitAddCircle) = f x := by
  classical
  let f' : C(U, UnitAddCircle) := ⟨fun x => f x, hf.domRestrict⟩
  obtain ⟨g, ⟨hg₀, hg⟩, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      f' ⟨x₀, hx₀⟩ r₀ hr₀
  let u : X → ℝ := fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert g.continuous using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change u x = g x
    simp only [u, dite_eq_left x.property]
  · simpa only [u, dite_eq_left hx₀] using hg₀
  · intro x hx
    have h := congrFun hg (⟨x, hx⟩ : U)
    change (g ⟨x, hx⟩ : UnitAddCircle) = f x at h
    simpa only [u, dite_eq_left hx] using h

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleCovectors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth covector fields of periodic coordinates

The locally defined circle differential is an ordinary smooth covector
field on its open domain. This supplies the tensor used in the same
metric construction as for single-valued real coordinates.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem contDiffOn_circleFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hU : IsOpen U) (hf : SmoothCircleOn f U) :
    ContDiffOn ℝ ∞ (circleFDeriv f) U := by
  intro x hx
  let a := circleCut f x
  let V := U ∩ f ⁻¹' ({(a : UnitAddCircle)} : Set UnitAddCircle)ᶜ
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hxV : x ∈ V := ⟨hx, circleCut_ne f x⟩
  have hu : ContDiffOn ℝ ∞ (circleBranch f a) V := by
    intro y hy
    exact (hf y hy.1 a hy.2).contDiffWithinAt
  have heq := circleFDeriv_eventuallyEq_lift hV (hf.continuousOn.mono inter_subset_left)
    hu (fun y _ => coe_circleBranch f a y) hxV
  exact (((hu.fderiv_of_isOpen (m := ∞) hV (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
    heq).contDiffWithinAt

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleDifferentialClosed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intrinsic differential of a smooth circle coordinate is closed.
The proof uses actual local real branches and symmetry of their Hessians. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem circleFDeriv_partial_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hU : IsOpen U) (hf : SmoothCircleOn f U)
    {x : E} (hx : x ∈ U) (v w : E) :
    (fderiv ℝ (fun y => circleFDeriv f y w) x) v =
      (fderiv ℝ (fun y => circleFDeriv f y v) x) w := by
  let a := circleCut f x
  let V := U ∩ f ⁻¹' ({(a : UnitAddCircle)} : Set UnitAddCircle)ᶜ
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hxV : x ∈ V := ⟨hx, circleCut_ne f x⟩
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (circleBranch f a) V := by
    intro y hy
    exact (hf y hy.1 a hy.2).contDiffWithinAt
  have heq := circleFDeriv_eventuallyEq_lift hV (hf.continuousOn.mono inter_subset_left)
    hu (fun y _ => coe_circleBranch f a y) hxV
  have hp (z : E) : (fun y => circleFDeriv f y z) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ (circleBranch f a) y) z) :=
    heq.mono fun _ h => congrArg (fun L : E →L[ℝ] ℝ => L z) h
  rw [(hp w).fderiv_eq, (hp v).fderiv_eq]
  have huAt := hu.contDiffAt (hV.mem_nhds hxV)
  have hdu : DifferentiableAt ℝ (fderiv ℝ (circleBranch f a)) x :=
    (huAt.fderiv_right (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hdu (differentiableAt_const w),
    fderiv_clm_apply hdu (differentiableAt_const v)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact huAt.isSymmSndFDerivAt (by simp) v w

 theorem circleFDeriv_closed_complex
    {f : ℂ → UnitAddCircle} {U : Set ℂ} (hU : IsOpen U) (hf : SmoothCircleOn f U)
    {z : ℂ} (hz : z ∈ U) :
    (fderiv ℝ (fun x => circleFDeriv f x Complex.I) z) 1 =
      (fderiv ℝ (fun x => circleFDeriv f x 1) z) Complex.I :=
    circleFDeriv_partial_commute hU hf hz 1 Complex.I

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRealLift
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous real lift of a smooth circle map is automatically smooth,
with exactly its intrinsic differential and no additional energy cost. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_real_lift {U : Set E} (hU : IsOpen U)
    {f : E → UnitAddCircle} (hf : SmoothCircleOn f U)
    {u : E → ℝ} (hu : ContinuousOn u U)
    (hproj : ∀ x ∈ U, (u x : UnitAddCircle) = f x) :
    ContDiffOn ℝ ∞ u U := by
  intro x hx
  have hux : ContinuousAt u x := (hu x hx).continuousAt (hU.mem_nhds hx)
  have hb := hf x hx (circleCut f x) (circleCut_ne f x)
  have heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x]
      fun y => (circleBranch f (circleCut f x) y : UnitAddCircle) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hproj y hy, coe_circleBranch]
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hux hb.continuousAt heq
  exact ((hb.add contDiffAt_const).congr_of_eventuallyEq hm).contDiffWithinAt

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCircleStokes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-region Stokes identity and area bound for the actual
intrinsic differential of a smooth circle coordinate. The only additional
published input is the precisely stated classical Green formula. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circleFormIntegral_eq_real_lift
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (γ : ℝ → ℂ) (hγ : Differentiable ℝ γ) (hγO : ∀ t, γ t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) :
    circleFormIntegral φ u γ = ∫ t in (0 : ℝ)..1, φ (γ t) * deriv v t := by
  have hd (t : ℝ) : deriv v t = circleFDeriv u (γ t) (deriv γ t) := by
    have he : fderiv ℝ v t = circleFDeriv (u ∘ γ) t := by
      symm
      apply circleFDeriv_eq_lift
        ((hu.continuousOn.continuousAt (hO.mem_nhds (hγO t))).comp (hγ t).continuousAt)
        hv.continuousAt
      exact Eventually.of_forall hproj
    rw [← fderiv_apply_one_eq_deriv, he, circleFDeriv_comp hO hu (hγ t) (hγO t)]
    simp only [ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv]
  unfold circleFormIntegral planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change (φ (γ t) * circleFDeriv u (γ t) 1) * (deriv γ t).re +
    (φ (γ t) * circleFDeriv u (γ t) Complex.I) * (deriv γ t).im =
    φ (γ t) * deriv v t
  conv_rhs => rw [hd t, complexCovector_apply]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleFormBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual boundary terms for the finite-circle Stokes formula. Smoothness
and integrability of real lifts follow from the circle coordinate, rather
than being extra analytic hypotheses on each boundary. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem contDiff_real_lift_along
    {O : Set ℂ} {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    {v : ℝ → ℝ} (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) :
    ContDiff ℝ (⊤ : ℕ∞) v := by
  apply contDiffOn_univ.mp
  apply contDiffOn_real_lift isOpen_univ _ hv.continuousOn (fun t _ => hproj t)
  intro t _ a ha
  exact (hu (γ t) (hγO t) a ha).comp t hγ.contDiffAt

 theorem circleFormIntegral_constant_weight
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (γ : ℝ → ℂ) (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    (hγO : ∀ t, γ t ∈ O) (v : ℝ → ℝ) (hv : Continuous v)
    (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t))
    (ρ : ℝ) (hφ : ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) = ρ) :
    circleFormIntegral φ u γ = ρ * (v 1 - v 0) := by
  have hvs := contDiff_real_lift_along hu hγ hγO hv hproj
  rw [circleFormIntegral_eq_real_lift hO hu φ γ (hγ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hγO v hv hproj]
  calc
    _ = ∫ t in (0 : ℝ)..1, ρ * deriv v t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change φ (γ t) * deriv v t = ρ * deriv v t
      rw [hφ t (by simpa only [uIcc_of_le zero_le_one] using ht)]
    _ = ρ * (v 1 - v 0) := constant_weight_integral_eq_period v (deriv v) 1 ρ
      (fun t _ => (hvs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt)
      ((hvs.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).intervalIntegrable 0 1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FixedCircuitExclusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single actual smooth source coordinate supplies a fixed real lift
and an open neighborhood of boundary-map/disk data. Its lower integral
is the same functional used to exclude diagonal Stokes limits. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_smooth_real_circuit_lift
    {O : Set ℂ} (hO : IsOpen O) {w : ℂ → UnitAddCircle} (hw : SmoothCircleOn w O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ ∀ t, (v t : UnitAddCircle) = w (γ t) := by
  let : ContractibleSpace (univ : Set ℝ) := convex_univ.contractibleSpace Set.univ_nonempty
  let : LocallyPathConnectedSpace (univ : Set ℝ) := isOpen_univ.locallyPathConnectedSpace
  have hc : Continuous (w ∘ γ) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (hw.continuousOn.continuousAt (hO.mem_nhds (hγO t))).comp hγ.continuous.continuousAt)
  obtain ⟨v, hv, _, hp⟩ := exists_continuous_circle_lift (w ∘ γ) hc.continuousOn
    (mem_univ 0) ((AddCircle.equivIco (1 : ℝ) 0 (w (γ 0))) : ℝ) (by
      simp only [Function.comp_apply, AddCircle.coe_equivIco])
  have hv' := continuousOn_univ.mp hv
  have hp' : ∀ t, (v t : UnitAddCircle) = w (γ t) := fun t => hp t (mem_univ t)
  exact ⟨v, contDiff_real_lift_along hw hγ hγO hv' hp', hp'⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularPieceFlow
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete tangent trajectories on a compact relatively clopen piece of
an actual regular scalar level. This includes a prescribed Jordan boundary
without requiring the other components of its defining level to be bounded. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_regular_piece_flow {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a : ℝ} (ha : IsPlanarRegularValue f a) {K : Set ℂ} (hc : IsCompact K)
    (hK : K ⊆ {z | f z = a}) (ho : IsOpen {z : {w // f w = a} | z.val ∈ K}) :
    Nonempty (CompactRegularPieceFlow f a K) := by
  obtain ⟨V,L,hV,hVc,hVL,ht,hne⟩ := exists_compact_level_tangent hf hc (fun z hz => ha z (hK hz))
  have he (z : K) : ∃ γ : ℝ → ℂ, γ 0 = z.val ∧ ∀ t, HasDerivAt γ (V (γ t)) t :=
    compact_vector_field_global_curve hV hVc z.val
  choose γ hγ0 hγ using he
  have hs (z : K) := smooth_integral_curve hV (hγ z)
  have hscalar (z : K) (t : ℝ) : f (γ z t) = a := by
    calc
      f (γ z t) = f (γ z 0) := integral_curve_preserves_scalar hf ht (hγ z) t 0
      _ = a := by rw [hγ0]; exact hK z.property
  have hm (z : K) (t : ℝ) : γ z t ∈ K := by
    let g : ℝ → {w // f w = a} := fun s => ⟨γ z s,hscalar z s⟩
    have hg : Continuous g := (hs z).continuous.subtype_mk _
    have hcl : IsClopen {w : {y // f y = a} | w.val ∈ K} :=
      ⟨hc.isClosed.preimage continuous_subtype_val,ho⟩
    have hz0 : g 0 ∈ {w : {y // f y = a} | w.val ∈ K} := by
      change γ z 0 ∈ K
      rw [hγ0]
      exact z.property
    exact (isPreconnected_range hg).subset_isClopen hcl ⟨g 0,mem_range_self 0,hz0⟩
      (mem_range_self t)
  refine ⟨⟨V,L,hV,hVc,hVL,ht,hK,γ,hγ0,hγ,hscalar,hm,hs,?_⟩⟩
  intro z t
  rw [(hγ z t).deriv]
  exact hne _ (hm z t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularPieceFlowOrbit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time translation and exact orbit identities for the constructed
regular-level flow. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularPieceFlow.range_eq_of_mem {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) {x y : {z // z ∈ K}}
    (hy : y.val ∈ range (F.trajectory x)) :
    range (F.trajectory y) = range (F.trajectory x) := by
  obtain ⟨s,hs⟩ := hy
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t+s,(F.trajectory_shift_of_eq hs t).symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨t-s,?_⟩
    rw [F.trajectory_shift_of_eq hs,sub_add_cancel]

lemma CompactRegularPieceFlow.orbits_eq_or_disjoint {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x y : {z // z ∈ K}) :
    range (F.trajectory x) = range (F.trajectory y) ∨
      Disjoint (range (F.trajectory x)) (range (F.trajectory y)) := by
  by_cases h : Disjoint (range (F.trajectory x)) (range (F.trajectory y))
  · exact Or.inr h
  · obtain ⟨z,hzx,hzy⟩ := Set.not_disjoint_iff.mp h
    let w : {z // z ∈ K} := ⟨z,by obtain ⟨t,rfl⟩ := hzx; exact F.member x t⟩
    have h1 : range (F.trajectory w) = range (F.trajectory x) := F.range_eq_of_mem hzx
    have h2 : range (F.trajectory w) = range (F.trajectory y) := F.range_eq_of_mem hzy
    exact Or.inl (h1.symm.trans h2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PieceFlowCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonstationary trajectory has nonzero speed in the actual local
one-dimensional coordinate of its regular level. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma piece_flow_coordinate_deriv_ne_zero {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) (t : ℝ)
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (ht : F.trajectory x t ∈ e.source) (he : ∀ z, (e z).1 = f z)
    (hs : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    deriv (fun s => (e (F.trajectory x s)).2) t ≠ 0 := by
  let γ := F.trajectory x
  have hg : ContDiff ℝ ∞ (fun s => (e (γ s)).2) := (hs.comp (F.trajectory_smooth x)).snd
  have hfirst : (fun s => (e (γ s)).1) = (fun _ => a) := by
    funext s
    exact (he (γ s)).trans (F.scalar x s)
  have h1 : HasDerivAt (fun s => (e (γ s)).1) 0 t := by
    rw [hfirst]
    exact hasDerivAt_const t a
  intro hzero
  have h2 : HasDerivAt (fun s => (e (γ s)).2) 0 t := by
    rw [← hzero]
    exact (hg.differentiable (by simp) t).hasDerivAt
  have heγ : HasDerivAt (fun s => e (γ s)) (0 : ℝ × ℝ) t := h1.prodMk h2
  have hei := (hi.contDiffAt (e.open_target.mem_nhds (e.map_source ht))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := hei.hasFDerivAt.comp_hasDerivAt t heγ
  have hfun : (e.symm ∘ fun s => e (γ s)) =ᶠ[𝓝 t] γ := by
    filter_upwards [((F.trajectory_smooth x).continuous.continuousAt).preimage_mem_nhds
      (e.open_source.mem_nhds ht)] with s hs
    exact e.left_inv hs
  have hz : HasDerivAt γ 0 t := by
    simpa only [map_zero] using hd.congr_of_eventuallyEq hfun.symm
  exact F.regular x t hz.deriv

lemma piece_flow_coordinate_open_image {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) (t : ℝ)
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (ht : F.trajectory x t ∈ e.source) (he : ∀ z, (e z).1 = f z)
    (hs : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {U : Set ℝ} (hU : U ∈ 𝓝 t) :
    (fun s => (e (F.trajectory x s)).2) '' U ∈ 𝓝 ((e (F.trajectory x t)).2) := by
  have hg : ContDiff ℝ ∞ (fun s => (e (F.trajectory x s)).2) :=
    (hs.comp (F.trajectory_smooth x)).snd
  have hd := (hg.contDiffAt (x := t)).hasStrictDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [← hd.map_nhds_eq (piece_flow_coordinate_deriv_ne_zero F x t e ht he hs hi)]
  exact Filter.mem_map_iff_exists_image.mpr ⟨U,hU,subset_refl _⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularPieceOpenOrbit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each orbit is open in its actual regular level, as witnessed by the
nonzero derivative of its local level coordinate. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularPieceFlow.continuous_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) : Continuous (F.levelTrajectory x) :=
  (F.trajectory_smooth x).continuous.subtype_mk _

lemma CompactRegularPieceFlow.isOpenMap_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // z ∈ K}) : IsOpenMap (F.levelTrajectory x) := by
  intro B hB
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨t,htB,rfl⟩
  obtain ⟨e,ht,he,hs,hi⟩ := exists_smooth_planar_level_chart hf (ha _ (F.scalar x t))
  let U : Set ℝ := (F.trajectory x) ⁻¹' e.source ∩ B
  have hU : U ∈ 𝓝 t := inter_mem
    ((F.trajectory_smooth x).continuous.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds ht))
    (hB.mem_nhds htB)
  let J := (fun s => (e (F.trajectory x s)).2) '' U
  have hJ : J ∈ 𝓝 ((e (F.trajectory x t)).2) :=
    piece_flow_coordinate_open_image F x t e ht he hs hi hU
  have hcont : Continuous (fun y : {z // z ∈ K} => (e y.val).2) :=
    (hs.continuous.comp continuous_subtype_val).snd
  have hsource : {y : {z // z ∈ K} | y.val ∈ e.source} ∈ 𝓝 (F.levelTrajectory x t) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds ht)
  filter_upwards [hsource,hcont.continuousAt.preimage_mem_nhds hJ] with y hyS hyJ
  obtain ⟨s,hsU,hsJ⟩ := hyJ
  have hsS : F.trajectory x s ∈ e.source := hsU.1
  have hp : e (F.trajectory x s) = e y.val := by
    apply Prod.ext
    · rw [he,he,F.scalar]
      exact F.in_level y.property |>.symm
    · exact hsJ
  have hy : F.levelTrajectory x s = y := Subtype.ext (e.injOn hsS hyS hp)
  exact ⟨s,hsU.2,hy⟩

lemma CompactRegularPieceFlow.isOpen_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // z ∈ K}) : IsOpen (range (F.levelTrajectory x)) := by
  simpa only [image_univ] using F.isOpenMap_levelTrajectory hf ha x univ isOpen_univ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularPieceCompactOrbit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orbits form clopen components of a compact regular level. Their
compactness forces a return for the complete nonstationary flow. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularPieceFlow.mem_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x y : {z // z ∈ K}) :
    y ∈ range (F.levelTrajectory x) ↔ y.val ∈ range (F.trajectory x) := by
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,Subtype.ext ht⟩

lemma CompactRegularPieceFlow.level_orbits_eq_or_disjoint {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x y : {z // z ∈ K}) :
    range (F.levelTrajectory x) = range (F.levelTrajectory y) ∨
      Disjoint (range (F.levelTrajectory x)) (range (F.levelTrajectory y)) := by
  rcases F.orbits_eq_or_disjoint x y with he | hd
  · left
    ext z
    rw [F.mem_range_levelTrajectory,F.mem_range_levelTrajectory,he]
  · right
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact Set.disjoint_left.mp hd ((F.mem_range_levelTrajectory x z).mp hzx)
      ((F.mem_range_levelTrajectory y z).mp hzy)

lemma CompactRegularPieceFlow.isClopen_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // z ∈ K}) : IsClopen (range (F.levelTrajectory x)) := by
  refine ⟨isOpen_compl_iff.mp ?_,F.isOpen_range_levelTrajectory hf ha x⟩
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyself : y ∈ range (F.levelTrajectory y) := ⟨0,Subtype.ext (F.initial y)⟩
  have hdis : Disjoint (range (F.levelTrajectory x)) (range (F.levelTrajectory y)) := by
    rcases F.level_orbits_eq_or_disjoint x y with he | hd
    · exact (hy (he ▸ hyself)).elim
    · exact hd
  exact Filter.mem_of_superset ((F.isOpen_range_levelTrajectory hf ha y).mem_nhds hyself)
    (fun z hz hx => Set.disjoint_left.mp hdis hx hz)

lemma CompactRegularPieceFlow.compact_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact K) (x : {z // z ∈ K}) :
    IsCompact (range (F.levelTrajectory x)) := by
  let : CompactSpace {z // z ∈ K} := isCompact_iff_compactSpace.mp hc
  exact (F.isClopen_range_levelTrajectory hf ha x).isClosed.isCompact

lemma CompactRegularPieceFlow.not_injective_trajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact K) (x : {z // z ∈ K}) :
    ¬ Injective (F.trajectory x) := by
  intro hi
  have hi' : Injective (F.levelTrajectory x) := fun s t h => hi (congrArg Subtype.val h)
  have he := Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (F.continuous_levelTrajectory x) hi' (F.isOpenMap_levelTrajectory hf ha x)
  have hk : IsCompact (univ : Set ℝ) := he.isEmbedding.isCompact_iff.mpr (by
    simpa only [image_univ] using F.compact_range_levelTrajectory hf ha hc x)
  exact noncompact_univ ℝ hk

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularPieceReturn
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness forces a positive return time for each nonstationary
regular-level orbit. Uniqueness turns every return into a true period. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularPieceFlow.return_of_collision {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) {s t : ℝ}
    (hst : F.trajectory x s = F.trajectory x t) :
    F.trajectory x (t-s) = x.val := by
  have h := ODE_solution_unique_univ (v := fun _ : ℝ => F.field)
    (s := fun _ : ℝ => (univ : Set ℂ)) (t₀ := 0)
    (fun _ => F.lipschitz.lipschitzOnWith)
    (fun u => ⟨(F.equation x (u+s)).comp_add_const u s,mem_univ _⟩)
    (fun u => ⟨(F.equation x (u+t)).comp_add_const u t,mem_univ _⟩)
    (by simpa only [zero_add] using hst)
  have he := congrFun h (-s)
  simpa only [neg_add_cancel,neg_add_eq_sub,F.initial] using he.symm

lemma CompactRegularPieceFlow.exists_positive_period {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact K) (x : {z // z ∈ K}) :
    ∃ p > 0, Periodic (F.trajectory x) p := by
  obtain ⟨s,t,hst,hne⟩ := not_injective_iff.mp (F.not_injective_trajectory hf ha hc x)
  have hp := F.periodic_of_return x (F.return_of_collision x hst)
  have hne' : t-s ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases lt_or_gt_of_ne hne' with hneg | hpos
  · exact ⟨-(t-s),neg_pos.mpr hneg,hp.neg⟩
  · exact ⟨t-s,hpos,hp⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularPieceLeastPeriod
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed return subgroup of a nonstationary compact regular-level
trajectory has a least positive element. This is its fundamental period. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularPieceFlow.returnSubgroup_closed {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) :
    IsClosed (F.returnSubgroup x : Set ℝ) :=
  isClosed_eq (F.trajectory_smooth x).continuous continuous_const

lemma CompactRegularPieceFlow.returnSubgroup_not_dense {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) :
    ¬ Dense (F.returnSubgroup x : Set ℝ) := by
  intro hd
  have he : (F.returnSubgroup x : Set ℝ) = univ :=
    (F.returnSubgroup_closed x).closure_eq.symm.trans hd.closure_eq
  have hc : F.trajectory x = fun _ => x.val := by
    funext t
    have ht : t ∈ (F.returnSubgroup x : Set ℝ) := he.symm ▸ mem_univ t
    exact ht
  exact F.regular x 0 (by rw [hc]; simp)

lemma CompactRegularPieceFlow.exists_least_positive_period {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact K) (x : {z // z ∈ K}) :
    ∃ p : ℝ, IsLeast {t | F.trajectory x t = x.val ∧ 0 < t} p := by
  have hb : F.returnSubgroup x ≠ ⊥ := by
    obtain ⟨p,hp,hper⟩ := F.exists_positive_period hf ha hc x
    intro he
    have hm : p ∈ F.returnSubgroup x := by
      change F.trajectory x p = x.val
      simpa only [zero_add] using (hper 0).trans (F.initial x)
    have hz : p = 0 := by simpa only [he, AddSubgroup.mem_bot] using hm
    exact hp.ne' hz
  by_contra hn
  exact F.returnSubgroup_not_dense x
    ((F.returnSubgroup x).dense_of_no_min hb hn)

lemma CompactRegularPieceFlow.injOn_fundamental_interval {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) {p : ℝ}
    (hp : IsLeast {t | F.trajectory x t = x.val ∧ 0 < t} p) :
    InjOn (F.trajectory x) (Ico 0 p) := by
  intro s hs t ht hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hret := F.return_of_collision x hst
    have hle := hp.2 ⟨hret,sub_pos.mpr hlt⟩
    linarith [hs.1, ht.2]
  · have hret := F.return_of_collision x hst.symm
    have hle := hp.2 ⟨hret,sub_pos.mpr hlt⟩
    linarith [ht.1, hs.2]

lemma CompactRegularPieceFlow.range_levelTrajectory_eq_component {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // z ∈ K}) :
    range (F.levelTrajectory x) = connectedComponent x := by
  have hx : x ∈ range (F.levelTrajectory x) := ⟨0,Subtype.ext (F.initial x)⟩
  exact Subset.antisymm
    ((isPreconnected_range (F.continuous_levelTrajectory x)).subset_connectedComponent hx)
    ((F.isClopen_range_levelTrajectory hf ha x).connectedComponent_subset hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularPiecePeriodicParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth embedded circles parametrizing the components of a
compact regular planar level. The parametrization comes from its tangent flow. -/
open Set Function
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularPieceFlow.exists_regular_period_one {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact K) (x : {z // z ∈ K}) :
    ∃ σ : ℝ → ℂ, ContDiff ℝ ∞ σ ∧ Periodic σ 1 ∧ InjOn σ (Ico 0 1) ∧
      (∀ t, deriv σ t ≠ 0) ∧ range σ = Subtype.val '' connectedComponent x := by
  obtain ⟨p,hp⟩ := F.exists_least_positive_period hf ha hc x
  have hp0 : 0 < p := hp.1.2
  have hper := F.periodic_of_return x hp.1.1
  let σ : ℝ → ℂ := fun t => F.trajectory x (p*t)
  have hσ : ContDiff ℝ ∞ σ := (F.trajectory_smooth x).comp (contDiff_const.mul contDiff_id)
  refine ⟨σ,hσ,?_,?_,?_,?_⟩
  · intro t
    dsimp [σ]
    convert hper (p*t) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · intro s hs t ht hst
    have he := F.injOn_fundamental_interval x hp
      (show p*s ∈ Ico 0 p from ⟨mul_nonneg hp0.le hs.1, mul_lt_of_lt_one_right hp0 hs.2⟩)
      (show p*t ∈ Ico 0 p from ⟨mul_nonneg hp0.le ht.1, mul_lt_of_lt_one_right hp0 ht.2⟩) hst
    exact (mul_left_cancel₀ hp0.ne' he)
  · intro t
    have hm : HasDerivAt (fun u : ℝ => p*u) p t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul p
    have hd : HasDerivAt σ (p • F.field (F.trajectory x (p*t))) t :=
      (F.equation x (p*t)).scomp t hm
    rw [hd.deriv]
    apply smul_ne_zero hp0.ne'
    simpa only [(F.equation x (p*t)).deriv] using F.regular x (p*t)
  · have hr : range σ = range (F.trajectory x) := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨p*t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨t/p,?_⟩
        dsimp [σ]
        rw [mul_div_cancel₀ _ hp0.ne']
    rw [hr, ← F.range_levelTrajectory_eq_component hf ha x]
    exact (range_comp Subtype.val (F.levelTrajectory x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_NormalizedArgumentDifferential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth local logarithmic branches and the exact differential of
argument in turns on the punctured plane. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

lemma localArgumentBranch_fderiv {a : ℂ} (ha : a ≠ 0) (v : ℂ) :
    fderiv ℝ (localArgumentBranch a) a v = (v/a).im / (2*Real.pi) := by
  have hsl : a/a ∈ Complex.slitPlane := by simpa only [div_self ha] using Complex.one_mem_slitPlane
  have hd : HasDerivAt (fun w : ℂ => Complex.log (w/a)) a⁻¹ a := by
    simpa only [id_eq, div_self ha, div_one, one_div] using ((hasDerivAt_id a).div_const a).clog hsl
  have hi := Complex.imCLM.hasFDerivAt.comp a (hd.hasFDerivAt.restrictScalars ℝ)
  have hh := (hi.mul_const (2*Real.pi)⁻¹).add_const (Complex.arg a/(2*Real.pi))
  have he : localArgumentBranch a =
      (fun w => (Complex.imCLM (Complex.log (w/a))) * (2*Real.pi)⁻¹ +
        Complex.arg a/(2*Real.pi)) := by
    funext w
    simp only [localArgumentBranch, Complex.imCLM_apply, div_eq_mul_inv]
  dsimp only [Function.comp_def] at hh
  rw [he, hh.fderiv]
  change (2*Real.pi)⁻¹ * (v * a⁻¹).im = _
  simp only [div_eq_mul_inv]
  ring

lemma smoothCircleOn_normalizedArgument :
    SmoothCircleOn normalizedArgument {z : ℂ | z ≠ 0} := by
  apply smoothCircleOn_iff_local_lifts.mpr
  intro a ha
  refine ⟨localArgumentBranch a, localArgumentBranch_smooth ha, ?_⟩
  filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds ha] with w hw
  exact localArgumentBranch_projects ha hw

lemma circleFDeriv_normalizedArgument {a : ℂ} (ha : a ≠ 0) (v : ℂ) :
    circleFDeriv normalizedArgument a v = (v/a).im/(2*Real.pi) := by
  have he : (fun w => (localArgumentBranch a w : UnitAddCircle)) =ᶠ[𝓝 a] normalizedArgument := by
    filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds ha] with w hw
    exact localArgumentBranch_projects ha hw
  rw [circleFDeriv_eq_lift (continuousAt_normalizedArgument ha)
    (localArgumentBranch_smooth ha).continuousAt he]
  exact localArgumentBranch_fderiv ha v

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular Jordan circuits with either orientation. The absolute Stokes
estimate does not need a choice of orientation. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem PositiveJordanParametrization.toRegular
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ) :
    RegularJordanParametrization H γ :=
  ⟨hγ.smooth, hγ.periodic, hγ.injective, hγ.regular, hγ.boundary⟩

 theorem RegularJordanParametrization.mem_frontier
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    γ t ∈ frontier (jordanInterior H) := by
  have he : γ (Int.fract t) = γ t := by
    simpa only [Int.fract, mul_one] using hγ.periodic.sub_int_mul_eq (x := t) ⌊t⌋
  rw [← he]
  exact hγ.boundary ▸ mem_image_of_mem γ
    (show Int.fract t ∈ Icc (0 : ℝ) 1 from ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundCircleParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positively sized round disk and its once-traversed regular
boundary, used to specialize the published Green identity to a disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem unitCircleParam_hasDerivAt (R t : ℝ) :
    HasDerivAt (unitCircleParam 0 R)
      (circleMap 0 R (2*Real.pi*t) * Complex.I * (2*Real.pi)) t := by
  change HasDerivAt (fun s : ℝ => circleMap 0 R (2*Real.pi*s)) _ t
  convert (hasDerivAt_circleMap 0 R (2*Real.pi*t)).scomp t
    ((hasDerivAt_id t).const_mul (2*Real.pi)) using 1 <;>
    (try simp only [Function.comp_def, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_one]) <;>
    first | rfl | ring


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ArgumentCircleIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized angular form has integral one on a positively
traversed round circle. Both the form and its tangent are actual derivatives. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma smoothCircleOn_centeredArgument (c : ℂ) :
    SmoothCircleOn (centeredArgument c) {z | z ≠ c} := by
  intro z hz a ha
  exact (smoothCircleOn_normalizedArgument (z-c) (sub_ne_zero.mpr hz) a ha).comp (f := fun w : ℂ => w-c) z
    (contDiffAt_id.sub contDiffAt_const)

lemma circleFDeriv_centeredArgument (c : ℂ) {z : ℂ} (hz : z ≠ c) (v : ℂ) :
    circleFDeriv (centeredArgument c) z v = (v/(z-c)).im/(2*Real.pi) := by
  have hh := circleFDeriv_comp (f := fun w : ℂ => w-c) (isOpen_ne_fun continuous_id continuous_const)
    smoothCircleOn_normalizedArgument
    (differentiableAt_id.sub (differentiableAt_const c)) (sub_ne_zero.mpr hz)
  change circleFDeriv (normalizedArgument ∘ (fun w : ℂ => w-c)) z v = _
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply, fderiv_sub_const, fderiv_fun_id,
    ContinuousLinearMap.id_apply]
  exact circleFDeriv_normalizedArgument (sub_ne_zero.mpr hz) v

lemma circleFormIntegral_eq_covector (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle) (γ : ℝ → ℂ) :
    circleFormIntegral φ u γ =
      ∫ t in (0 : ℝ)..1, φ (γ t) * circleFDeriv u (γ t) (deriv γ t) := by
  unfold circleFormIntegral planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [Pi.mul_apply]
  conv_rhs => rw [complexCovector_apply]
  ring

lemma unitCircleParam_hasDerivAt_centered (c : ℂ) (r t : ℝ) :
    HasDerivAt (unitCircleParam c r)
      ((unitCircleParam c r t-c) * Complex.I * (2*Real.pi)) t := by
  have he : unitCircleParam c r = fun s => c + unitCircleParam 0 r s := by
    funext s
    simp [unitCircleParam, circleMap]
  rw [he]
  simpa only [unitCircleParam, circleMap, zero_add, add_sub_cancel_left] using
    (unitCircleParam_hasDerivAt r t).const_add c

lemma unitCircleParam_ne_center (c : ℂ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    unitCircleParam c r t ≠ c := circleMap_ne_center hr.ne'

lemma centeredArgument_round_integral (c : ℂ) {r : ℝ} (hr : 0 < r) :
    circleFormIntegral (fun _ => 1) (centeredArgument c) (unitCircleParam c r) = 1 := by
  rw [circleFormIntegral_eq_covector]
  have he (t : ℝ) : (1 : ℝ) * circleFDeriv (centeredArgument c)
      (unitCircleParam c r t) (deriv (unitCircleParam c r) t) = 1 := by
    rw [one_mul, circleFDeriv_centeredArgument c (unitCircleParam_ne_center c hr t),
      (unitCircleParam_hasDerivAt_centered c r t).deriv]
    have hn : unitCircleParam c r t-c ≠ 0 := sub_ne_zero.mpr (unitCircleParam_ne_center c hr t)
    rw [mul_assoc, mul_div_cancel_left₀ _ hn]
    simp [Complex.mul_im]
  simp only [he, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RealInjectiveOpenImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-dimensional open-image fact needed to recognize a Jordan
boundary inside a regular scalar level. Only interval monotonicity and
the intermediate value theorem are used. -/
open Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma real_injective_interval_image_mem_nhds {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b)) (hi : InjOn f (Ioo a b)) :
    f '' Ioo a b ∈ 𝓝 (f x) := by
  obtain ⟨u, hau, hux⟩ := exists_between hx.1
  obtain ⟨v, hxv, hvb⟩ := exists_between hx.2
  have hu : u ∈ Ioo a b := ⟨hau, hux.trans hx.2⟩
  have hv : v ∈ Ioo a b := ⟨hx.1.trans hxv, hvb⟩
  rcases hf.strictMonoOn_of_injOn_Ioo (hx.1.trans hx.2) hi with hm | hm
  · have hux' := hm hu hx hux
    have hxv' := hm hx hv hxv
    apply mem_of_superset (Ioo_mem_nhds hux' hxv')
    exact fun y hy => isPreconnected_Ioo.intermediate_value hu hv hf ⟨hy.1.le, hy.2.le⟩
  · have hvx' := hm hx hv hxv
    have hxu' := hm hu hx hux
    apply mem_of_superset (Ioo_mem_nhds hvx' hxu')
    exact fun y hy => isPreconnected_Ioo.intermediate_value hv hu hf ⟨hy.1.le, hy.2.le⟩

lemma real_open_image_of_continuousOn_injOn {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hi : InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
  exact mem_of_superset (real_injective_interval_image_mem_nhds ⟨hax, hxb⟩
    (hf.mono hab) (hi.mono hab)) (image_mono hab)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OneDimensionalOpenImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local real charts turn a continuous injection between curves into
an open map. This supplies the topology of a regular Jordan boundary. -/
open Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma continuous_injective_local_real_image
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {f : M → N} (hf : Continuous f) (hi : Injective f)
    (c : OpenPartialHomeomorph ℝ M) (d : OpenPartialHomeomorph N ℝ)
    {x : M} (hx : x ∈ c.target) (hfx : f x ∈ d.source)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) : f '' U ∈ 𝓝 (f x) := by
  let V : Set ℝ := c.source ∩ c ⁻¹' (U ∩ f ⁻¹' d.source)
  let g : ℝ → ℝ := fun r => d (f (c r))
  have hV : IsOpen V := c.isOpen_inter_preimage (hU.inter (d.open_source.preimage hf))
  have hcd (r : ℝ) (hr : r ∈ V) : f (c r) ∈ d.source := hr.2.2
  have hg : ContinuousOn g V := d.continuousOn.comp
    (hf.comp_continuousOn (c.continuousOn.mono inter_subset_left)) hcd
  have hgi : InjOn g V := by
    intro r hr s hs he
    exact c.injOn hr.1 hs.1 (hi (d.injOn (hcd r hr) (hcd s hs) he))
  have hG := real_open_image_of_continuousOn_injOn hV hg hgi
  have hGt : g '' V ⊆ d.target := by
    rintro y ⟨r, hr, rfl⟩
    exact d.map_source (hcd r hr)
  have hW : IsOpen (d.symm '' (g '' V)) :=
    d.symm.isOpen_image_of_subset_source hG hGt
  have hcx : c.symm x ∈ V := by
    refine ⟨c.map_target hx, ?_⟩
    change c (c.symm x) ∈ U ∧ f (c (c.symm x)) ∈ d.source
    simpa only [c.right_inv hx] using And.intro hxU hfx
  have hxg : g (c.symm x) = d (f x) := by
    dsimp only [g]
    rw [c.right_inv hx]
  have hxW : f x ∈ d.symm '' (g '' V) :=
    ⟨d (f x), ⟨c.symm x, hcx, hxg⟩, d.left_inv hfx⟩
  apply mem_of_superset (hW.mem_nhds hxW)
  rintro y ⟨s, ⟨r, hr, rfl⟩, rfl⟩
  exact ⟨c r, hr.2.1, (d.left_inv (hcd r hr)).symm⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleRealCharts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit local real charts of the circle and the open-image theorem
for circle embeddings into a real one-manifold. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_real_circle_chart (z : Circle) :
    ∃ c : OpenPartialHomeomorph ℝ Circle, z ∈ c.target := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hhalf : ((1/2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
    intro h
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show (1/2 : ℝ) ∈ Ico 0 (0+1) by norm_num)
      (show (0 : ℝ) ∈ Ico 0 (0+1) by norm_num)).mp h
    norm_num at hh
  obtain ⟨a, ha⟩ : ∃ a : ℝ, e.symm z ≠ (a : AddCircle (1 : ℝ)) := by
    by_cases hz : e.symm z = 0
    · exact ⟨1/2, by simpa only [hz] using hhalf.symm⟩
    · exact ⟨0, hz⟩
  refine ⟨(AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).trans e.toOpenPartialHomeomorph, ?_⟩
  rw [OpenPartialHomeomorph.trans_target]
  exact ⟨mem_univ _, ha⟩

lemma isOpenMap_circle_to_real_manifold {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    {f : Circle → M} (hf : Continuous f) (hi : Injective f) : IsOpenMap f := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨c, hc⟩ := exists_real_circle_chart z
  exact continuous_injective_local_real_image hf hi c (chartAt ℝ (f z))
    hc (mem_chart_source ℝ (f z)) hU hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanArgumentIncrement
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed Green fixes the argument increment of a regular Jordan curve.
The sign is chosen once, before the interior point. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma regular_jordan_argument_increment
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    ∃ e : ℝ, |e| = 1 ∧ ∀ z ∈ jordanInterior H,
      ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
        (∀ t, (v t : UnitAddCircle) = normalizedArgument (γ t-z)) ∧ v 1-v 0 = e := by
  obtain ⟨e, he, hG⟩ := hgreen H γ hγ
  refine ⟨e, he, ?_⟩
  intro z hz
  let O : Set ℂ := {w | w ≠ z}
  have hO : IsOpen O := isOpen_ne_fun continuous_id continuous_const
  have hu : SmoothCircleOn (centeredArgument z) O := smoothCircleOn_centeredArgument z
  have hγO : ∀ t, γ t ∈ O := by
    intro t heq
    have ht := hγ.mem_frontier t
    rw [frontier, (jordanInterior_isOpen H).interior_eq] at ht
    exact ht.2 (heq ▸ hz)
  obtain ⟨v, hv, hp⟩ := exists_smooth_real_circuit_lift hO hu hγ.smooth hγO
  refine ⟨v, hv, hp, ?_⟩
  obtain ⟨r, hr, hrH⟩ := nhds_basis_closedBall.mem_iff.mp ((jordanInterior_isOpen H).mem_nhds hz)
  have hcover : closure (jordanInterior H) \ ⋃ _i : Fin 1, ball z r ⊆ O := by
    intro w hw heq
    subst w
    exact hw.2 (mem_iUnion.mpr ⟨0, mem_ball_self hr⟩)
  have hc := contDiffOn_circleFDeriv hO hu
  have hformula := hG 1 (fun _ => z) (fun _ => r) (fun _ => hr)
    (fun i j hij => (hij (Subsingleton.elim _ _)).elim) (fun _ => hrH) O hO hcover
    (fun w => circleFDeriv (centeredArgument z) w 1)
    (fun w => circleFDeriv (centeredArgument z) w Complex.I)
    (hc.clm_apply contDiffOn_const) (hc.clm_apply contDiffOn_const)
  have hzero : (∫ w in jordanInterior H \ ⋃ _i : Fin 1, closedBall z r,
      fderiv ℝ (fun w => circleFDeriv (centeredArgument z) w Complex.I) w 1 -
        fderiv ℝ (fun w => circleFDeriv (centeredArgument z) w 1) w Complex.I) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro w hw
    have hwO : w ∈ O := hcover ⟨subset_closure hw.1, fun h => hw.2 (by
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩)⟩
    exact sub_eq_zero.mpr (circleFDeriv_closed_complex hO hu hwO)
  have hinner : planarFormIntegral (fun w => circleFDeriv (centeredArgument z) w 1)
      (fun w => circleFDeriv (centeredArgument z) w Complex.I) (unitCircleParam z r) = 1 := by
    simpa only [circleFormIntegral, show (fun _ : ℂ => (1 : ℝ)) = 1 from rfl, one_mul] using centeredArgument_round_integral z hr
  have houter : planarFormIntegral (fun w => circleFDeriv (centeredArgument z) w 1)
      (fun w => circleFDeriv (centeredArgument z) w Complex.I) γ = v 1-v 0 := by
    simpa only [circleFormIntegral, show (fun _ : ℂ => (1 : ℝ)) = 1 from rfl, one_mul] using
      circleFormIntegral_constant_weight hO hu (fun _ => 1) γ hγ.smooth hγO v
        hv.continuous hp 1 (fun _ _ => rfl)
  simp only [Fin.sum_univ_one, hinner, houter, hzero] at hformula
  rcases le_total 0 e with hp | hn
  · rw [abs_of_nonneg hp] at he
    rw [he] at hformula ⊢
    linarith
  · rw [abs_of_nonpos hn] at he
    have he' : e = -1 := by linarith
    rw [he'] at hformula ⊢
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PositiveJordanOrientation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every regular Jordan parametrization has one of two orientations.
The fixed Green sign gives an actual positive parametrization. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma RegularJordanParametrization.injective_Ioc
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) :
    InjOn γ (Ioc 0 1) := by
  intro s hs t ht he
  have h10 : γ 1 = γ 0 := by simpa using hγ.periodic 0
  by_cases hs1 : s = 1
  · by_cases ht1 : t = 1
    · exact hs1.trans ht1.symm
    · have hh : γ 0 = γ t := by simpa only [hs1, h10] using he
      have := hγ.injective (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
        ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩ hh
      linarith [ht.1]
  · by_cases ht1 : t = 1
    · have hh : γ s = γ 0 := by simpa only [ht1, h10] using he
      have := hγ.injective ⟨hs.1.le, lt_of_le_of_ne hs.2 hs1⟩
        (show (0 : ℝ) ∈ Ico 0 1 by norm_num) hh
      linarith [hs.1]
    · exact hγ.injective ⟨hs.1.le, lt_of_le_of_ne hs.2 hs1⟩
        ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩ he

lemma RegularJordanParametrization.reverse
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) :
    RegularJordanParametrization H (fun t => γ (1-t)) := by
  refine ⟨hγ.smooth.comp (contDiff_const.sub contDiff_id), ?_, ?_, ?_, ?_⟩
  · intro t
    change γ (1-(t+1)) = γ (1-t)
    rw [show 1-(t+1) = -t by ring, show 1-t = -t+1 by ring]
    exact (hγ.periodic (-t)).symm
  · intro s hs t ht he
    have hh := hγ.injective_Ioc (show 1-s ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
      (show 1-t ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2]) he
    linarith
  · intro t
    have hi : HasDerivAt (fun s : ℝ => 1-s) (-1) t := by
      simpa only [id_eq, neg_mul, one_mul] using (hasDerivAt_id t).const_sub 1
    have hh := (hγ.smooth.differentiable (by simp) (1-t)).hasDerivAt.scomp t hi
    change deriv (γ ∘ (fun s : ℝ => 1-s)) t ≠ 0
    rw [hh.deriv]
    simpa using hγ.regular (1-t)
  · rw [← hγ.boundary]
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨1-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨1-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
      exact congrArg γ (by ring)

lemma exists_positive_jordan_parametrization
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    ∃ δ : ℝ → ℂ, PositiveJordanParametrization H δ := by
  obtain ⟨e, he, harg⟩ := regular_jordan_argument_increment hgreen H γ hγ
  rcases le_total 0 e with hpos | hneg
  · have he1 : e = 1 := by simpa only [abs_of_nonneg hpos] using he
    refine ⟨γ, hγ.smooth, hγ.periodic, hγ.injective, hγ.regular, hγ.boundary, ?_⟩
    intro z hz
    obtain ⟨v, hv, hp, hi⟩ := harg z hz
    refine ⟨⟨fun t => v t, hv.continuous.comp continuous_subtype_val⟩, (fun t => hp t), ?_⟩
    change v 1 = v 0+1
    linarith
  · have he1 : e = -1 := by rw [abs_of_nonpos hneg] at he; linarith
    have hr := hγ.reverse
    refine ⟨_, hr.smooth, hr.periodic, hr.injective, hr.regular, hr.boundary, ?_⟩
    intro z hz
    obtain ⟨v, hv, hp, hi⟩ := harg z hz
    refine ⟨⟨fun t => v (1-t), hv.continuous.comp
      (continuous_const.sub continuous_subtype_val)⟩, ?_, ?_⟩
    · intro t
      exact hp (1-t)
    · change v (1-1) = v (1-0)+1
      simp only [sub_self, sub_zero]
      linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PositiveJordanIsotopy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.normalizedArgument_standardCirclePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous family of ambient homeomorphisms beginning at the identity
preserves the positive argument increment. No smooth isotopy theorem is assumed. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma jordanInterior_trans (H T : ℂ ≃ₜ ℂ) :
    jordanInterior (H.trans T) = T '' jordanInterior H := by
  change (T ∘ H) '' Metric.ball 0 1 = T '' (H '' Metric.ball 0 1)
  rw [image_image]
  rfl

lemma positiveJordanParametrization_transport
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (T : A → ℂ ≃ₜ ℂ) (hT : Continuous (fun p : A × ℂ => T p.1 p.2))
    (a₀ : A) (h₀ : T a₀ = Homeomorph.refl ℂ)
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ)
    (a : A) (hreg : RegularJordanParametrization (H.trans (T a)) (T a ∘ γ)) :
    PositiveJordanParametrization (H.trans (T a)) (T a ∘ γ) := by
  refine ⟨hreg.smooth, hreg.periodic, hreg.injective, hreg.regular, hreg.boundary, ?_⟩
  intro y hy
  rw [jordanInterior_trans] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hne (b : A) (t : ℝ) : T b (γ t) - T b z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have ht := hγ.toRegular.mem_frontier t
    have he' := (T b).injective he
    rw [he', frontier, (jordanInterior_isOpen H).interior_eq] at ht
    exact ht.2 hz
  let p : A → C(unitInterval, UnitAddCircle) := fun b =>
    ⟨fun t => normalizedArgument (T b (γ t) - T b z), by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (continuousAt_normalizedArgument (hne b t)).comp
        (f := fun t : unitInterval => T b (γ t) - T b z)
        (((T b).continuous.comp (hγ.smooth.continuous.comp continuous_subtype_val)).sub
          continuous_const).continuousAt⟩
  have hp : Continuous p := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_iff_continuousAt.mpr
    intro q
    apply (continuousAt_normalizedArgument (hne q.1 q.2)).comp
      (f := fun q : A × unitInterval => T q.1 (γ q.2) - T q.1 z)
    exact ((hT.comp (continuous_fst.prodMk
      (hγ.smooth.continuous.comp (continuous_subtype_val.comp continuous_snd)))).sub
        (hT.comp (continuous_fst.prodMk continuous_const))).continuousAt
  have hi : Continuous (fun b => circlePathIncrement (p b)) := continuous_circlePathIncrement.comp hp
  have hproj (b : A) : (circlePathIncrement (p b) : UnitAddCircle) = (0 : ℝ) := by
    unfold circlePathIncrement
    rw [AddCircle.coe_sub, realCirclePathLift_projects, realCirclePathLift_projects]
    change normalizedArgument (T b (γ 1) - T b z) -
      normalizedArgument (T b (γ 0) - T b z) = _
    rw [show γ 1 = γ 0 by simpa using hγ.periodic 0, sub_self]
    rfl
  have hc := isLocallyConstant_real_lift_difference hi (continuous_const (y := (0 : ℝ))) hproj
  have he := hc.apply_eq_of_preconnectedSpace a a₀
  obtain ⟨u, hu, hu1⟩ := hγ.positive z hz
  have hstart : circlePathIncrement (p a₀) = 1 := by
    rw [circlePathIncrement_eq_lift (p a₀) u (fun t => by simpa [p, h₀] using hu t), hu1]
    ring
  refine ⟨realCirclePathLift (p a), ?_, ?_⟩
  · exact realCirclePathLift_projects (p a)
  · change circlePathIncrement (p a) - 0 = circlePathIncrement (p a₀) - 0 at he
    rw [hstart] at he
    dsimp only [circlePathIncrement] at he
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPerturbationHomeomorph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small globally Lipschitz perturbations of the identity give actual
ambient homeomorphisms. These are the deformation maps for regular collars. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma smallPerturbationHomeomorph_smooth {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (hs : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (smallPerturbationHomeomorph V hV hL) :=
  contDiff_id.add hs

lemma id_add_fderiv_injective {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) {z : ℂ}
    (hd : DifferentiableAt ℝ V z) :
    Injective (fderiv ℝ (fun w => w + V w) z) := by
  have hb := norm_fderiv_le_of_lipschitz ℝ hV (x₀ := z)
  change Injective (fderiv ℝ (id + V) z)
  rw [fderiv_add differentiableAt_id hd, fderiv_id]
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have he : (fderiv ℝ V z) v = -v := by
    change v + (fderiv ℝ V z) v = 0 at hv
    exact eq_neg_of_add_eq_zero_right hv
  have hh : ‖v‖ ≤ (L : ℝ) * ‖v‖ := by
    calc
      ‖v‖ = ‖(fderiv ℝ V z) v‖ := by rw [he, norm_neg]
      _ ≤ ‖fderiv ℝ V z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hL' : (L : ℝ) < 1 := hL
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPerturbationJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small smooth ambient perturbations preserve regular Jordan curves. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma regularJordanParametrization_smallPerturbation
    {V : ℂ → ℂ} {L : ℝ≥0} (hV : LipschitzWith L V) (hL : L < 1)
    (hs : ContDiff ℝ ∞ V) {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) :
    RegularJordanParametrization (H.trans (smallPerturbationHomeomorph V hV hL))
      (smallPerturbationHomeomorph V hV hL ∘ γ) := by
  let T := smallPerturbationHomeomorph V hV hL
  have hT : ContDiff ℝ ∞ T := smallPerturbationHomeomorph_smooth hV hL hs
  refine ⟨hT.comp hγ.smooth, ?_, ?_, ?_, ?_⟩
  · intro t
    exact congrArg T (hγ.periodic t)
  · intro s hs t ht he
    exact hγ.injective hs ht (T.injective he)
  · intro t he
    have hd := (hT.differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t
      (hγ.smooth.differentiable (by simp) t).hasDerivAt
    have hi : Injective (fderiv ℝ T (γ t)) :=
      id_add_fderiv_injective hV hL (hs.differentiable (by simp) (γ t))
    have hh : fderiv ℝ T (γ t) (deriv γ t) = 0 := by
      rw [← hd.deriv]
      exact he
    exact hγ.regular t (hi (hh.trans (map_zero _).symm))
  · rw [jordanInterior_trans, ← T.image_frontier, ← hγ.boundary, image_image]
    rfl

lemma scaledPerturbationHomeomorph_zero (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) :
    scaledPerturbationHomeomorph V hV hL ⟨0, by norm_num⟩ = Homeomorph.refl ℂ := by
  ext z
  simp

lemma positiveJordanParametrization_smallPerturbation
    {V : ℂ → ℂ} {L : ℝ≥0} (hV : LipschitzWith L V) (hL : L < 1)
    (hs : ContDiff ℝ ∞ V) {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : PositiveJordanParametrization H γ) (ρ : Icc (0 : ℝ) 1) :
    PositiveJordanParametrization (H.trans (scaledPerturbationHomeomorph V hV hL ρ))
      (scaledPerturbationHomeomorph V hV hL ρ ∘ γ) := by
  refine positiveJordanParametrization_transport (scaledPerturbationHomeomorph V hV hL)
    ?_ ⟨0, by norm_num⟩ (scaledPerturbationHomeomorph_zero V hV hL) hγ ρ ?_
  · exact continuous_snd.add
      ((continuous_subtype_val.comp continuous_fst).smul (hV.continuous.comp continuous_snd))
  · exact regularJordanParametrization_smallPerturbation
      (V := fun z => (ρ : ℝ) • V z) _ _ ((contDiff_const (c := (ρ : ℝ))).smul hs) hγ.toRegular

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PerturbedCurveTangent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-parameter deformation has a jointly continuous
classical tangent, including the original boundary at parameter zero. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma perturbedCurve_deriv {V : ℂ → ℂ} {γ : ℝ → ℂ}
    (hV : ContDiff ℝ ∞ V) (hγ : ContDiff ℝ ∞ γ) (ρ t : ℝ) :
    deriv (fun s => γ s+ρ • V (γ s)) t =
      deriv γ t+ρ • deriv (V ∘ γ) t := by
  exact (((hγ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt).add
    (((hV.comp hγ).differentiable (by simp) t).hasDerivAt.const_smul ρ)).deriv

lemma perturbedCurve_tangent_continuous {V : ℂ → ℂ} {γ : ℝ → ℂ}
    (hV : ContDiff ℝ ∞ V) (hγ : ContDiff ℝ ∞ γ) :
    Continuous (fun p : ℝ × ℝ => deriv (fun t => γ t+p.1 • V (γ t)) p.2) := by
  have he : (fun p : ℝ × ℝ => deriv (fun t => γ t+p.1 • V (γ t)) p.2) =
      (fun p => deriv γ p.2+p.1 • deriv (V ∘ γ) p.2) := by
    funext p
    exact perturbedCurve_deriv hV hγ _ _
  rw [he]
  exact ((hγ.continuous_deriv (by simp)).comp continuous_snd).add
    (continuous_fst.smul (((hV.comp hγ).continuous_deriv (by simp)).comp continuous_snd))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_InwardFieldCollar
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit assembly of an inward collar from a small smooth ambient
field. Compact retention follows from the actual inverse displacement bound. -/
open Set Function Filter Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_inward_collar_of_field
    (H : ℂ ≃ₜ ℂ) {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ)
    (V : ℂ → ℂ) (hs : ContDiff ℝ ∞ V) (hc : HasCompactSupport V)
    {L : ℝ≥0} (hV : LipschitzWith L V) (hL : L < 1)
    (hin : ∀ ρ ∈ Ioc (0 : ℝ) 1, ∀ z ∈ frontier (jordanInterior H),
      z+ρ • V z ∈ jordanInterior H) : Nonempty (RegularJordanInwardCollar H) := by
  let disk : ℝ → ℂ ≃ₜ ℂ := fun ρ => if hρ : ρ ∈ Icc (0 : ℝ) 1 then
    H.trans (scaledPerturbationHomeomorph V hV hL ⟨ρ,hρ⟩) else H
  let curve : ℝ → ℝ → ℂ := fun ρ t => γ t+ρ • V (γ t)
  have hdisk (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
      disk ρ = H.trans (scaledPerturbationHomeomorph V hV hL ⟨ρ,hρ⟩) := by
    simp only [disk, dite_eq_left hρ]
  have hcurve (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
      curve ρ = scaledPerturbationHomeomorph V hV hL ⟨ρ,hρ⟩ ∘ γ := rfl
  have hpar (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
      PositiveJordanParametrization (disk ρ) (curve ρ) := by
    rw [hdisk ρ hρ, hcurve ρ hρ]
    exact positiveJordanParametrization_smallPerturbation hV hL hs hγ _
  refine ⟨⟨1, zero_lt_one, curve, disk, ?_, ?_, ?_, hpar, ?_, ?_⟩⟩
  · rw [hdisk 0 (by norm_num), scaledPerturbationHomeomorph_zero]
    rfl
  · exact ((hγ.smooth.continuous.comp continuous_snd).add
      (continuous_fst.smul (hs.continuous.comp (hγ.smooth.continuous.comp continuous_snd)))).continuousOn
  · exact (perturbedCurve_tangent_continuous hs hγ.smooth).continuousOn
  · intro ρ hρ
    apply closed_jordanInterior_subset_of_frontier_subset
    rw [hdisk ρ ⟨hρ.1.le,hρ.2⟩, jordanInterior_trans,
      ← (scaledPerturbationHomeomorph V hV hL ⟨ρ, hρ.1.le,hρ.2⟩).image_frontier]
    rintro z ⟨w, hw, rfl⟩
    exact hin ρ hρ w hw
  · intro K hK hKH
    obtain ⟨d, hd, hthick⟩ := hK.exists_cthickening_subset_open (jordanInterior_isOpen H) hKH
    obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hs.continuous
    have hM0 : 0 ≤ M := (norm_nonneg (V 0)).trans (hM 0)
    let η := min 1 (d/(M+1))
    have hη : 0 < η := lt_min zero_lt_one (div_pos hd (by linarith))
    refine ⟨η, hη, min_le_left _ _, ?_⟩
    intro ρ hρ y hy
    have hρ1 : ρ ∈ Icc (0 : ℝ) 1 := ⟨hρ.1.le,hρ.2.trans (min_le_left _ _)⟩
    let T := scaledPerturbationHomeomorph V hV hL ⟨ρ,hρ1⟩
    have hdist : dist (T.symm y) y ≤ ρ*M := by
      have he : T.symm y+ρ • V (T.symm y) = y := T.apply_symm_apply y
      have hv : T.symm y-y = -(ρ • V (T.symm y)) := by
        calc
          _ = T.symm y-(T.symm y+ρ • V (T.symm y)) := congrArg (fun w => T.symm y-w) he.symm
          _ = _ := by abel
      rw [dist_eq_norm, hv, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1.le]
      exact mul_le_mul_of_nonneg_left (hM _) hρ.1.le
    have hpay : ρ*M ≤ d := by
      have hbound : ρ ≤ d/(M+1) := hρ.2.trans (min_le_right _ _)
      have hmul := (le_div_iff₀ (show 0 < M+1 by linarith)).mp hbound
      nlinarith [hρ.1]
    have hback : T.symm y ∈ jordanInterior H :=
      hthick (mem_cthickening_of_dist_le (T.symm y) y d K hy (hdist.trans hpay))
    rw [hdisk ρ hρ1, jordanInterior_trans]
    exact ⟨T.symm y, hback, T.apply_symm_apply y⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanLocalSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two connected local sides of a Jordan boundary lie on opposite
sides. The proof uses density and regular openness of the actual Jordan disk. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma connected_disjoint_jordan_boundary {S : Set ℂ} (hS : IsPreconnected S)
    (H : ℂ ≃ₜ ℂ) (hd : Disjoint S (frontier (jordanInterior H))) :
    S ⊆ jordanInterior H ∨ S ⊆ (closure (jordanInterior H))ᶜ := by
  apply hS.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
  · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
  · intro z hz
    by_cases hzin : z ∈ jordanInterior H
    · exact Or.inl hzin
    · right
      intro hzc
      apply Set.disjoint_left.mp hd hz
      rw [frontier, (jordanInterior_isOpen H).interior_eq]
      exact ⟨hzc, hzin⟩

lemma jordan_local_sides (H : ℂ ≃ₜ ℂ) {N S T : Set ℂ} {x : ℂ}
    (hN : IsOpen N) (hxN : x ∈ N) (hx : x ∈ frontier (jordanInterior H))
    (hS : IsPreconnected S) (hT : IsPreconnected T)
    (hSf : Disjoint S (frontier (jordanInterior H)))
    (hTf : Disjoint T (frontier (jordanInterior H)))
    (hcover : N ⊆ closure (S ∪ T)) :
    (S ⊆ jordanInterior H ∧ T ⊆ (closure (jordanInterior H))ᶜ) ∨
      (T ⊆ jordanInterior H ∧ S ⊆ (closure (jordanInterior H))ᶜ) := by
  have hxin : x ∉ jordanInterior H := by
    intro hi
    exact hx.2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hi)
  rcases connected_disjoint_jordan_boundary hS H hSf with hSi | hSo <;>
    rcases connected_disjoint_jordan_boundary hT H hTf with hTi | hTo
  · have hc : N ⊆ closure (jordanInterior H) :=
      hcover.trans (closure_mono (union_subset hSi hTi))
    have hi : x ∈ interior (closure (jordanInterior H)) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hN.mem_nhds hxN) hc)
    rw [interior_closure_jordanInterior] at hi
    exact (hxin hi).elim
  · exact Or.inl ⟨hSi, hTo⟩
  · exact Or.inr ⟨hTi, hSo⟩
  · have hc : N ⊆ (jordanInterior H)ᶜ := by
      have hh := hcover.trans (closure_mono (union_subset hSo hTo))
      simpa only [closure_compl, interior_closure_jordanInterior] using hh
    obtain ⟨y, hyN, hyJ⟩ := mem_closure_iff.1 hx.1 N hN hxN
    exact (hc hyN hyJ).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LevelChartJordanSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two halves of an actual scalar-level chart lie on opposite sides
of a Jordan boundary contained in that level. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma level_chart_jordan_sides
    (H : ℂ ≃ₜ ℂ) (f : ℂ → ℝ) (t : ℝ)
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ)) (he : ∀ w, (e w).1 = f w)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t})
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H)) (hxe : x ∈ e.source)
    {r : ℝ} (hr : 0 < r)
    (hbox : Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) ⊆ e.target) :
    (e.symm '' (Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)) ⊆ jordanInterior H ∧
      e.symm '' (Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r)) ⊆
        (closure (jordanInterior H))ᶜ) ∨
    (e.symm '' (Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r)) ⊆ jordanInterior H ∧
      e.symm '' (Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)) ⊆
        (closure (jordanInterior H))ᶜ) := by
  let B := Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)
  let P := Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)
  let M := Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r)
  have hPB : P ⊆ B := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], hq.1.2⟩, hq.2⟩
  have hMB : M ⊆ B := by
    intro q hq
    exact ⟨⟨hq.1.1, by linarith [hq.1.2]⟩, hq.2⟩
  have hx1 : (e x).1 = t := (he x).trans (hlevel hx)
  have hxB : e x ∈ B := by
    exact ⟨⟨by rw [hx1]; linarith, by rw [hx1]; linarith⟩,
      ⟨by linarith, by linarith⟩⟩
  have hN : IsOpen (e.symm '' B) :=
    e.symm.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hbox
  have hSP : IsPreconnected (e.symm '' P) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e.symm
      (e.continuousOn_symm.mono (hPB.trans hbox))
  have hSM : IsPreconnected (e.symm '' M) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e.symm
      (e.continuousOn_symm.mono (hMB.trans hbox))
  have hPf : Disjoint (e.symm '' P) (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨q, hq, rfl⟩ hqf
    have hcoord : q.1 = t := by
      rw [← e.right_inv (hbox (hPB hq)), he]
      exact hlevel hqf
    linarith [hq.1.1]
  have hMf : Disjoint (e.symm '' M) (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨q, hq, rfl⟩ hqf
    have hcoord : q.1 = t := by
      rw [← e.right_inv (hbox (hMB hq)), he]
      exact hlevel hqf
    linarith [hq.1.2]
  have hcover : e.symm '' B ⊆ closure ((e.symm '' P) ∪ (e.symm '' M)) := by
    rintro _ ⟨q, hq, rfl⟩
    have hcont := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (hbox hq))
    rcases le_total t q.1 with hqpos | hqneg
    · apply closure_mono subset_union_left
      apply mem_closure_image hcont
      change q ∈ closure (Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r))
      rw [closure_prod_eq, closure_Ioo (by linarith : t ≠ t+r),
        closure_Ioo (by linarith : (e x).2-r ≠ (e x).2+r)]
      exact ⟨⟨hqpos, hq.1.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
    · apply closure_mono subset_union_right
      apply mem_closure_image hcont
      change q ∈ closure (Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r))
      rw [closure_prod_eq, closure_Ioo (by linarith : t-r ≠ t),
        closure_Ioo (by linarith : (e x).2-r ≠ (e x).2+r)]
      exact ⟨⟨hq.1.1.le, hqneg⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
  exact jordan_local_sides H hN ⟨e x, hxB, e.left_inv hxe⟩ hx hSP hSM hPf hMf hcover

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanLevelComponent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Jordan boundary lying in a regular scalar level is an open compact
connected component of that level, even if the rest of the level is unbounded. -/
open Set Function Filter
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_boundary_open_in_level (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    IsOpen {z : {w : ℂ // f w = t} | z.val ∈ frontier (jordanInterior H)} := by
  let := regularLevelChartedSpace hf ht
  let g : Circle → {w : ℂ // f w = t} := fun z =>
    ⟨H z, hlevel (by rw [frontier_jordanInterior]; exact mem_image_of_mem H z.property)⟩
  have hg : Continuous g := (H.continuous.comp continuous_subtype_val).subtype_mk _
  have hgi : Injective g := by
    intro z w he
    exact Subtype.val_injective (H.injective (congrArg Subtype.val he))
  have ho := (isOpenMap_circle_to_real_manifold hg hgi).isOpen_range
  have he : range g = {z : {w : ℂ // f w = t} | z.val ∈ frontier (jordanInterior H)} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [mem_ofPred_eq, frontier_jordanInterior]
      exact mem_image_of_mem H w.property
    · intro hz
      rw [mem_ofPred_eq, frontier_jordanInterior] at hz
      obtain ⟨w, hw, he⟩ := hz
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩
  rwa [he] at ho

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanBoundaryFlow
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed regular Jordan boundary has an actual regular periodic
parametrization. No circle-classification input is used, and the rest of
its defining scalar level is allowed to be unbounded. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_boundary_parametrization (H : ℂ ≃ₜ ℂ)
    {f : ℂ → ℝ} {t : ℝ} (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    ∃ γ : ℝ → ℂ, RegularJordanParametrization H γ := by
  let K := frontier (jordanInterior H)
  have hK : IsCompact K := (isCompact_closure_jordanInterior H).of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  have hconn : IsConnected K := isConnected_frontier_jordanInterior H
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hconn
  obtain ⟨x,hx⟩ := hconn.nonempty
  obtain ⟨F⟩ := exists_compact_regular_piece_flow hf ht hK hlevel
    (regular_jordan_boundary_open_in_level H hf ht hlevel)
  obtain ⟨γ,hs,hp,hi,hr,himage⟩ := F.exists_regular_period_one hf ht hK ⟨x,hx⟩
  have hfull : range γ = K := by
    rw [himage,PreconnectedSpace.connectedComponent_eq_univ,image_univ,Subtype.range_val]
  refine ⟨γ,hs,hp,hi,hr,?_⟩
  apply Subset.antisymm
  · exact (image_subset_range _ _).trans hfull.subset
  · intro z hz
    have hzr : z ∈ range γ := hfull.symm ▸ (show z ∈ K from hz)
    obtain ⟨s,hsz⟩ := hzr
    refine ⟨Int.fract s,⟨Int.fract_nonneg s,(Int.fract_lt_one s).le⟩,?_⟩
    have he : γ (Int.fract s) = γ s := by
      simpa only [Int.fract,mul_one] using hp.sub_int_mul_eq (x := s) ⌊s⌋
    exact he.trans hsz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PositiveRegularJordanBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact regular-level Jordan boundary admits a positive regular
parametrization, using only the retained circle classification and Green inputs. -/
open Set
open scoped ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_positive_parametrization_of_regular_jordan_boundary
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ} (hf : ContDiff ℝ ∞ f)
    (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    ∃ γ : ℝ → ℂ, PositiveJordanParametrization H γ := by
  obtain ⟨γ, hγ⟩ := regular_jordan_boundary_parametrization H hf ht hlevel
  exact exists_positive_jordan_parametrization hgreen H γ hγ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_LevelChartBox
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric coordinate boxes can be chosen inside any prescribed
ambient neighborhood of a regular level point. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_openPartialHomeomorph_box
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ)) {x : ℂ} (hx : x ∈ e.source)
    {U : Set ℂ} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r > 0, Ioo ((e x).1-r) ((e x).1+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) ⊆
      e.target ∩ e.symm ⁻¹' U := by
  have hW := e.isOpen_inter_preimage_symm hU
  have hxW : e x ∈ e.target ∩ e.symm ⁻¹' U :=
    ⟨e.map_source hx, by simpa only [mem_preimage, e.left_inv hx] using hxU⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hW _ hxW
  refine ⟨r, hr, ?_⟩
  intro q hq
  apply hsub
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> rw [abs_lt] <;> constructor <;> linarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]

lemma regular_jordan_local_side
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t})
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H)) :
    ∃ N : Set ℂ, IsOpen N ∧ x ∈ N ∧
      ((∀ y ∈ N, t < f y → y ∈ jordanInterior H) ∨
        (∀ y ∈ N, f y < t → y ∈ jordanInterior H)) := by
  obtain ⟨e, hxe, he, _, _⟩ := exists_smooth_planar_level_chart hf (ht x (hlevel hx))
  obtain ⟨r, hr, hbox⟩ := exists_openPartialHomeomorph_box e hxe isOpen_univ (mem_univ x)
  have hx1 : (e x).1 = t := (he x).trans (hlevel hx)
  rw [hx1] at hbox
  let B := Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)
  let N := e.symm '' B
  have hBt : B ⊆ e.target := fun _ hy => (hbox hy).1
  refine ⟨N, e.symm.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hBt,
    ⟨e x, ⟨⟨by rw [hx1]; linarith, by rw [hx1]; linarith⟩,
      ⟨by linarith, by linarith⟩⟩, e.left_inv hxe⟩, ?_⟩
  rcases level_chart_jordan_sides H f t e he hlevel hx hxe hr hBt with hp | hm
  · left
    rintro y ⟨q, hq, rfl⟩ hy
    apply hp.1
    refine ⟨q, ⟨⟨?_, hq.1.2⟩, hq.2⟩, rfl⟩
    have heq := congrArg Prod.fst (e.right_inv (hBt hq))
    rw [he] at heq
    linarith
  · right
    rintro y ⟨q, hq, rfl⟩ hy
    apply hm.1
    refine ⟨q, ⟨⟨hq.1.1, ?_⟩, hq.2⟩, rfl⟩
    have heq := congrArg Prod.fst (e.right_inv (hBt hq))
    rw [he] at heq
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanSideChoice
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The choice of the inward scalar-level side is consistent along a
connected Jordan boundary. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_side_incompatible
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t})
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H))
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hxU : x ∈ U) (hxV : x ∈ V)
    (hp : ∀ y ∈ U, t < f y → y ∈ jordanInterior H)
    (hm : ∀ y ∈ V, f y < t → y ∈ jordanInterior H) : False := by
  obtain ⟨e, hxe, he, _, _⟩ := exists_smooth_planar_level_chart hf (ht x (hlevel hx))
  obtain ⟨r, hr, hb⟩ := exists_openPartialHomeomorph_box e hxe (hU.inter hV) ⟨hxU, hxV⟩
  have hx1 : (e x).1 = t := (he x).trans (hlevel hx)
  rw [hx1] at hb
  have hBt : Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) ⊆ e.target :=
    fun _ h => (hb h).1
  have hfq (q : ℝ × ℝ) (hq : q ∈ e.target) : f (e.symm q) = q.1 := by
    rw [← he, e.right_inv hq]
  rcases level_chart_jordan_sides H f t e he hlevel hx hxe hr hBt with h | h
  · let q : ℝ × ℝ := (t-r/2, (e x).2)
    have hq : q ∈ Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r) := by
      constructor <;> constructor <;> dsimp [q] <;> linarith
    have hqb : q ∈ Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) :=
      ⟨⟨hq.1.1, by dsimp [q] <;> linarith⟩, hq.2⟩
    have hj : e.symm q ∈ jordanInterior H := hm _ (hb hqb).2.2 (by
      rw [hfq q (hBt hqb)]; exact hq.1.2)
    exact h.2 ⟨q, hq, rfl⟩ (subset_closure hj)
  · let q : ℝ × ℝ := (t+r/2, (e x).2)
    have hq : q ∈ Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) := by
      constructor <;> constructor <;> dsimp [q] <;> linarith
    have hqb : q ∈ Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) :=
      ⟨⟨by dsimp [q] <;> linarith, hq.1.2⟩, hq.2⟩
    have hj : e.symm q ∈ jordanInterior H := hp _ (hb hqb).2.1 (by
      rw [hfq q (hBt hqb)]; exact hq.1.1)
    exact h.2 ⟨q, hq, rfl⟩ (subset_closure hj)

lemma regular_jordan_global_side
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    ∃ U : Set ℂ, IsOpen U ∧ frontier (jordanInterior H) ⊆ U ∧
      ((∀ y ∈ U, t < f y → y ∈ jordanInterior H) ∨
        (∀ y ∈ U, f y < t → y ∈ jordanInterior H)) := by
  let P : Set ℂ := {x | ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, t < f y → y ∈ jordanInterior H}
  let M : Set ℂ := {x | ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, f y < t → y ∈ jordanInterior H}
  have hP : IsOpen P := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨U, hU, hxU, hp⟩
    exact Filter.mem_of_superset (hU.mem_nhds hxU) (fun y hy => ⟨U, hU, hy, hp⟩)
  have hM : IsOpen M := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨U, hU, hxU, hp⟩
    exact Filter.mem_of_superset (hU.mem_nhds hxU) (fun y hy => ⟨U, hU, hy, hp⟩)
  have hcover : frontier (jordanInterior H) ⊆ P ∪ M := by
    intro x hx
    obtain ⟨U, hU, hxU, hp | hm⟩ := regular_jordan_local_side H hf ht hlevel hx
    · exact Or.inl ⟨U, hU, hxU, hp⟩
    · exact Or.inr ⟨U, hU, hxU, hm⟩
  have hdisj (x : ℂ) (hx : x ∈ frontier (jordanInterior H)) (hp : x ∈ P) (hm : x ∈ M) : False := by
    obtain ⟨U, hU, hxU, hp⟩ := hp
    obtain ⟨V, hV, hxV, hm⟩ := hm
    exact regular_jordan_side_incompatible H hf ht hlevel hx hU hV hxU hxV hp hm
  have halts : frontier (jordanInterior H) ⊆ P ∨ frontier (jordanInterior H) ⊆ M := by
    by_contra! hh
    obtain ⟨x, hx, hxP⟩ := Set.not_subset.mp hh.1
    obtain ⟨y, hy, hyM⟩ := Set.not_subset.mp hh.2
    have hxM : x ∈ M := (hcover hx).resolve_left hxP
    have hyP : y ∈ P := (hcover hy).resolve_right hyM
    obtain ⟨z, hz, hzP, hzM⟩ := (isConnected_frontier_jordanInterior H).isPreconnected
      P M hP hM hcover ⟨y, hy, hyP⟩ ⟨x, hx, hxM⟩
    exact hdisj z hz hzP hzM
  rcases halts with hp | hm
  · refine ⟨P, hP, hp, Or.inl ?_⟩
    rintro y ⟨U, _, hy, h⟩ hf
    exact h y hy hf
  · refine ⟨M, hM, hm, Or.inr ?_⟩
    rintro y ⟨U, _, hy, h⟩ hf
    exact h y hy hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_UniformTransverseDisplacement
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness gives a common displacement width for an actual smooth
transverse field, including retention in a prescribed open neighborhood. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma uniform_transverse_displacement
    {f : ℂ → ℝ} {V : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hV : ContDiff ℝ ∞ V)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hpos : ∀ x ∈ K, 0 < fderiv ℝ f x (V x)) :
    ∃ δ > 0, ∀ x ∈ K, ∀ r ∈ Ioc (0 : ℝ) δ,
      f (x-r • V x) < f x ∧ f x < f (x+r • V x) ∧
        x-r • V x ∈ U ∧ x+r • V x ∈ U := by
  let D : ℝ × ℂ → ℝ := fun p => fderiv ℝ f (p.2+p.1 • V p.2) (V p.2)
  let W : Set (ℝ × ℂ) := {p | 0 < D p ∧ p.2+p.1 • V p.2 ∈ U}
  have hshift : Continuous (fun p : ℝ × ℂ => p.2+p.1 • V p.2) :=
    continuous_snd.add (continuous_fst.smul (hV.continuous.comp continuous_snd))
  have hD : Continuous D :=
    ((hf.continuous_fderiv (by simp)).comp hshift).clm_apply (hV.continuous.comp continuous_snd)
  have hW : IsOpen W := (isOpen_lt continuous_const hD).inter (hU.preimage hshift)
  have hCW : ({0} : Set ℝ) ×ˢ K ⊆ W := by
    rintro ⟨r, x⟩ ⟨hr, hx⟩
    simp only [mem_singleton_iff] at hr
    subst r
    simpa only [W, D, zero_smul, add_zero, mem_ofPred_eq] using And.intro (hpos x hx) (hKU hx)
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_singleton.prod hK).exists_cthickening_subset_open hW hCW
  have hbound (x : ℂ) (hx : x ∈ K) (r : ℝ) (hr : r ∈ Icc (-δ) δ) :
      0 < D (r,x) ∧ x+r • V x ∈ U := by
    apply hthick
    apply mem_cthickening_of_dist_le (r,x) (0,x) δ ({0} ×ˢ K) ⟨rfl, hx⟩
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq, sub_zero]
    exact abs_le.mpr hr
  have hmono (x : ℂ) (hx : x ∈ K) : StrictMonoOn (fun r : ℝ => f (x+r • V x)) (Icc (-δ) δ) := by
    apply strictMonoOn_of_deriv_pos (f := fun r : ℝ => f (x+r • V x)) (convex_Icc _ _) (hf.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    intro r hr
    have hd : HasDerivAt (fun s : ℝ => f (x+s • V x)) (D (r,x)) r := by
      have hi := ((hasDerivAt_id r).smul_const (V x)).const_add x
      have hh := (hf.differentiable (by simp) (x+r • V x)).hasFDerivAt.comp_hasDerivAt r hi
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      simp only [D, one_smul]
    rw [hd.deriv]
    exact (hbound x hx r (interior_subset hr)).1
  refine ⟨δ, hδ, ?_⟩
  intro x hx r hr
  have hneg : -r ∈ Icc (-δ) δ := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hposr : r ∈ Icc (-δ) δ := ⟨by linarith [hr.1], hr.2⟩
  have hlo := hmono x hx hneg hzero (by linarith [hr.1])
  have hhi := hmono x hx hzero hposr hr.1
  simpa only [zero_smul, add_zero, neg_smul, sub_eq_add_neg] using
    And.intro hlo (And.intro hhi (And.intro (hbound x hx (-r) hneg).2 (hbound x hx r hposr).2))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanCollarProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the precise regular Jordan inward collar from
regular level charts and a compactly supported transverse field, using
circle classification and the signed finite Green identity. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_small_inward_field
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ} (hf : ContDiff ℝ ∞ f)
    (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    ∃ (W : ℂ → ℂ) (L : ℝ≥0), ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      LipschitzWith L W ∧ L < 1 ∧
      ∀ ρ ∈ Ioc (0 : ℝ) 1, ∀ z ∈ frontier (jordanInterior H),
        z+ρ • W z ∈ jordanInterior H := by
  let K := frontier (jordanInterior H)
  have hK : IsCompact K := (isCompact_closure_jordanInterior H).of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  obtain ⟨V, L, hs, hc, hV, htrans⟩ := exists_compact_transverse_field hf hK
    (fun z hz => ht z (hlevel hz))
  obtain ⟨U, hU, hKU, hside⟩ := regular_jordan_global_side H hf ht hlevel
  obtain ⟨δ, hδ, hdisp⟩ := uniform_transverse_displacement hf hs hK hU hKU htrans
  let ε : ℝ := min δ (1/(2*((L : ℝ)+1)))
  have hL0 : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hε : 0 < ε := lt_min hδ (by positivity)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεL : ε*(L : ℝ) < 1 := by
    have hh := (le_div_iff₀ (show 0 < 2*((L : ℝ)+1) by positivity)).mp
      (show ε ≤ 1/(2*((L : ℝ)+1)) from min_le_right _ _)
    nlinarith
  have hsmall : ‖ε‖₊*L < 1 := by
    change ‖ε‖*(L : ℝ) < 1
    simpa only [Real.norm_eq_abs, abs_of_pos hε] using hεL
  have hsmallneg : ‖-ε‖₊*L < 1 := by simpa only [nnnorm_neg] using hsmall
  have hr (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) 1) : ρ*ε ∈ Ioc (0 : ℝ) δ :=
    ⟨mul_pos hρ.1 hε, (mul_le_of_le_one_left hε.le hρ.2).trans hεδ⟩
  rcases hside with hp | hm
  · refine ⟨(fun z => ε • V z), ‖ε‖₊*L,
      (contDiff_const (c := ε)).smul hs, hc.smul_left (f := fun _ : ℂ => ε),
      (lipschitzWith_smul ε).comp hV, hsmall, ?_⟩
    intro ρ hρ z hz
    have hh := hdisp z hz (ρ*ε) (hr ρ hρ)
    rw [smul_smul]
    exact hp _ hh.2.2.2 (by rw [← show f z = t from hlevel hz]; exact hh.2.1)
  · refine ⟨(fun z => (-ε) • V z), ‖-ε‖₊*L,
      (contDiff_const (c := -ε)).smul hs, hc.smul_left (f := fun _ : ℂ => -ε),
      (lipschitzWith_smul (-ε)).comp hV, hsmallneg, ?_⟩
    intro ρ hρ z hz
    have hh := hdisp z hz (ρ*ε) (hr ρ hρ)
    have hin := hm _ hh.2.2.1 (by rw [← show f z = t from hlevel hz]; exact hh.1)
    simpa only [smul_smul, mul_neg, neg_smul, smul_neg, sub_eq_add_neg] using hin

 theorem smoothRegularJordanCollars_oai
    (hgreen : UnorientedFiniteCircleGreenFormula) :
    SmoothRegularJordanCollars := by
  intro H f t hf ht hlevel
  obtain ⟨γ, hγ⟩ := exists_positive_parametrization_of_regular_jordan_boundary
    hgreen H hf ht hlevel
  obtain ⟨V, L, hs, hc, hV, hL, hin⟩ := exists_small_inward_field H hf ht hlevel
  exact exists_inward_collar_of_field H hγ V hs hc hV hL hin

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.smoothRegularJordanCollars_oai := @OAI.CircleDomainRigidity.smoothRegularJordanCollars_oai
