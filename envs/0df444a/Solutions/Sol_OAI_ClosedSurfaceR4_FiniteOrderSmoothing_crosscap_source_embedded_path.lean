-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscap_source_embedded_path
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:55:30.529246+00:00
-- url     : https://prove2.me/submissions/5c1cdaf6-c93b-46f6-9212-d6c3ee824cf3

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI000
import Definitions.Def_OAIQ249SI007

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneCurveFrame
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A transverse linear coordinate for a regular curve in the surface plane. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma planeCurveLinear_apply (v w x : Base) :
    planeCurveLinear v w x = x 0 • v+x 1 • w := rfl

theorem exists_plane_curve_frame {w : Base} (hw : w ≠ 0) :
    ∃ v : Base, Function.Bijective (planeCurveLinear v w) := by
  obtain ⟨v,hli⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := ℝ) (M := Base) (by simp [Base]) hw
  refine ⟨v,?_⟩
  have hz : ∀ x, planeCurveLinear v w x = 0 → x = 0 := by
    intro x hx
    have he : x 1 • w+x 0 • v = 0 := by
      rw [add_comm]
      exact hx
    obtain ⟨h1,h0⟩ := (LinearIndependent.pair_iff.mp hli) (x 1) (x 0) he
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hi : Function.Injective (planeCurveLinear v w) := by
    intro x y he
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,he,sub_self]
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (planeCurveLinear v w).toLinearMap) rfl).mp hi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PlaneCurveCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local coordinates straightening a regular curve in the surface plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma planeCurveTube_smooth {c : ℝ → Base} (hc : ContDiff ℝ ∞ c) (v : Base) :
    ContDiff ℝ ∞ (planeCurveTube c v) :=
  (hc.comp (contDiff_apply ℝ ℝ 1)).add ((contDiff_apply ℝ ℝ 0).smul contDiff_const)

lemma planeCurveTube_fderiv {c : ℝ → Base} (hc : ContDiff ℝ ∞ c) (v : Base) (t : ℝ) :
    fderiv ℝ (planeCurveTube c v) ![0,t] = planeCurveLinear v (deriv c t) := by
  have hC := ((hc.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasFDerivAt).comp ![0,t]
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) ![0,t])
  have hV := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) ![0,t]).smul_const v
  have hd := hC.add hV
  change HasFDerivAt (planeCurveTube c v) _ ![0,t] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro x
  simp [planeCurveLinear_apply,fderiv_eq_smul_deriv,add_comm]

theorem plane_curve_coordinates {c : ℝ → Base} (hc : ContDiff ℝ ∞ c)
    (t : ℝ) (ht : deriv c t ≠ 0) :
    ∃ (e : OpenPartialHomeomorph Base Base) (U : Set ℝ),
      IsOpen U ∧ t ∈ U ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ s ∈ U, (![0,s] : Base) ∈ e.source ∧ e ![0,s] = c s := by
  obtain ⟨v,hbij⟩ := exists_plane_curve_frame ht
  let T := planeCurveTube c v
  have hT : ContDiff ℝ ∞ T := planeCurveTube_smooth hc v
  have hD : Function.Bijective (fderiv ℝ T ![0,t]) := by
    rw [planeCurveTube_fderiv hc]
    exact hbij
  let R : Base ≃L[ℝ] Base := ContinuousLinearEquiv.ofBijective (fderiv ℝ T ![0,t])
    (LinearMap.ker_eq_bot.mpr hD.1) (LinearMap.range_eq_top.mpr hD.2)
  have hd : HasFDerivAt T R.toContinuousLinearMap ![0,t] :=
    (hT.differentiable (by simp) _).hasFDerivAt
  let e₀ := hT.contDiffAt.toOpenPartialHomeomorph T hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W := {x : Base | IsUnit (fderiv ℝ T x)}
  have hW : IsOpen W := Units.isOpen.preimage (hT.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  let e := e₀.restrOpen W hW
  have he : (e : Base → Base) = T := rfl
  have htE : (![0,t] : Base) ∈ e.source :=
    ⟨hT.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
      ContinuousLinearMap.isUnit_iff_bijective.mpr hD⟩
  let U := (fun s => (![0,s] : Base)) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (by fun_prop)
  refine ⟨e,U,hU,htE,by simpa only [he] using hT,?_,?_⟩
  · intro y hy
    obtain ⟨u,hu⟩ := (e.map_target hy).2
    let D := ContinuousLinearEquiv.ofUnit u
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he]
      convert (hT.differentiable (by simp) _).hasFDerivAt using 1
      all_goals try with_reducible_and_instances rfl
      exact hu
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hT.contDiffAt)).contDiffWithinAt
  · intro s hs
    refine ⟨hs,?_⟩
    change planeCurveTube c v ![0,s] = c s
    simp [planeCurveTube]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceCurveCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular smooth curve in the surface is the second coordinate
in actual smooth local surface coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_curve_coordinates {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ I) {t : ℝ} (ht : t ∈ I)
    (hreg : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ (c : OpenPartialHomeomorph M Base) (U : Set ℝ),
      IsOpen U ∧ t ∈ U ∧ U ⊆ I ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ∀ s ∈ U, γ s ∈ c.source ∧ c (γ s) = ![0,s] := by
  let p := γ t
  have hp : p ∈ (chart p).source := by
    simpa only [chart_source] using mem_chart_source Plane p
  let W := I ∩ γ ⁻¹' (chart p).source
  have hW : IsOpen W := hγ.continuousOn.isOpen_inter_preimage hI (chart p).open_source
  have htW : t ∈ W := ⟨ht,hp⟩
  have hγt := hγ.contMDiffAt (hI.mem_nhds ht)
  let φ : ℝ → Base := chart p ∘ γ
  have hφ : ContDiffOn ℝ ∞ φ W :=
    ((chart_smooth p).comp (hγ.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  have hφI : Function.Injective (fderiv ℝ φ t) := by
    have hc := ((chart_smooth p).contMDiffAt ((chart p).open_source.mem_nhds hp))
    rw [← mfderiv_eq_fderiv,mfderiv_comp t (hc.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hγt.mdifferentiableAt (by simp))]
    exact ((chart_mdifferentiable p).mfderiv_injective hp).comp hreg
  obtain ⟨V,hV,htV,hVW,F,hF,hFφ⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := t)) hW (singleton_subset_iff.mpr htW) hφ
  have hFe : F =ᶠ[𝓝 t] φ := hFφ.eventuallyEq_of_mem (hV.mem_nhds (htV (by simp)))
  have hFI : Function.Injective (fderiv ℝ F t) := by rw [hFe.fderiv_eq]; exact hφI
  have hFt : deriv F t ≠ 0 := by
    intro hz
    have he : fderiv ℝ F t 1 = fderiv ℝ F t 0 := by
      rw [fderiv_apply_one_eq_deriv,hz,map_zero]
    have hn := hFI he
    norm_num at hn
  obtain ⟨e,J,hJ,htJ,hes,hei,heaxis⟩ := plane_curve_coordinates hF t hFt
  let c := (chart p).trans e.symm
  have hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source := by
    exact hei.contMDiffOn.comp ((chart_smooth p).mono inter_subset_left) (fun _ hx => hx.2)
  have hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target := by
    exact (chart_symm_smooth p).comp hes.contMDiff.contMDiffOn (fun _ hx => hx.2)
  refine ⟨c,V ∩ J,hV.inter hJ,⟨htV (by simp),htJ⟩,
    inter_subset_left.trans (hVW.trans inter_subset_left),hcs,hci,?_⟩
  intro s hs
  have hsW := hVW hs.1
  have hmodel : e ![0,s] = chart p (γ s) := (heaxis s hs.2).2.trans (hFφ hs.1)
  have hsource : γ s ∈ c.source := by
    refine ⟨hsW.2,?_⟩
    change chart p (γ s) ∈ e.target
    rw [← hmodel]
    exact e.map_source (heaxis s hs.2).1
  refine ⟨hsource,?_⟩
  change e.symm (chart p (γ s)) = ![0,s]
  rw [← hmodel]
  exact e.left_inv (heaxis s hs.2).1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual double-locus charts retain smooth coordinate expressions in
both directions. Their overlap maps are ordinary smooth real functions. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma overlap_open (a b : SmoothDoubleChart f) : IsOpen (a.overlap b) :=
  b.coord.continuousOn_symm.isOpen_inter_preimage b.coord.open_target a.coord.open_source

omit [T2Space M] in
theorem transition_smooth (a b : SmoothDoubleChart f) :
    ContDiffOn ℝ ∞ (a.transition b) (a.overlap b) := by
  have hA := (chart_smooth a.left).comp (b.inverse_left_smooth.mono inter_subset_left)
    (fun t (ht : t ∈ a.overlap b) => (a.source_formula (b.coord.symm t) ht.2).1)
  have hB := (chart_smooth a.right).comp (b.inverse_right_smooth.mono inter_subset_left)
    (fun t (ht : t ∈ a.overlap b) => (a.source_formula (b.coord.symm t) ht.2).2.1)
  have hC := a.expression_smooth.comp_contDiffOn (hA.contDiffOn.prodMk hB.contDiffOn)
  apply hC.congr
  intro t ht
  exact (a.source_formula (b.coord.symm t) ht.2).2.2

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleCurveParameter
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular smooth curve lying in an actual double-locus chart has a
smooth local scalar parameter with nonzero derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem curve_parameter (c : SmoothDoubleChart f) {γ : ℝ → surfaceDoublePairs f} {x : ℝ}
    (hc : ContinuousAt γ x) (hx : γ x ∈ c.coord.source)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (γ t).val.1) x)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (γ t).val.2) x)
    (hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x))) :
    ∃ h : ℝ → ℝ, ContDiffAt ℝ ∞ h x ∧ deriv h x ≠ 0 ∧
      h x = c.coord (γ x) ∧ γ =ᶠ[𝓝 x] c.coord.symm ∘ h := by
  let h : ℝ → ℝ := fun t => c.expression
    (chart c.left (γ t).val.1,chart c.right (γ t).val.2)
  have hsource := c.source_formula (γ x) hx
  have hleft := ((chart_smooth c.left).contMDiffAt
    ((chart c.left).open_source.mem_nhds hsource.1)).comp x hA
  have hright := ((chart_smooth c.right).contMDiffAt
    ((chart c.right).open_source.mem_nhds hsource.2.1)).comp x hB
  have hh : ContDiffAt ℝ ∞ h x := c.expression_smooth.contDiffAt.comp x
    (hleft.contDiffAt.prodMk hright.contDiffAt)
  have hnear : ∀ᶠ t in 𝓝 x, γ t ∈ c.coord.source := hc.eventually (c.coord.open_source.mem_nhds hx)
  have he : h =ᶠ[𝓝 x] c.coord ∘ γ := by
    filter_upwards [hnear] with t ht
    exact (c.source_formula (γ t) ht).2.2.symm
  have hval : h x = c.coord (γ x) := he.eq_of_nhds
  have hinv : γ =ᶠ[𝓝 x] c.coord.symm ∘ h := by
    filter_upwards [hnear,he] with t ht ht'
    change γ t = c.coord.symm (h t)
    rw [ht']
    exact (c.coord.left_inv ht).symm
  have htarget : h x ∈ c.coord.target := hval ▸ c.coord.map_source hx
  have hDA := c.inverse_left_smooth.contMDiffAt (c.coord.open_target.mem_nhds htarget)
  have hDB := c.inverse_right_smooth.contMDiffAt (c.coord.open_target.mem_nhds htarget)
  have heA : (fun t => (γ t).val.1) =ᶠ[𝓝 x] (fun t => (c.coord.symm t).val.1) ∘ h :=
    hinv.mono fun _ ht => congrArg (fun p => p.val.1) ht
  have heB : (fun t => (γ t).val.2) =ᶠ[𝓝 x] (fun t => (c.coord.symm t).val.2) ∘ h :=
    hinv.mono fun _ ht => congrArg (fun p => p.val.2) ht
  have hDiffeo := hh.contMDiffAt.mdifferentiableAt (by simp)
  have hAD := heA.mfderiv_eq (I := 𝓘(ℝ)) (I' := planeModel)
  have hBD := heB.mfderiv_eq (I := 𝓘(ℝ)) (I' := planeModel)
  rw [mfderiv_comp x (hDA.mdifferentiableAt (by simp)) hDiffeo] at hAD
  rw [mfderiv_comp x (hDB.mdifferentiableAt (by simp)) hDiffeo] at hBD
  refine ⟨h,hh,?_,hval,hinv⟩
  intro hz
  have hhz : HasDerivAt h 0 x := by
    simpa only [hz] using (hh.differentiableAt (by simp)).hasDerivAt
  have hmf : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) h x (0 : ℝ →L[ℝ] ℝ) := by
    simpa using hhz.hasFDerivAt.hasMFDerivAt
  have hDz := hmf.mfderiv
  rw [hDz] at hAD hBD
  have hA1 := congrArg (fun L => L (1:ℝ)) hAD
  have hB1 := congrArg (fun L => L (1:ℝ)) hBD
  change (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x) 1 =
    (mfderiv 𝓘(ℝ) planeModel (fun t => (c.coord.symm t).val.1) (h x)) 0 at hA1
  change (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x) 1 =
    (mfderiv 𝓘(ℝ) planeModel (fun t => (c.coord.symm t).val.2) (h x)) 0 at hB1
  rw [map_zero] at hA1 hB1
  have h10 :
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x)) 1 =
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x)) 0 := by
    apply Prod.ext
    · exact hA1.trans (map_zero _).symm
    · exact hB1.trans (map_zero _).symm
  have hn := hpair h10
  change (1:ℝ) = 0 at hn
  exact one_ne_zero hn

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_LocalDoubleCurveLift
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A curve locally in the double locus has a continuous local lift to
its actual subtype, with an arbitrary fixed continuation outside the germ. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M]
variable {f : M → ProjectionTarget 3}

theorem local_double_curve_lift {C : ℝ → M × M} {x : ℝ}
    (hC : ContinuousAt C x) (p : surfaceDoublePairs f) (hp : p.val = C x)
    (hgood : ∀ᶠ t in 𝓝 x, C t ∈ surfaceDoublePairs f) :
    ∃ γ : ℝ → surfaceDoublePairs f, ContinuousAt γ x ∧ γ x = p ∧
      (fun t => (γ t).val) =ᶠ[𝓝 x] C := by
  classical
  let γ : ℝ → surfaceDoublePairs f := fun t =>
    if ht : C t ∈ surfaceDoublePairs f then ⟨C t,ht⟩ else p
  have he : (fun t => (γ t).val) =ᶠ[𝓝 x] C := by
    filter_upwards [hgood] with t ht
    dsimp only [γ]
    rw [dite_eq_left ht]
  have hcont : ContinuousAt (fun t => (γ t).val) x := hC.congr_of_eventuallyEq he
  have hγ : ContinuousAt γ x := (Topology.IsInducing.subtypeVal.continuousAt_iff).mpr hcont
  refine ⟨γ,hγ,?_,he⟩
  apply Subtype.ext
  exact he.eq_of_nhds.trans hp.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PairCurveParameter
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth regular pair curve locally contained in the double locus
has the actual chart parameter, with nonzero derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem pair_curve_parameter (c : SmoothDoubleChart f) {C : ℝ → M × M} {x : ℝ}
    (p : surfaceDoublePairs f) (hp : p.val = C x) (hpc : p ∈ c.coord.source)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (C t).1) x)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (C t).2) x)
    (hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (C t).1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (C t).2) x)))
    (hgood : ∀ᶠ t in 𝓝 x, C t ∈ surfaceDoublePairs f) :
    ∃ h : ℝ → ℝ, ContDiffAt ℝ ∞ h x ∧ deriv h x ≠ 0 ∧
      h x = c.coord p ∧ C =ᶠ[𝓝 x] (fun t => (c.coord.symm (h t)).val) := by
  have hC : ContinuousAt C x := hA.continuousAt.prodMk hB.continuousAt
  obtain ⟨γ,hγ,hγx,he⟩ := local_double_curve_lift hC p hp hgood
  have heA : (fun t => (γ t).val.1) =ᶠ[𝓝 x] (fun t => (C t).1) :=
    he.mono fun _ ht => congrArg Prod.fst ht
  have heB : (fun t => (γ t).val.2) =ᶠ[𝓝 x] (fun t => (C t).2) :=
    he.mono fun _ ht => congrArg Prod.snd ht
  have hγA := hA.congr_of_eventuallyEq heA
  have hγB := hB.congr_of_eventuallyEq heB
  have hDA := ((hA.mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq heA).mfderiv
  have hDB := ((hB.mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq heB).mfderiv
  have hγpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x)) := by
    rw [hDA,hDB]
    exact hpair
  obtain ⟨h,hhs,hhn,hval,hinv⟩ := c.curve_parameter hγ (hγx ▸ hpc) hγA hγB hγpair
  refine ⟨h,hhs,hhn,by simpa only [hγx] using hval,?_⟩
  filter_upwards [he,hinv] with t ht ht'
  exact ht.symm.trans (congrArg Subtype.val ht')

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PairCurveSmoothParameter
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chart parameter for a smooth pair curve is smooth on an actual
open neighborhood, as required by the global parameter-germ extension. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem smooth_pair_curve_parameter (c : SmoothDoubleChart f) {C : ℝ → M × M}
    {W : Set ℝ} (hW : IsOpen W) (hC : ContMDiffOn 𝓘(ℝ) (planeModel.prod planeModel) ∞ C W)
    {x : ℝ} (hx : x ∈ W) (p : surfaceDoublePairs f) (hp : p.val = C x) (hpc : p ∈ c.coord.source)
    (hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (C t).1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (C t).2) x)))
    (hgood : ∀ᶠ t in 𝓝 x, C t ∈ surfaceDoublePairs f) :
    ∃ (U : Set ℝ) (h : ℝ → ℝ), IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
      ContDiffOn ℝ ∞ h U ∧ deriv h x ≠ 0 ∧ h x = c.coord p ∧
      C =ᶠ[𝓝 x] (fun t => (c.coord.symm (h t)).val) := by
  have hA : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (C t).1) W :=
    contMDiff_fst.comp_contMDiffOn hC
  have hB : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (C t).2) W :=
    contMDiff_snd.comp_contMDiffOn hC
  obtain ⟨g,hg,hgn,hgv,hginv⟩ := c.pair_curve_parameter p hp hpc
    (hA.contMDiffAt (hW.mem_nhds hx)) (hB.contMDiffAt (hW.mem_nhds hx)) hpair hgood
  let U := W ∩ C ⁻¹' ((chart c.left).source ×ˢ (chart c.right).source)
  have hU : IsOpen U := hC.continuousOn.isOpen_inter_preimage hW
    ((chart c.left).open_source.prod (chart c.right).open_source)
  have hxU : x ∈ U := by
    refine ⟨hx,?_⟩
    change C x ∈ (chart c.left).source ×ˢ (chart c.right).source
    rw [← hp]
    exact ⟨(c.source_formula p hpc).1,(c.source_formula p hpc).2.1⟩
  let h : ℝ → ℝ := fun t => c.expression (chart c.left (C t).1,chart c.right (C t).2)
  have hleft := (chart_smooth c.left).comp (hA.mono (show U ⊆ W from inter_subset_left)) (fun t (ht : t ∈ U) => ht.2.1)
  have hright := (chart_smooth c.right).comp (hB.mono (show U ⊆ W from inter_subset_left)) (fun t (ht : t ∈ U) => ht.2.2)
  have hs : ContDiffOn ℝ ∞ h U := c.expression_smooth.comp_contDiffOn
    (hleft.contDiffOn.prodMk hright.contDiffOn)
  have hgtarget : ∀ᶠ t in 𝓝 x, g t ∈ c.coord.target :=
    hg.continuousAt.eventually (c.coord.open_target.mem_nhds (hgv ▸ c.coord.map_source hpc))
  have he : h =ᶠ[𝓝 x] g := by
    filter_upwards [hginv,hgtarget] with t ht ht'
    change c.expression (chart c.left (C t).1,chart c.right (C t).2) = g t
    rw [ht]
    exact (c.source_formula (c.coord.symm (g t)) (c.coord.map_target ht')).2.2.symm.trans
      (c.coord.right_inv ht')
  refine ⟨U,h,hU,hxU,inter_subset_left,hs,?_,he.eq_of_nhds.trans hgv,?_⟩
  · rw [he.deriv_eq]
    exact hgn
  · filter_upwards [hginv,he] with t ht ht'
    rw [ht']
    exact ht

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InjectivePathConcatenation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concatenating two embedded arcs meeting only at their common endpoint. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] {x y z : X}

theorem path_trans_injective (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hsep : ∀ s t, γ s = δ t → s = 1 ∧ t = 0) : Function.Injective (γ.trans δ) := by
  intro s t h
  apply Subtype.ext
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · have hv := congrArg (fun u : I => (u:ℝ)) (hγ h)
    dsimp only at hv
    linarith
  · obtain ⟨ha,hb⟩ := hsep _ _ h
    have ha' := congrArg (fun u : I => (u:ℝ)) ha
    have hb' := congrArg (fun u : I => (u:ℝ)) hb
    dsimp only at ha' hb'
    norm_num at ha' hb'
    linarith
  · obtain ⟨ha,hb⟩ := hsep _ _ h.symm
    have ha' := congrArg (fun u : I => (u:ℝ)) ha
    have hb' := congrArg (fun u : I => (u:ℝ)) hb
    dsimp only at ha' hb'
    norm_num at ha' hb'
    linarith
  · have hv := congrArg (fun u : I => (u:ℝ)) (hδ h)
    dsimp only at hv
    linarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicPrimitive
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rawPrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (rawPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem rawPrimitive_contDiff {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rawPrimitive f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (rawPrimitive_hasDerivAt hf.continuous x).differentiableAt, ?_⟩
  have he : deriv (rawPrimitive f) = f := by
    funext x
    exact (rawPrimitive_hasDerivAt hf.continuous x).deriv
  rwa [he]

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MonotoneGermExtension
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending an oriented smooth coordinate germ to a globally increasing
smooth real function, with derivative one outside a compact set. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem increasing_smooth_germ_extension {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : 0 < deriv h a) :
    ∃ (g : ℝ → ℝ) (K : Set ℝ), ContDiff ℝ ∞ g ∧ StrictMono g ∧
      g =ᶠ[𝓝 a] h ∧ (∀ x, 0 < deriv g x) ∧ IsCompact K ∧
      ∀ x ∉ K, deriv g x = 1 := by
  have hd : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  let U := {x | 0 < deriv h x}
  have hU : IsOpen U := isOpen_lt continuous_const hd.continuous
  obtain ⟨W,hW,haW,hWU,φ,χ,hφ,hχ,hφc,hχc,hφr,hχr,hχs,hφs,hφone,hχone⟩ :=
    CollarVelocity.nested_compact_cutoffs (isCompact_singleton (x := a)) hU
      (singleton_subset_iff.mpr ha)
  let v : ℝ → ℝ := fun x => φ x * deriv h x + (1-φ x)
  have hv : ContDiff ℝ ∞ v := (hφ.mul hd).add (contDiff_const.sub hφ)
  have hvpos : ∀ x, 0 < v x := by
    intro x
    by_cases hx : x ∈ U
    · have hdpos : 0 < deriv h x := hx
      have hφnonneg := (hφr x).1
      have hφle := (hφr x).2
      by_cases hzero : φ x = 0
      · simp [v,hzero]
      · have hφpos : 0 < φ x := lt_of_le_of_ne hφnonneg (Ne.symm hzero)
        have hmul := mul_pos hφpos hdpos
        dsimp [v]
        linarith
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hin => hx (hφs hin))
      simp [v,hz]
  let g : ℝ → ℝ := fun x => h a +
    PeriodicPrimitive.rawPrimitive v x - PeriodicPrimitive.rawPrimitive v a
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_const.add (PeriodicPrimitive.rawPrimitive_contDiff hv)).sub contDiff_const
  have hgder : ∀ x, deriv g x = v x := by
    intro x
    exact (((PeriodicPrimitive.rawPrimitive_hasDerivAt hv.continuous x).const_add (h a)).sub_const _).deriv
  have hag : g a = h a := by dsimp [g] <;> ring
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW a (haW (by simp))
  have heq : EqOn g h (Metric.ball a r) := by
    apply isOpen_ball.eqOn_of_deriv_eq (convex_ball a r).isPreconnected
      (hg.differentiable (by simp)).differentiableOn (hh.differentiable (by simp)).differentiableOn
    · intro x hx
      rw [hgder]
      dsimp [v]
      rw [hφone x (hrW hx)]
      ring
    · exact Metric.mem_ball_self hr
    · exact hag
  refine ⟨g,tsupport φ,hg,strictMono_of_deriv_pos (fun x => (hgder x) ▸ hvpos x),
    heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
    fun x => (hgder x) ▸ hvpos x,hφc,?_⟩
  intro x hx
  rw [hgder]
  have hz := image_eq_zero_of_notMem_tsupport hx
  simp [v,hz]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MonotoneGermDiffeomorphism
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The increasing extensions are global diffeomorphisms, allowing local
arc coordinates to be joined without changing their germs. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma affine_tails_of_deriv_one {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hd : ∀ x ∉ K, deriv g x = 1) :
    ∃ R cPos cNeg : ℝ, (∀ x, R < x → g x = x+cPos) ∧
      ∀ x, x < -R → g x = x+cNeg := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : ℝ → ℝ)).continuousOn
  let R := |C|+1
  have hout : ∀ x, R < |x| → x ∉ K := by
    intro x hx hin
    have hb := hC x hin
    change ‖x‖ ≤ C at hb
    rw [Real.norm_eq_abs] at hb
    have hc := le_abs_self C
    dsimp [R] at hx
    linarith
  have hplus : EqOn g (fun x => x+(g (R+1)-(R+1))) (Ioi R) := by
    apply isOpen_Ioi.eqOn_of_deriv_eq (convex_Ioi R).isPreconnected
      (hg.differentiable (by simp)).differentiableOn
      (differentiable_id.add_const _).differentiableOn
    · intro x hx
      rw [hd x (hout x (lt_of_lt_of_le hx (le_abs_self x)))]
      simp
    · change R < R+1
      linarith
    · dsimp only [id]
      ring
  have hminus : EqOn g (fun x => x+(g (-R-1)-(-R-1))) (Iio (-R)) := by
    apply isOpen_Iio.eqOn_of_deriv_eq (convex_Iio (-R)).isPreconnected
      (hg.differentiable (by simp)).differentiableOn
      (differentiable_id.add_const _).differentiableOn
    · intro x hx
      have hxr : x < -R := hx
      have habs : R < |x| := by linarith [neg_le_abs x]
      rw [hd x (hout x habs)]
      simp
    · change -R-1 < -R
      linarith
    · dsimp only [id]
      ring
  exact ⟨R,g (R+1)-(R+1),g (-R-1)-(-R-1),fun x hx => hplus hx,fun x hx => hminus hx⟩

lemma surjective_of_deriv_one_off_compact {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hd : ∀ x ∉ K, deriv g x = 1) :
    Function.Surjective g := by
  obtain ⟨R,cPos,cNeg,hplus,hminus⟩ := affine_tails_of_deriv_one hg hK hd
  have htop : Tendsto g atTop atTop := by
    apply (tendsto_atTop_add_const_right atTop cPos tendsto_id).congr'
    filter_upwards [eventually_gt_atTop R] with x hx
    exact (hplus x hx).symm
  have hbot : Tendsto g atBot atBot := by
    apply (tendsto_atBot_add_const_right atBot cNeg tendsto_id).congr'
    filter_upwards [eventually_lt_atBot (-R)] with x hx
    exact (hminus x hx).symm
  exact hg.continuous.surjective htop hbot

theorem increasing_smooth_germ_diffeomorphism {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : 0 < deriv h a) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      StrictMono e ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨g,K,hg,hmono,he,hpos,hK,hd⟩ := increasing_smooth_germ_extension hh a ha
  have hsurj := surjective_of_deriv_one_off_compact hg hK hd
  let e := (hmono.orderIsoOfSurjective g hsurj).toHomeomorph
  have heq : (e : ℝ → ℝ) = g := rfl
  refine ⟨e,by simpa only [heq] using hg,?_,by simpa only [heq] using hmono,by simpa only [heq] using he⟩
  apply e.contDiff_symm_deriv (f' := deriv g)
  · intro x
    exact ne_of_gt (hpos x)
  · intro x
    change HasDerivAt g (deriv g x) x
    exact (hg.differentiable (by simp) x).hasDerivAt
  · simpa only [heq] using hg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalMonotoneTransition
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth oriented transition on an open real interval extends to a
global smooth change of parameter while retaining its germ. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem local_increasing_diffeomorphism {h : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) {a : ℝ}
    (haU : a ∈ U) (ha : 0 < deriv h a) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      StrictMono e ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨W,hW,haW,hWU,H,hH,heq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := a)) hU (singleton_subset_iff.mpr haU) hh
  have he : H =ᶠ[𝓝 a] h := heq.eventuallyEq_of_mem (hW.mem_nhds (haW (by simp)))
  have hd : 0 < deriv H a := by rw [he.deriv_eq]; exact ha
  obtain ⟨e,hes,hei,hem,hee⟩ := increasing_smooth_germ_diffeomorphism hH a hd
  exact ⟨e,hes,hei,hem,hee.trans he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcJoin
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth joining at a common germ, with regularity and injectivity
retained on the two ordered pieces of the parameter interval. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*}

lemma joinedCurve_germ_left (a : ℝ) (γ δ : ℝ → M) {t : ℝ} (ht : t < a) :
    joinedCurve a γ δ =ᶠ[𝓝 t] γ := by
  filter_upwards [eventually_lt_nhds ht] with s hs
  simp only [joinedCurve,ite_eq_left hs.le]

lemma joinedCurve_germ_right (a : ℝ) (γ δ : ℝ → M) {t : ℝ} (ht : a < t) :
    joinedCurve a γ δ =ᶠ[𝓝 t] δ := by
  filter_upwards [eventually_gt_nhds ht] with s hs
  simp only [joinedCurve,ite_eq_right (not_le.mpr hs)]

lemma joinedCurve_germ_center (a : ℝ) {γ δ : ℝ → M} (he : γ =ᶠ[𝓝 a] δ) :
    joinedCurve a γ δ =ᶠ[𝓝 a] γ := by
  filter_upwards [he] with s hs
  dsimp only [joinedCurve]
  split_ifs
  · rfl
  · exact hs.symm

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem joinedCurve_smooth_on (a : ℝ) {γ δ : ℝ → M} {U : Set ℝ}
    (hγ : ∀ t ∈ U, t ≤ a → ContMDiffAt 𝓘(ℝ) I ∞ γ t)
    (hδ : ∀ t ∈ U, a ≤ t → ContMDiffAt 𝓘(ℝ) I ∞ δ t)
    (he : γ =ᶠ[𝓝 a] δ) :
    ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve a γ δ) U := by
  intro t ht
  rcases lt_trichotomy t a with h | heq | h
  · exact ((hγ t ht h.le).congr_of_eventuallyEq (joinedCurve_germ_left a γ δ h)).contMDiffWithinAt
  · subst t
    exact ((hγ a ht le_rfl).congr_of_eventuallyEq (joinedCurve_germ_center a he)).contMDiffWithinAt
  · exact ((hδ t ht h.le).congr_of_eventuallyEq (joinedCurve_germ_right a γ δ h)).contMDiffWithinAt

theorem joinedCurve_regular_on (a : ℝ) {γ δ : ℝ → M} {U : Set ℝ}
    (hγ : ∀ t ∈ U, t ≤ a → Function.Injective (mfderiv 𝓘(ℝ) I γ t))
    (hδ : ∀ t ∈ U, a ≤ t → Function.Injective (mfderiv 𝓘(ℝ) I δ t))
    (he : γ =ᶠ[𝓝 a] δ) :
    ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I (joinedCurve a γ δ) t) := by
  intro t ht
  rcases lt_trichotomy t a with h | heq | h
  · rw [(joinedCurve_germ_left a γ δ h).mfderiv_eq]
    exact hγ t ht h.le
  · subst t
    rw [(joinedCurve_germ_center a he).mfderiv_eq]
    exact hγ a ht le_rfl
  · rw [(joinedCurve_germ_right a γ δ h).mfderiv_eq]
    exact hδ t ht h.le

end Smooth

theorem joinedCurve_injective_on (a : ℝ) (γ δ : ℝ → M) (U : Set ℝ)
    (hγ : (U ∩ Iic a).InjOn γ) (hδ : (U ∩ Ioi a).InjOn δ)
    (hcross : ∀ s ∈ U, s ≤ a → ∀ t ∈ U, a < t → γ s ≠ δ t) :
    U.InjOn (joinedCurve a γ δ) := by
  intro s hs t ht he
  by_cases hsa : s ≤ a <;> by_cases hta : t ≤ a
  · exact hγ ⟨hs,hsa⟩ ⟨ht,hta⟩ (by simpa [joinedCurve,hsa,hta] using he)
  · exact False.elim (hcross s hs hsa t ht (lt_of_not_ge hta) (by simpa [joinedCurve,hsa,hta] using he))
  · exact False.elim (hcross t ht hta s hs (lt_of_not_ge hsa) (by simpa [joinedCurve,hsa,hta] using he.symm))
  · exact hδ ⟨hs,lt_of_not_ge hsa⟩ ⟨ht,lt_of_not_ge hta⟩ (by simpa [joinedCurve,hsa,hta] using he)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactArcJoin
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joining compact parameterized arcs preserves their precise image and
injectivity when their only shared point is the common endpoint. -/
noncomputable section
open Set
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*}

theorem joinedCurve_compact_image (γ δ : ℝ → N) (e : ℝ ≃ₜ ℝ)
    (he : StrictMono e) {l a d : ℝ} (hla : l ≤ a) (had : e a < d)
    (hpoint : γ a = δ (e a)) :
    joinedCurve a γ (δ ∘ e) '' Icc l (e.symm d) =
      γ '' Icc l a ∪ δ '' Icc (e a) d := by
  have haw : a < e.symm d := by
    apply he.lt_iff_lt.mp
    simpa only [e.apply_symm_apply] using had
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    by_cases hta : t ≤ a
    · exact Or.inl ⟨t,⟨ht.1,hta⟩,by simp only [joinedCurve,ite_eq_left hta]⟩
    · refine Or.inr ⟨e t,⟨he.monotone (le_of_not_ge hta),?_⟩,?_⟩
      · simpa only [e.apply_symm_apply] using he.monotone ht.2
      · simp only [joinedCurve,ite_eq_right hta,Function.comp_apply]
  · rintro y (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
    · exact ⟨t,⟨ht.1,ht.2.trans haw.le⟩,by simp only [joinedCurve,ite_eq_left ht.2]⟩
    · have hlow : a ≤ e.symm t := by
        apply he.le_iff_le.mp
        simpa only [e.apply_symm_apply] using ht.1
      have hhigh : e.symm t ≤ e.symm d := (he.le_iff_le).mp (by simpa using ht.2)
      refine ⟨e.symm t,⟨hla.trans hlow,hhigh⟩,?_⟩
      by_cases hta : e.symm t ≤ a
      · have hta' : e.symm t = a := le_antisymm hta hlow
        have ht' : t = e a := by simpa only [e.apply_symm_apply] using congrArg e hta'
        rw [hta',ht']
        simpa only [joinedCurve,le_refl,ite_true, if_true] using hpoint
      · simp only [joinedCurve,ite_eq_right hta,Function.comp_apply,e.apply_symm_apply]

theorem joinedCurve_compact_injective (γ δ : ℝ → N) (e : ℝ ≃ₜ ℝ)
    (he : StrictMono e) {l a d : ℝ}
    (hγ : (Icc l a).InjOn γ) (hδ : (Icc (e a) d).InjOn δ)
    (hcross : ∀ s ∈ Icc l a, ∀ t ∈ Ioc (e a) d, γ s ≠ δ t) :
    (Icc l (e.symm d)).InjOn (joinedCurve a γ (δ ∘ e)) := by
  apply joinedCurve_injective_on
  · intro x hx y hy hxy
    exact hγ ⟨hx.1.1,hx.2⟩ ⟨hy.1.1,hy.2⟩ hxy
  · intro x hx y hy hxy
    apply e.injective
    apply hδ _ _ hxy
    · exact ⟨(he hx.2).le,by simpa only [e.apply_symm_apply] using he.monotone hx.1.2⟩
    · exact ⟨(he hy.2).le,by simpa only [e.apply_symm_apply] using he.monotone hy.1.2⟩
  · intro x hx hxa y hy hay
    exact hcross x ⟨hx.1,hxa⟩ (e y)
      ⟨he hay,by simpa only [e.apply_symm_apply] using he.monotone hy.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothCompactArc
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact regular embedded smooth arcs, and the actual joining operation
for arcs meeting through an oriented smooth parameter germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (N : Type*) [TopologicalSpace N] [ChartedSpace H N]

namespace SmoothCompactArc
variable {I N}

theorem join_with_parameter (P Q : SmoothCompactArc I N) (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hem : StrictMono e)
    (hea : e P.finish = Q.start)
    (hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ e)
    (hcross : ∀ s ∈ Icc P.start P.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.curve s ≠ Q.curve t) :
    ∃ R : SmoothCompactArc I N,
      R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve = joinedCurve P.finish P.curve (Q.curve ∘ e) ∧
      R.curve '' Icc R.start R.finish =
        P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish := by
  have haw : P.finish < e.symm Q.finish := by
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact Q.start_lt_finish
  let V := e ⁻¹' Q.domain
  let U := (P.domain ∩ Iio P.finish) ∪ (V ∩ Ioi P.finish) ∪ (P.domain ∩ V)
  have hV : IsOpen V := Q.domain_open.preimage e.continuous
  have hU : IsOpen U := (P.domain_open.inter isOpen_Iio).union (hV.inter isOpen_Ioi) |>.union (P.domain_open.inter hV)
  have hleft : ∀ t ∈ U, t ≤ P.finish → t ∈ P.domain := by
    intro t ht hta
    rcases ht with (ht | ht) | ht
    · exact ht.1
    · exact False.elim (not_lt_of_ge hta ht.2)
    · exact ht.1
  have hright : ∀ t ∈ U, P.finish ≤ t → e t ∈ Q.domain := by
    intro t ht hat
    rcases ht with (ht | ht) | ht
    · exact False.elim (not_lt_of_ge hat ht.2)
    · exact ht.1
    · exact ht.2
  have hsub : Icc P.start (e.symm Q.finish) ⊆ U := by
    intro t ht
    rcases lt_trichotomy t P.finish with h | rfl | h
    · exact Or.inl (Or.inl ⟨P.interval_subset ⟨ht.1,h.le⟩,h⟩)
    · exact Or.inr ⟨P.interval_subset (right_mem_Icc.mpr P.start_lt_finish.le),by
        change e P.finish ∈ Q.domain
        rw [hea]
        exact Q.interval_subset (left_mem_Icc.mpr Q.start_lt_finish.le)⟩
    · refine Or.inl (Or.inr ⟨?_,h⟩)
      apply Q.interval_subset
      refine ⟨?_,?_⟩
      · rw [← hea]; exact (hem h).le
      · simpa only [e.apply_symm_apply] using hem.monotone ht.2
  have hdif : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  have hsmooth : ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve P.finish P.curve (Q.curve ∘ e)) U := by
    apply joinedCurve_smooth_on
    · intro t ht hta
      exact P.smooth.contMDiffAt (P.domain_open.mem_nhds (hleft t ht hta))
    · intro t ht hat
      exact (Q.smooth.contMDiffAt (Q.domain_open.mem_nhds (hright t ht hat))).comp t hes.contMDiff.contMDiffAt
    · exact hmatch
  have hregular : ∀ t ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ) I (joinedCurve P.finish P.curve (Q.curve ∘ e)) t) := by
    apply joinedCurve_regular_on
    · intro t ht hta
      exact P.regular t (hleft t ht hta)
    · intro t ht hat
      rw [mfderiv_comp t
        ((Q.smooth.contMDiffAt (Q.domain_open.mem_nhds (hright t ht hat))).mdifferentiableAt (by simp))
        (hes.contMDiff.mdifferentiable (by simp) t)]
      exact (Q.regular _ (hright t ht hat)).comp (hdif.mfderiv_injective (mem_univ t))
    · exact hmatch
  have hinj := joinedCurve_compact_injective P.curve Q.curve e hem P.injective
    (by simpa only [hea] using Q.injective) (by simpa only [hea] using hcross)
  let R : SmoothCompactArc I N := ⟨_,P.start,e.symm Q.finish,
    P.start_lt_finish.trans haw,U,hU,hsub,hsmooth,hregular,hinj⟩
  refine ⟨R,rfl,rfl,rfl,?_⟩
  exact (joinedCurve_compact_image P.curve Q.curve e hem P.start_lt_finish.le
    (by rw [hea]; exact Q.start_lt_finish) hmatch.eq_of_nhds).trans (by rw [hea])

theorem join (P Q : SmoothCompactArc I N) {h : ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) (hh : ContDiffOn ℝ ∞ h V) (haV : P.finish ∈ V)
    (hpos : 0 < deriv h P.finish) (hea : h P.finish = Q.start)
    (hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ h)
    (hcross : ∀ s ∈ Icc P.start P.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.curve s ≠ Q.curve t) :
    ∃ (R : SmoothCompactArc I N) (e : ℝ ≃ₜ ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
      e P.finish = Q.start ∧ R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve = joinedCurve P.finish P.curve (Q.curve ∘ e) ∧
      R.curve '' Icc R.start R.finish =
        P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish := by
  obtain ⟨e,hes,hei,hem,he⟩ := local_increasing_diffeomorphism hV hh haV hpos
  have he' : e P.finish = Q.start := he.eq_of_nhds.trans hea
  have hm : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ e := by
    filter_upwards [hmatch,he] with t ht ht'
    exact ht.trans (congrArg Q.curve ht'.symm)
  obtain ⟨R,hR⟩ := P.join_with_parameter Q e hes hei hem he' hm hcross
  exact ⟨R,e,hes,hei,hem,he',hR⟩

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ArcJoinOrientation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orientation required for joining is forced by separation of the
old and new compact arc interiors. It is not an additional geometric choice. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*}

theorem arc_join_deriv_pos {γ δ : ℝ → N} {h : ℝ → ℝ} {l a c d : ℝ}
    (hla : l < a) (hcd : c < d) (hh : DifferentiableAt ℝ h a)
    (hne : deriv h a ≠ 0) (ha : h a = c)
    (he : γ =ᶠ[𝓝 a] δ ∘ h)
    (hcross : ∀ s ∈ Icc l a, ∀ t ∈ Ioc c d, γ s ≠ δ t) :
    0 < deriv h a := by
  have hsmall : ∀ᶠ t in 𝓝 a, l < t ∧ h t < d :=
    (eventually_gt_nhds hla).and (hh.continuousAt.eventually (gt_mem_nhds (ha ▸ hcd)))
  have hslope : ∀ᶠ t in 𝓝[<] a, 0 ≤ slope h a t := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,
      he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht heq hta
    have hc : h t ≤ c := by
      by_contra hc
      exact hcross t ⟨ht.1.le,hta.le⟩ (h t) ⟨lt_of_not_ge hc,ht.2.le⟩ heq
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr (ha ▸ hc)) (sub_nonpos.mpr hta.le)
  have hlim := (hasDerivAt_iff_tendsto_slope_left_right.mp hh.hasDerivAt).1
  exact lt_of_le_of_ne (ge_of_tendsto hlim hslope) hne.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleTransitions
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transition functions of the actual smooth double-locus charts
have smooth local inverses and nonzero derivative. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

omit [IsManifold planeModel ∞ M] in
lemma transition_mem_overlap (a b : SmoothDoubleChart f) {t : ℝ} (ht : t ∈ a.overlap b) :
    a.transition b t ∈ b.overlap a := by
  refine ⟨a.coord.map_source ht.2,?_⟩
  change a.coord.symm (a.coord (b.coord.symm t)) ∈ b.coord.source
  rw [a.coord.left_inv ht.2]
  exact b.coord.map_target ht.1

omit [IsManifold planeModel ∞ M] in
lemma transition_inverse (a b : SmoothDoubleChart f) {t : ℝ} (ht : t ∈ a.overlap b) :
    b.transition a (a.transition b t) = t := by
  change b.coord (a.coord.symm (a.coord (b.coord.symm t))) = t
  rw [a.coord.left_inv ht.2,b.coord.right_inv ht.1]

theorem transition_derivative_product (a b : SmoothDoubleChart f) {t : ℝ}
    (ht : t ∈ a.overlap b) :
    deriv (b.transition a) (a.transition b t) * deriv (a.transition b) t = 1 := by
  have hF : DifferentiableAt ℝ (a.transition b) t :=
    ((a.transition_smooth b).contDiffAt ((a.overlap_open b).mem_nhds ht)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hG : DifferentiableAt ℝ (b.transition a) (a.transition b t) :=
    ((b.transition_smooth a).contDiffAt ((b.overlap_open a).mem_nhds
      (a.transition_mem_overlap b ht))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : (b.transition a) ∘ (a.transition b) =ᶠ[𝓝 t] id := by
    filter_upwards [(a.overlap_open b).mem_nhds ht] with s hs
    exact a.transition_inverse b hs
  have hd := deriv_comp t hG hF
  rw [he.deriv_eq,deriv_id] at hd
  exact hd.symm

lemma transition_derivative_ne_zero (a b : SmoothDoubleChart f) {t : ℝ}
    (ht : t ∈ a.overlap b) : deriv (a.transition b) t ≠ 0 := by
  intro hz
  have h := a.transition_derivative_product b ht
  rw [hz,mul_zero] at h
  norm_num at h

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OrientedChartArc
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded compact arc lying in one real chart has an oriented smooth
coordinate parameterization with exactly the original image and endpoints. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {N : Type*} [TopologicalSpace N]

theorem oriented_chart_arc (c : OpenPartialHomeomorph N ℝ) {γ : ℝ → N}
    {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) (hsource : MapsTo γ (Icc a b) c.source) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      let u := s * c (γ a)
      let v := s * c (γ b)
      u < v ∧
      (∀ t ∈ Icc u v, s * t ∈ c.target) ∧
      (fun t => c.symm (s * t)) '' Icc u v = γ '' Icc a b ∧
      (Icc u v).InjOn (fun t => c.symm (s * t)) ∧
      c.symm (s * u) = γ a ∧ c.symm (s * v) = γ b := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hc : ContinuousOn (fun t => c (γ t)) (Icc a b) :=
    c.continuousOn.comp hγ hsource
  have hi : InjOn (fun t => c (γ t)) (Icc a b) :=
    c.injOn.comp hinj hsource
  have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      StrictMonoOn (fun t => s * c (γ t)) (Icc a b) := by
    rcases hc.strictMonoOn_of_injOn_Icc' hab.le hi with hm | hm
    · exact ⟨1,Or.inl rfl,by simpa only [one_mul] using hm⟩
    · refine ⟨-1,Or.inr rfl,?_⟩
      intro x hx y hy hxy
      simpa only [neg_one_mul,neg_lt_neg_iff] using hm hx hy hxy
  obtain ⟨s,hs,hm⟩ := hs
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have himage : (fun t => s * c (γ t)) '' Icc a b =
      Icc (s*c (γ a)) (s*c (γ b)) :=
    (continuousOn_const.mul hc).image_Icc_of_monotoneOn hab.le hm.monotoneOn
  have htarget : ∀ t ∈ Icc (s*c (γ a)) (s*c (γ b)), s*t ∈ c.target := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := himage.symm.subset ht
    simpa only [← mul_assoc,hss,one_mul] using c.map_source (hsource hx)
  refine ⟨s,hs,hm ha hb hab,htarget,?_,?_,?_,?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      obtain ⟨x,hx,rfl⟩ := himage.symm.subset ht
      refine ⟨x,hx,?_⟩
      dsimp only
      rw [← mul_assoc,hss,one_mul,c.left_inv (hsource hx)]
    · rintro y ⟨x,hx,rfl⟩
      refine ⟨s*c (γ x),himage.subset ⟨x,hx,rfl⟩,?_⟩
      dsimp only
      rw [← mul_assoc,hss,one_mul,c.left_inv (hsource hx)]
  · intro x hx y hy he
    exact mul_left_cancel₀ hs0 (c.symm.injOn (htarget x hx) (htarget y hy) he)
  · rw [← mul_assoc,hss,one_mul,c.left_inv (hsource ha)]
  · rw [← mul_assoc,hss,one_mul,c.left_inv (hsource hb)]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OrientedDoubleChartArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth regular embedded arc pieces in the double locus,
with the image and endpoint order of the original topological arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem oriented_arc (c : SmoothDoubleChart f) {γ : ℝ → surfaceDoublePairs f}
    {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) (hsource : MapsTo γ (Icc a b) c.coord.source) :
    ∃ (P : SmoothCompactArc (planeModel.prod planeModel) (M × M)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧
      P.curve = (fun t => (c.coord.symm (s*t)).val) ∧
      P.start = s*c.coord (γ a) ∧ P.finish = s*c.coord (γ b) ∧
      P.curve '' Icc P.start P.finish = (fun t => (γ t).val) '' Icc a b ∧
      P.curve P.start = (γ a).val ∧ P.curve P.finish = (γ b).val := by
  obtain ⟨s,hs,hab',htarget,himage,hi,hleft,hright⟩ :=
    oriented_chart_arc c.coord hab hγ hinj hsource
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  let V : Set ℝ := (fun t : ℝ => s*t) ⁻¹' c.coord.target
  have hV : IsOpen V := c.coord.open_target.preimage (continuous_const.mul continuous_id)
  have hVsub : Icc (s*c.coord (γ a)) (s*c.coord (γ b)) ⊆ V := htarget
  have hlin : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => s*t) :=
    (contDiff_const.mul contDiff_id).contMDiff
  have hA : ContMDiffOn 𝓘(ℝ) planeModel ∞
      (fun t => (c.coord.symm (s*t)).val.1) V :=
    c.inverse_left_smooth.comp hlin.contMDiffOn (fun _ ht => ht)
  have hB : ContMDiffOn 𝓘(ℝ) planeModel ∞
      (fun t => (c.coord.symm (s*t)).val.2) V :=
    c.inverse_right_smooth.comp hlin.contMDiffOn (fun _ ht => ht)
  have hregular : ∀ t ∈ V, Function.Injective
      (mfderiv 𝓘(ℝ) (planeModel.prod planeModel) (fun t => (c.coord.symm (s*t)).val) t) := by
    intro t ht
    have hAt := c.inverse_left_smooth.contMDiffAt (c.coord.open_target.mem_nhds ht)
    have hBt := c.inverse_right_smooth.contMDiffAt (c.coord.open_target.mem_nhds ht)
    have hDt := hlin.mdifferentiable (by simp) t
    let e := Homeomorph.mulLeft₀ s hs0
    have hei : ContDiff ℝ ∞ e.symm := by
      change ContDiff ℝ ∞ (fun t : ℝ => s⁻¹*t)
      exact contDiff_const.mul contDiff_id
    have he : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
      ⟨hlin.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.mdifferentiableOn,
        hei.contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.mdifferentiableOn⟩
    have hD : Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => s*t) t) :=
      he.mfderiv_injective (mem_univ t)
    have hdA := (hAt.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hDt.hasMFDerivAt
    have hdB := (hBt.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hDt.hasMFDerivAt
    have hd := (hdA.prodMk hdB).mfderiv
    have hj : Function.Injective
        (((mfderiv 𝓘(ℝ) planeModel (fun t => (c.coord.symm t).val.1) (s*t)).comp
            (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => s*t) t)).prod
          ((mfderiv 𝓘(ℝ) planeModel (fun t => (c.coord.symm t).val.2) (s*t)).comp
            (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => s*t) t))) := by
      intro x y hxy
      apply hD
      exact c.inverse_regular (s*t) ht hxy
    exact hd.symm ▸ hj
  let P : SmoothCompactArc (planeModel.prod planeModel) (M × M) :=
    ⟨_,s*c.coord (γ a),s*c.coord (γ b),hab',V,hV,hVsub,
      hA.prodMk hB,hregular,fun _ hx _ hy he => hi hx hy (Subtype.val_injective he)⟩
  refine ⟨P,s,hs,rfl,rfl,rfl,?_,?_,?_⟩
  · change (Subtype.val ∘ (fun t => c.coord.symm (s*t))) ''
      Icc (s*c.coord (γ a)) (s*c.coord (γ b)) = (Subtype.val ∘ γ) '' Icc a b
    rw [Set.image_comp,himage,← Set.image_comp]
  · exact congrArg Subtype.val hleft
  · exact congrArg Subtype.val hright

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OrientedDoubleTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transitions between oriented double-curve parameters remain local
smooth diffeomorphisms after a global smooth reparameterization. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma smooth_real_homeomorph_deriv_ne_zero (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (x : ℝ) : deriv e x ≠ 0 := by
  have heq : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  have hd := deriv_comp x ((hei.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (e x)) ((hes.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) x)
  rw [heq,deriv_id] at hd
  intro hz
  rw [hz,mul_zero] at hd
  norm_num at hd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem reparameterized_transition (c d : SmoothDoubleChart f)
    {s t : ℝ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (e : ℝ ≃ₜ ℝ) (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    {x : ℝ} (hx : s*e x ∈ d.overlap c) :
    ∃ (U : Set ℝ) (h : ℝ → ℝ), IsOpen U ∧ x ∈ U ∧
      ContDiffOn ℝ ∞ h U ∧ deriv h x ≠ 0 ∧
      h x = t*d.coord (c.coord.symm (s*e x)) ∧
      (fun u => c.coord.symm (s*e u)) =ᶠ[𝓝 x] (fun u => d.coord.symm (t*h u)) := by
  let k : ℝ → ℝ := fun u => s*e u
  let U := k ⁻¹' d.overlap c
  let h : ℝ → ℝ := fun u => t*d.transition c (k u)
  have hk : ContDiff ℝ ∞ k := contDiff_const.mul hes
  have hU : IsOpen U := (d.overlap_open c).preimage hk.continuous
  have hxU : x ∈ U := hx
  have hhs : ContDiffOn ℝ ∞ h U := contDiffOn_const.mul
    ((d.transition_smooth c).comp hk.contDiffOn (fun _ hu => hu))
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  have htt : t*t = 1 := by rcases ht with rfl | rfl <;> norm_num
  have hcD := ((d.transition_smooth c).contDiffAt ((d.overlap_open c).mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := ((hcD.hasDerivAt.comp x (((hes.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) x).hasDerivAt.const_mul s)).const_mul t).deriv
  have hn : deriv h x ≠ 0 := by
    change deriv (fun u => t*d.transition c (s*e u)) x ≠ 0
    dsimp only [Function.comp_def] at hd
    rw [hd]
    exact mul_ne_zero ht0 (mul_ne_zero (d.transition_derivative_ne_zero c hx)
      (mul_ne_zero hs0 (smooth_real_homeomorph_deriv_ne_zero e hes hei x)))
  refine ⟨U,h,hU,hxU,hhs,hn,rfl,?_⟩
  filter_upwards [hU.mem_nhds hxU] with u hu
  change c.coord.symm (s*e u) = d.coord.symm (t*(t*d.coord (c.coord.symm (s*e u))))
  rw [← mul_assoc,htt,one_mul,d.coord.left_inv hu.2]

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalParameterTransition
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two regular smooth real parameters admit a local smooth change of
parameter, constructed using the proved global extension of an oriented germ. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem local_parameter_transition {h k : ℝ → ℝ} {U V : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (ha : a ∈ U) (hb : b ∈ V)
    (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k V)
    (hhn : deriv h a ≠ 0) (hkn : deriv k b ≠ 0) (heq : h a = k b) :
    ∃ H : ℝ → ℝ, ContDiffOn ℝ ∞ H U ∧ H a = b ∧ deriv H a ≠ 0 ∧
      h =ᶠ[𝓝 a] k ∘ H := by
  have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 < deriv (fun t => s*k t) b := by
    by_cases hp : 0 < deriv k b
    · exact ⟨1,Or.inl rfl,by simpa only [one_mul] using hp⟩
    · refine ⟨-1,Or.inr rfl,?_⟩
      have hn := lt_of_le_of_ne (le_of_not_gt hp) hkn
      simpa only [neg_one_mul,deriv.fun_neg] using neg_pos.mpr hn
  obtain ⟨s,hs,hpos⟩ := hs
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨e,hes,hei,hem,heg⟩ := local_increasing_diffeomorphism hV
    (contDiffOn_const.mul hk) hb hpos
  have heb : e b = s*k b := heg.eq_of_nhds
  let H : ℝ → ℝ := fun t => e.symm (s*h t)
  have hHs : ContDiffOn ℝ ∞ H U := hei.comp_contDiffOn (contDiffOn_const.mul hh)
  have hHa : H a = b := by
    change e.symm (s*h a) = b
    rw [heq,← heb,e.symm_apply_apply]
  have hD := ((hei.differentiable (by simp) (s*h a)).hasDerivAt.comp a
    (((hh.contDiffAt (hU.mem_nhds ha)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt.const_mul s)).deriv
  dsimp only [Function.comp_def] at hD
  have hHn : deriv H a ≠ 0 := by
    rw [hD]
    exact mul_ne_zero (smooth_real_homeomorph_deriv_ne_zero e.symm hei hes (s*h a))
      (mul_ne_zero hs0 hhn)
  have hHt : Tendsto H (𝓝 a) (𝓝 b) := hHa ▸ (hHs.continuousOn.continuousAt (hU.mem_nhds ha))
  have hcomp := heg.comp_tendsto hHt
  refine ⟨H,hHs,hHa,hHn,?_⟩
  filter_upwards [hcomp] with t ht
  change h t = k (H t)
  apply mul_left_cancel₀ hs0
  exact (e.apply_symm_apply (s*h t)).symm.trans ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PathLastIntersection
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Loop removal at the last intersection of two compact embedded arcs. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X] {x y z : X}

omit [T2Space X] in
lemma injective_subpath (γ : Path x y) (hi : Function.Injective γ)
    {s t : I} (hst : s ≠ t) : Function.Injective (γ.subpath s t) := by
  intro u v huv
  have h := congrArg (fun w : I => (w:ℝ)) (hi huv)
  change (1-(u:ℝ))*(s:ℝ)+(u:ℝ)*(t:ℝ) =
    (1-(v:ℝ))*(s:ℝ)+(v:ℝ)*(t:ℝ) at h
  have hst' : (s:ℝ) ≠ (t:ℝ) := fun he => hst (Subtype.ext he)
  apply Subtype.ext
  have hz : ((u:ℝ)-(v:ℝ))*((t:ℝ)-(s:ℝ)) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hz with huv0 | hts0
  · exact sub_eq_zero.mp huv0
  · exact False.elim (hst' (sub_eq_zero.mp hts0).symm)

lemma path_last_intersection (γ : Path x y) (δ : Path y z)
    (hend : z ∉ range γ) (hstart : x ∉ range δ) :
    ∃ s m : I, 0 < s ∧ m < 1 ∧ γ s = δ m ∧
      ∀ u v : I, u ≤ s → m < v → γ u ≠ δ v := by
  let K := δ ⁻¹' range γ
  have hK : IsCompact K :=
    ((isCompact_range γ.continuous).isClosed.preimage δ.continuous).isCompact
  have hne : K.Nonempty := ⟨0,by
    change δ 0 ∈ range γ
    exact ⟨1,by simp⟩⟩
  obtain ⟨m,hm,hmax⟩ := hK.exists_isGreatest hne
  obtain ⟨s,hsm⟩ := hm
  have hs : 0 < s := by
    refine lt_of_le_of_ne (unitInterval.nonneg s) ?_
    intro he
    apply hstart
    refine ⟨m,?_⟩
    simpa only [← he,Path.source] using hsm.symm
  have hm1 : m < 1 := by
    refine lt_of_le_of_ne (unitInterval.le_one m) ?_
    intro he
    apply hend
    exact ⟨s,by simpa only [he,Path.target] using hsm⟩
  refine ⟨s,m,hs,hm1,hsm,?_⟩
  intro u v _ hmv huv
  have hv : v ∈ K := ⟨u,huv⟩
  exact (not_le_of_gt hmv) (hmax hv)

theorem embedded_path_last_join (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hend : z ∉ range γ) (hstart : x ∉ range δ) :
    ∃ s m : I, 0 < s ∧ m < 1 ∧ ∃ hsm : γ s = δ m,
      let P := ((γ.subpath 0 s).cast (show x = γ 0 from γ.source.symm) hsm.symm).trans
        ((δ.subpath m 1).cast rfl (show z = δ 1 from δ.target.symm))
      Function.Injective P ∧ range P ⊆ range γ ∪ range δ := by
  obtain ⟨s,m,hs,hm,hsm,hsep⟩ := path_last_intersection γ δ hend hstart
  refine ⟨s,m,hs,hm,hsm,?_,?_⟩
  · apply path_trans_injective
    · exact injective_subpath γ hγ (ne_of_lt hs)
    · exact injective_subpath δ hδ (ne_of_lt hm)
    · intro u v huv
      have hu : Icc.convexComb 0 s u ≤ s := by
        change (1-(u:ℝ)) * 0 + (u:ℝ)*(s:ℝ) ≤ (s:ℝ)
        nlinarith [unitInterval.le_one u,unitInterval.nonneg s]
      have hv : m ≤ Icc.convexComb m 1 v := by
        change (m:ℝ) ≤ (1-(v:ℝ))*(m:ℝ)+(v:ℝ)*1
        nlinarith [unitInterval.nonneg v,unitInterval.le_one m]
      have hev : Icc.convexComb m 1 v = m := by
        by_contra hn
        exact hsep _ _ hu (lt_of_le_of_ne hv (Ne.symm hn)) huv
      have he0 : v = 0 := by
        have he := congrArg (fun w : I => (w:ℝ)) hev
        change (1-(v:ℝ))*(m:ℝ)+(v:ℝ)*1 = (m:ℝ) at he
        apply Subtype.ext
        change (v:ℝ) = 0
        have hm' : (m:ℝ) < 1 := hm
        nlinarith
      have he1 : u = 1 := by
        have heγ : (γ.subpath 0 s) u = (γ.subpath 0 s) 1 := by
          have huv' : γ (Icc.convexComb 0 s u) = δ (Icc.convexComb m 1 v) := huv
          rw [he0,Icc.convexComb_zero] at huv'
          change γ (Icc.convexComb 0 s u) = γ (Icc.convexComb 0 s 1)
          rw [Icc.convexComb_one]
          exact huv'.trans hsm.symm
        exact injective_subpath γ hγ (ne_of_lt hs) heγ
      exact ⟨he1,he0⟩
  · rw [Path.trans_range]
    apply union_subset
    · intro w hw
      change w ∈ range (γ.subpath 0 s) at hw
      rw [Path.range_subpath] at hw
      exact Or.inl (image_subset_range _ _ hw)
    · intro w hw
      change w ∈ range (δ.subpath m 1) at hw
      rw [Path.range_subpath] at hw
      exact Or.inr (image_subset_range _ _ hw)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_StandardCrosscapDerivative
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The standard umbrella has one singular point and a transverse double ray. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardBaseNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardBaseSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardTripleNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardTripleSpace
lemma standardCrosscap_double_iff {x y : Base} (hne : x ≠ y) :
    standardCrosscap x = standardCrosscap y ↔
      x 0 = 0 ∧ y 0 = 0 ∧ x 1 = -y 1 ∧ x 1 ≠ 0 := by
  constructor
  · intro he
    have h0 : x 0 = y 0 := congrArg Prod.snd he
    have h1 : x 0*x 1 = y 0*y 1 := congrFun (congrArg Prod.fst he) 0
    have h2 : (x 1)^2 = (y 1)^2 := congrFun (congrArg Prod.fst he) 1
    have hxy1 : x 1 ≠ y 1 := by
      intro h
      apply hne
      ext i
      fin_cases i
      · exact h0
      · exact h
    have hx0 : x 0 = 0 := by
      by_contra h
      apply hxy1
      rw [← h0] at h1
      exact mul_left_cancel₀ h h1
    have hneg : x 1 = -y 1 := (sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left hxy1
    refine ⟨hx0,h0 ▸ hx0,hneg,?_⟩
    intro hx1
    apply hxy1
    linarith
  · rintro ⟨hx,hy,hneg,_⟩
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap,hx,hy,hneg]
    · exact hx.trans hy.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapPairCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two branches of a double point near an actual prepared crosscap
are exactly the two opposite nonzero kernel-axis coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem double_pair (c : SurfaceCrosscapCoordinates f p) {x y : M}
    (hx : x ∈ c.source.source) (hy : y ∈ c.source.source)
    (hne : x ≠ y) (heq : f x = f y) :
    c.source x 0 = 0 ∧ c.source y 0 = 0 ∧
      c.source x 1 = -c.source y 1 ∧ c.source x 1 ≠ 0 := by
  have hcne : c.source x ≠ c.source y := fun h => hne (c.source.injOn hx hy h)
  apply (standardCrosscap_double_iff hcne).mp
  apply c.target.injOn (c.model_mem x hx) (c.model_mem y hy)
  rw [← c.model_eq x hx,← c.model_eq y hy]
  exact heq

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisCurve
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The kernel axis of an actual crosscap chart gives a smooth regular
source curve through the singular point, even though its image velocity vanishes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscapAxis_apply (t : ℝ) : crosscapAxis t = ![0,t] := by
  ext i
  fin_cases i <;> rfl

lemma crosscapAxis_injective : Function.Injective crosscapAxis := by
  intro x y he
  simpa only [crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun he 1

lemma crosscapAxis_regular (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) crosscapAxis t) := by
  have hd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,Base) crosscapAxis t crosscapAxis :=
    crosscapAxis.hasFDerivAt.hasMFDerivAt
  exact hd.mfderiv.symm ▸ crosscapAxis_injective

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem axis_curve (c : SurfaceCrosscapCoordinates f p) :
    ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ c.axisCurve U ∧
      (∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel c.axisCurve t)) ∧
      c.axisCurve 0 = p ∧
      (∀ t ∈ U, c.axisCurve t ∈ c.source.source ∧ c.source (c.axisCurve t) = ![0,t]) := by
  let U := crosscapAxis ⁻¹' c.source.target
  have hU : IsOpen U := c.source.open_target.preimage crosscapAxis.continuous
  have h0 : (0:ℝ) ∈ U := by
    change crosscapAxis 0 ∈ c.source.target
    rw [map_zero,← c.source_center]
    exact c.source.map_source c.source_mem
  have hk : ContMDiff 𝓘(ℝ) 𝓘(ℝ,Base) ∞ crosscapAxis := crosscapAxis.contDiff.contMDiff
  have hs : ContMDiffOn 𝓘(ℝ) planeModel ∞ c.axisCurve U :=
    c.source_inverse_smooth.comp hk.contMDiffOn (fun _ ht => ht)
  have hdif : c.source.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨c.source_inverse_smooth.mdifferentiableOn (by simp),c.source_smooth.mdifferentiableOn (by simp)⟩
  refine ⟨U,hU,h0,hs,?_,?_,?_⟩
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (c.source.symm ∘ crosscapAxis) t)
    rw [mfderiv_comp t
      ((c.source_inverse_smooth.contMDiffAt (c.source.open_target.mem_nhds ht)).mdifferentiableAt (by simp))
      (hk.mdifferentiable (by simp) t)]
    exact (hdif.mfderiv_injective ht).comp (crosscapAxis_regular t)
  · change c.source.symm (crosscapAxis 0) = p
    rw [map_zero,← c.source_center,c.source.left_inv c.source_mem]
  · intro t ht
    exact ⟨c.source.map_target ht,(c.source.right_inv ht).trans (crosscapAxis_apply t)⟩

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularCurveGerms
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularity under smooth reparameterization and actual curve germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma regular_curve_germ {γ δ : ℝ → M} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) planeModel ∞ γ t) (he : δ =ᶠ[𝓝 t] γ)
    (hi : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel δ t) := by
  have hD := ((hγ.mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq he).mfderiv
  exact hD.symm ▸ hi

lemma regular_curve_reparameterization {γ : ℝ → M} (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) planeModel ∞ γ (e t))
    (hi : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ (e t))) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel (γ ∘ e) t) := by
  have heD : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  rw [mfderiv_comp t (hγ.mdifferentiableAt (by simp)) (hes.contMDiff.mdifferentiable (by simp) t)]
  exact hi.comp (heD.mfderiv_injective (mem_univ t))

variable [IsManifold planeModel ∞ M]

lemma regular_curve_neighborhood {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U) {t : ℝ}
    (ht : t ∈ U) (hi : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ V ⊆ U ∧
      ∀ s ∈ V, Function.Injective (mfderiv 𝓘(ℝ) planeModel γ s) := by
  obtain ⟨c,V,hV,htV,hVU,hcs,hci,hcoord⟩ := surface_curve_coordinates hU hγ ht hi
  have hdif : c.symm.MDifferentiable 𝓘(ℝ,JetPolynomial.Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  refine ⟨V,hV,htV,hVU,?_⟩
  intro s hs
  have htarget : crosscapAxis s ∈ c.target := by
    rw [crosscapAxis_apply,← (hcoord s hs).2]
    exact c.map_source (hcoord s hs).1
  let δ : ℝ → M := c.symm ∘ crosscapAxis
  have hk : ContMDiff 𝓘(ℝ) 𝓘(ℝ,JetPolynomial.Base) ∞ crosscapAxis := crosscapAxis.contDiff.contMDiff
  have hδ : ContMDiffAt 𝓘(ℝ) planeModel ∞ δ s :=
    (hci.contMDiffAt (c.open_target.mem_nhds htarget)).comp s hk.contMDiffAt
  have hδi : Function.Injective (mfderiv 𝓘(ℝ) planeModel δ s) := by
    rw [mfderiv_comp s
      ((hci.contMDiffAt (c.open_target.mem_nhds htarget)).mdifferentiableAt (by simp))
      (hk.mdifferentiable (by simp) s)]
    exact (hdif.mfderiv_injective htarget).comp (crosscapAxis_regular s)
  apply regular_curve_germ hδ _ hδi
  filter_upwards [hV.mem_nhds hs] with r hr
  change γ r = c.symm (crosscapAxis r)
  rw [crosscapAxis_apply,← (hcoord r hr).2,c.left_inv (hcoord r hr).1]

lemma curve_regular_locus_open {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U) :
    IsOpen {t | t ∈ U ∧ Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  obtain ⟨V,hV,htV,hVU,hreg⟩ := regular_curve_neighborhood hU hγ ht.1 ht.2
  apply mem_of_superset (hV.mem_nhds htV)
  exact fun s hs => ⟨hVU hs,hreg s hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularArcPaths
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Paths generated by finitely many compact regular smooth arcs, with
explicit subdivision, concatenation and endpoint casts. -/
noncomputable section
open Set Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

namespace SmoothCompactArc

lemma path_injective (P : SmoothCompactArc J N) : Function.Injective P.path := by
  intro s t he
  apply (iccHomeoI P.start P.finish P.start_lt_finish).symm.injective
  apply Subtype.ext
  exact P.injective ((iccHomeoI P.start P.finish P.start_lt_finish).symm s).property
    ((iccHomeoI P.start P.finish P.start_lt_finish).symm t).property he

lemma path_range (P : SmoothCompactArc J N) :
    range P.path = P.curve '' Icc P.start P.finish := by
  change range ((fun t : Icc P.start P.finish => P.curve t) ∘
    (iccHomeoI P.start P.finish P.start_lt_finish).symm) = _
  rw [range_comp,(iccHomeoI P.start P.finish P.start_lt_finish).symm.surjective.range_eq,
    image_univ]
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,t.property,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨⟨t,ht⟩,rfl⟩

end SmoothCompactArc

variable [T2Space N] {x y z : N}

theorem finite_regular_path_last_join {γ : Path x y} {δ : Path y z}
    (hγp : FiniteRegularPath J γ) (hδp : FiniteRegularPath J δ)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hend : z ∉ range γ) (hstart : x ∉ range δ) :
    ∃ P : Path x z, FiniteRegularPath J P ∧ Function.Injective P ∧
      range P ⊆ range γ ∪ range δ := by
  obtain ⟨s,m,_,_,hsm,hi,hr⟩ := embedded_path_last_join γ δ hγ hδ hend hstart
  refine ⟨_,?_,hi,hr⟩
  exact ((hγp.subpath 0 s).cast γ.source.symm hsm.symm).trans
    ((hδp.subpath m 1).cast rfl δ.target.symm)

theorem finite_regular_path_join {γ : Path x y} {δ : Path y z}
    (hγp : FiniteRegularPath J γ) (hδp : FiniteRegularPath J δ)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hxz : x ≠ z) (hstart : x ∉ range δ) :
    ∃ P : Path x z, FiniteRegularPath J P ∧ Function.Injective P ∧
      range P ⊆ range γ ∪ range δ := by
  by_cases hz : z ∈ range γ
  · obtain ⟨s,hs⟩ := hz
    have hs0 : (0 : I) ≠ s := by
      intro he
      apply hxz
      simpa only [← he,Path.source] using hs
    let P : Path x z := (γ.subpath 0 s).cast γ.source.symm hs.symm
    refine ⟨P,(hγp.subpath 0 s).cast _ _,injective_subpath γ hγ hs0,?_⟩
    intro w hw
    change w ∈ range (γ.subpath 0 s) at hw
    rw [Path.range_subpath] at hw
    exact Or.inl (image_subset_range _ _ hw)
  · exact finite_regular_path_last_join hγp hδp hγ hδ hz hstart

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularCurvePieces
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact regular surface curve is a finite concatenation of actual
smooth embedded pieces. It need not itself be embedded. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma regular_curve_local_injective {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    {t : ℝ} (ht : t ∈ U)
    (hreg : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ V ⊆ U ∧ V.InjOn γ := by
  obtain ⟨c,V,hV,htV,hVU,_,_,hcoord⟩ := surface_curve_coordinates hU hγ ht hreg
  refine ⟨V,hV,htV,hVU,?_⟩
  intro x hx y hy he
  have hc : (![0,x] : Base) = ![0,y] :=
    (hcoord x hx).2.symm.trans ((congrArg c he).trans (hcoord y hy).2)
  have h1 := congrFun hc 1
  simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using h1

theorem regular_curve_finite_pieces {γ : ℝ → M} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    (hreg : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t))
    (hab : a ≤ b) (hsub : Icc a b ⊆ U) :
    ∃ (τ : ℕ → ℝ) (N : ℕ), τ 0 = a ∧ Monotone τ ∧
      (∀ n, a ≤ τ n ∧ τ n ≤ b) ∧ (∀ n ≥ N, τ n = b) ∧
      ∀ n, τ n < τ (n+1) → ∃ P : SmoothCompactArc planeModel M,
        P.curve = γ ∧ P.start = τ n ∧ P.finish = τ (n+1) := by
  have hl (t : Icc a b) := regular_curve_local_injective hU hγ
    (hsub t.property) (hreg t (hsub t.property))
  choose V hV htV hVU hVi using hl
  let C : Icc a b → Set (Icc a b) := fun t => Subtype.val ⁻¹' V t
  have hC : ∀ t, IsOpen (C t) := fun t => (hV t).preimage continuous_subtype_val
  have hcover : univ ⊆ ⋃ t, C t := by
    intro t _
    exact mem_iUnion.mpr ⟨t,htV t⟩
  obtain ⟨τ,hzero,hmono,⟨N,hend⟩,hpieces⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hC hcover
  refine ⟨fun n => (τ n).val,N,hzero,fun _ _ h => hmono h,
    fun n => (τ n).property,hend,?_⟩
  intro n hn
  obtain ⟨t,ht⟩ := hpieces n
  have hinterval : Icc (τ n).val (τ (n+1)).val ⊆ V t := by
    intro s hs
    have hsab : s ∈ Icc a b :=
      ⟨(τ n).property.1.trans hs.1,hs.2.trans (τ (n+1)).property.2⟩
    exact ht (show (⟨s,hsab⟩ : Icc a b) ∈ Icc (τ n) (τ (n+1)) from hs)
  let P : SmoothCompactArc planeModel M :=
    ⟨γ,τ n,τ (n+1),hn,V t,hV t,hinterval,hγ.mono (hVU t),
      fun s hs => hreg s (hVU t hs),(hVi t).mono hinterval⟩
  exact ⟨P,rfl,rfl,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_RegularCurveLoopRemoval
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite loop removal for a compact regular curve. The selected embedded
path uses only its original image and retains a finite smooth decomposition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem regular_curve_loop_removal {γ : ℝ → M} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    (hreg : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t))
    (hab : a < b) (hsub : Icc a b ⊆ U)
    (hstart : ∀ t ∈ Ioc a b, γ t ≠ γ a) :
    ∃ P : Path (γ a) (γ b), FiniteRegularPath planeModel P ∧
      Function.Injective P ∧ range P ⊆ γ '' Icc a b := by
  obtain ⟨τ,N,hzero,hmono,hbounds,hend,hpieces⟩ :=
    regular_curve_finite_pieces hU hγ hreg hab.le hsub
  have hstep (n : ℕ) : τ n = a ∨
      ∃ P : Path (γ a) (γ (τ n)), FiniteRegularPath planeModel P ∧
        Function.Injective P ∧ range P ⊆ γ '' Icc a (τ n) := by
    induction n with
    | zero => exact Or.inl hzero
    | succ n ih =>
      by_cases heq : τ (n+1) = a
      · exact Or.inl heq
      right
      by_cases hn : τ n = τ (n+1)
      · rcases ih with ha | ⟨P,hPp,hPi,hPr⟩
        · exact False.elim (heq (hn.symm.trans ha))
        · let Q : Path (γ a) (γ (τ (n+1))) := P.cast rfl (congrArg γ hn.symm)
          refine ⟨Q,hPp.cast _ _,hPi,?_⟩
          change range P ⊆ _
          rw [← hn]
          exact hPr
      have hlt : τ n < τ (n+1) := lt_of_le_of_ne (hmono (Nat.le_succ n)) hn
      obtain ⟨R,hRc,hRs,hRf⟩ := hpieces n hlt
      have hleft : γ (τ n) = R.curve R.start := by rw [hRc,hRs]
      have hright : γ (τ (n+1)) = R.curve R.finish := by rw [hRc,hRf]
      let δ : Path (γ (τ n)) (γ (τ (n+1))) := R.path.cast hleft hright
      have hδp : FiniteRegularPath planeModel δ := (FiniteRegularPath.arc R).cast hleft hright
      have hδi : Function.Injective δ := R.path_injective
      have hδr : range δ = γ '' Icc (τ n) (τ (n+1)) := by
        change range R.path = _
        rw [R.path_range,hRc,hRs,hRf]
      by_cases ha : τ n = a
      · let Q : Path (γ a) (γ (τ (n+1))) := δ.cast (congrArg γ ha.symm) rfl
        refine ⟨Q,hδp.cast _ _,hδi,?_⟩
        change range δ ⊆ _
        rw [hδr,ha]
      · obtain ⟨P,hPp,hPi,hPr⟩ := ih.resolve_left ha
        have hna : a < τ n := lt_of_le_of_ne (hbounds n).1 (Ne.symm ha)
        have hn1a : a < τ (n+1) := hna.trans hlt
        have havoid : γ a ∉ range δ := by
          rw [hδr]
          rintro ⟨t,ht,het⟩
          exact hstart t ⟨hna.trans_le ht.1,ht.2.trans (hbounds (n+1)).2⟩ het
        obtain ⟨Q,hQp,hQi,hQr⟩ := finite_regular_path_join hPp hδp hPi hδi
          (hstart _ ⟨hn1a,(hbounds (n+1)).2⟩).symm havoid
        refine ⟨Q,hQp,hQi,hQr.trans ?_⟩
        apply union_subset
        · exact hPr.trans (image_mono (Icc_subset_Icc_right (hmono (Nat.le_succ n))))
        · rw [hδr]
          exact image_mono (Icc_subset_Icc_left (hbounds n).1)
  rcases hstep N with hNa | ⟨P,hPp,hPi,hPr⟩
  · exact False.elim (hab.ne (hNa.symm.trans (hend N le_rfl)))
  · let Q : Path (γ a) (γ b) := P.cast rfl (congrArg γ (hend N le_rfl).symm)
    refine ⟨Q,hPp.cast _ _,hPi,?_⟩
    change range P ⊆ _
    rw [← hend N le_rfl]
    exact hPr

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapArcEndpoint
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous ordered double arc ending at a prepared crosscap lies
in its source chart on a full initial parameter interval. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

 theorem crosscap_arc_endpoint (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hzero : Γ 0 = (p,p))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1/3 ∧ ∀ t : I, (t:ℝ) ≤ ε →
      (Γ t).1 ∈ c.source.source ∧ (Γ t).2 ∈ c.source.source ∧
      c.source (Γ t).1 0 = 0 ∧ c.source (Γ t).2 0 = 0 ∧
      c.source (Γ t).1 1 = -c.source (Γ t).2 1 ∧
      (0 < (t:ℝ) → c.source (Γ t).1 1 ≠ 0) := by
  let Θ : ℝ → M × M := Γ ∘ projIcc 0 1 zero_le_one
  have hΘ : Continuous Θ := hΓ.comp continuous_projIcc
  have hΘ0 : Θ 0 = (p,p) := by
    change Γ (projIcc 0 1 zero_le_one 0) = _
    have hp : projIcc 0 1 zero_le_one 0 = (0:I) := Subtype.ext (by simp [projIcc_left])
    rw [hp]
    exact hzero
  have hU : IsOpen (Θ ⁻¹' (c.source.source ×ˢ c.source.source)) :=
    (c.source.open_source.prod c.source.open_source).preimage hΘ
  have h0 : (0:ℝ) ∈ Θ ⁻¹' (c.source.source ×ˢ c.source.source) := by
    change (Θ 0).1 ∈ c.source.source ∧ (Θ 0).2 ∈ c.source.source
    rw [hΘ0]
    exact ⟨c.source_mem,c.source_mem⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let ε : ℝ := min (r/2) (1/4)
  have hε : 0 < ε := lt_min (half_pos hr) (by norm_num)
  have hεsmall : ε < 1/3 := (min_le_right _ _).trans_lt (by norm_num)
  have hε1 : ε < 1 := hεsmall.trans (by norm_num)
  have hεr : ε < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  refine ⟨ε,hε,hεsmall,?_⟩
  intro t ht
  have hmem : Θ (t:ℝ) ∈ c.source.source ×ˢ c.source.source := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg t.property.1]
    exact ht.trans_lt hεr
  have hΘt : Θ (t:ℝ) = Γ t := by
    change Γ (projIcc 0 1 zero_le_one (t:ℝ)) = Γ t
    rw [projIcc_val]
  rw [hΘt] at hmem
  refine ⟨hmem.1,hmem.2,?_⟩
  by_cases ht0 : (t:ℝ) = 0
  · have htz : t = 0 := Subtype.ext ht0
    rw [htz,hzero]
    simp [c.source_center]
  · have hp := c.double_pair hmem.1 hmem.2
      (hne t (lt_of_le_of_ne t.property.1 (Ne.symm ht0)) (ht.trans_lt hε1)) (heq t)
    exact ⟨hp.1,hp.2.1,hp.2.2.1,fun _ => hp.2.2.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the two source branches from their scalar
kernel-axis parameter in the actual crosscap chart. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

lemma axisCurve_coordinate (c : SurfaceCrosscapCoordinates f p) {x : M}
    (hx : x ∈ c.source.source) (hzero : c.source x 0 = 0) :
    c.axisCurve (c.source x 1) = x := by
  have he : crosscapAxis (c.source x 1) = c.source x := by
    rw [crosscapAxis_apply]
    ext i
    fin_cases i
    · exact hzero.symm
    · rfl
  change c.source.symm (crosscapAxis (c.source x 1)) = x
  rw [he,c.source.left_inv hx]

lemma axis_pair_coordinates (c : SurfaceCrosscapCoordinates f p) {x y : M}
    (hx : x ∈ c.source.source) (hy : y ∈ c.source.source)
    (h0x : c.source x 0 = 0) (h0y : c.source y 0 = 0)
    (hopp : c.source x 1 = -c.source y 1) :
    (x,y) = (c.axisCurve (c.source x 1),c.axisCurve (-c.source x 1)) := by
  apply Prod.ext
  · exact (c.axisCurve_coordinate hx h0x).symm
  · have he : -c.source x 1 = c.source y 1 := by linarith
    rw [he,c.axisCurve_coordinate hy h0y]

lemma axis_parameter_injective (c : SurfaceCrosscapCoordinates f p)
    {Γ : ℝ → M × M} {K : Set ℝ} (hΓ : K.InjOn Γ)
    (hsource : ∀ t ∈ K, (Γ t).1 ∈ c.source.source ∧ (Γ t).2 ∈ c.source.source)
    (haxis : ∀ t ∈ K, c.source (Γ t).1 0 = 0 ∧ c.source (Γ t).2 0 = 0 ∧
      c.source (Γ t).1 1 = -c.source (Γ t).2 1) :
    K.InjOn (fun t => c.source (Γ t).1 1) := by
  intro t ht u hu he
  apply hΓ ht hu
  have ht' := c.axis_pair_coordinates (hsource t ht).1 (hsource t ht).2
    (haxis t ht).1 (haxis t ht).2.1 (haxis t ht).2.2
  have hu' := c.axis_pair_coordinates (hsource u hu).1 (hsource u hu).2
    (haxis u hu).1 (haxis u hu).2.1 (haxis u hu).2.2
  change ((Γ t).1,(Γ t).2) = ((Γ u).1,(Γ u).2)
  dsimp only at he
  rw [ht',hu',he]

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisDoublePair
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from zero, the opposite kernel-axis source points form genuine
double pairs of the original surface map throughout the chart domain. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem axis_double_pair (c : SurfaceCrosscapCoordinates f p) {u : ℝ} (hu : u ≠ 0)
    (hplus : crosscapAxis u ∈ c.source.target) (hminus : crosscapAxis (-u) ∈ c.source.target) :
    (c.axisCurve u,c.axisCurve (-u)) ∈ surfaceDoublePairs f := by
  have hp : c.axisCurve u ∈ c.source.source := c.source.map_target hplus
  have hm : c.axisCurve (-u) ∈ c.source.source := c.source.map_target hminus
  have hpc : c.source (c.axisCurve u) = crosscapAxis u := c.source.right_inv hplus
  have hmc : c.source (c.axisCurve (-u)) = crosscapAxis (-u) := c.source.right_inv hminus
  constructor
  · intro he
    have hv := congrArg (fun x => c.source x 1) he
    rw [hpc,hmc,crosscapAxis_apply,crosscapAxis_apply] at hv
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero] at hv
    exact hu (by linarith)
  · rw [c.model_eq _ hp,c.model_eq _ hm,hpc,hmc]
    congr 1
    rw [crosscapAxis_apply,crosscapAxis_apply]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapEndpointParameter
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A whole initial segment of the chosen embedded double arc is traced
by the explicit pair of opposite kernel-axis curves, in one orientation. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_endpoint_parameter (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ (ε s d : ℝ), 0 < ε ∧ ε < 1/3 ∧ (s = 1 ∨ s = -1) ∧ 0 < d ∧
      (fun t => (c.axisCurve (s*t),c.axisCurve (-(s*t)))) '' Icc 0 d =
        Γ '' {t : I | (t:ℝ) ≤ ε} ∧
      (∀ t ∈ Icc 0 d, crosscapAxis (s*t) ∈ c.source.target ∧
        crosscapAxis (-(s*t)) ∈ c.source.target) ∧
      (∀ u : I, (u:ℝ) = ε → (c.axisCurve (s*d),c.axisCurve (-(s*d))) = Γ u) := by
  obtain ⟨ε,hε,hεsmall,hcoords⟩ := crosscap_arc_endpoint c hΓ hzero heq hne
  have hε1 : ε < 1 := hεsmall.trans (by norm_num)
  let θ : ℝ → I := projIcc 0 1 zero_le_one
  let A : ℝ → M × M := Γ ∘ θ
  let v : ℝ → ℝ := fun t => c.source (A t).1 1
  have hθ : Continuous θ := continuous_projIcc
  have hA : Continuous A := hΓ.comp hθ
  have hθval : ∀ t ∈ Icc 0 ε, (θ t : ℝ) = t := by
    intro t ht
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨ht.1,ht.2.trans hε1.le⟩)
  have hdata : ∀ t ∈ Icc 0 ε,
      (A t).1 ∈ c.source.source ∧ (A t).2 ∈ c.source.source ∧
      c.source (A t).1 0 = 0 ∧ c.source (A t).2 0 = 0 ∧
      c.source (A t).1 1 = -c.source (A t).2 1 := by
    intro t ht
    have h := hcoords (θ t) (by rw [hθval t ht]; exact ht.2)
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
  have hAi : InjOn A (Icc 0 ε) := by
    intro t ht u hu he
    have hh := congrArg Subtype.val (hinj he)
    change (θ t:ℝ) = (θ u:ℝ) at hh
    rwa [hθval t ht,hθval u hu] at hh
  have hvi : InjOn v (Icc 0 ε) := c.axis_parameter_injective hAi
    (fun t ht => ⟨(hdata t ht).1,(hdata t ht).2.1⟩)
    (fun t ht => ⟨(hdata t ht).2.2.1,(hdata t ht).2.2.2.1,(hdata t ht).2.2.2.2⟩)
  have hvc : ContinuousOn v (Icc 0 ε) := (continuous_apply 1).comp_continuousOn
    (c.source.continuousOn.comp hA.fst.continuousOn (fun t ht => (hdata t ht).1))
  have hv0 : v 0 = 0 := by
    have hz : θ 0 = 0 := Subtype.ext (hθval 0 (left_mem_Icc.mpr hε.le))
    change c.source (Γ (θ 0)).1 1 = 0
    rw [hz,hzero]
    exact congrFun c.source_center 1
  have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ StrictMonoOn (fun t => s*v t) (Icc 0 ε) := by
    rcases hvc.strictMonoOn_of_injOn_Icc' hε.le hvi with hm | hm
    · exact ⟨1,Or.inl rfl,by simpa only [one_mul] using hm⟩
    · refine ⟨-1,Or.inr rfl,?_⟩
      intro x hx y hy hxy
      simpa only [neg_one_mul,neg_lt_neg_iff] using hm hx hy hxy
  obtain ⟨s,hs,hm⟩ := hs
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  let d := s*v ε
  have hd : 0 < d := by
    have h := hm (left_mem_Icc.mpr hε.le) (right_mem_Icc.mpr hε.le) hε
    simpa only [hv0,mul_zero] using h
  have himage : (fun t => s*v t) '' Icc 0 ε = Icc 0 d := by
    have hc : ContinuousOn (fun t => s*v t) (Icc 0 ε) := continuousOn_const.mul hvc
    simpa only [hv0,mul_zero] using hc.image_Icc_of_monotoneOn hε.le hm.monotoneOn
  have hpair : ∀ t ∈ Icc 0 ε, A t = (c.axisCurve (v t),c.axisCurve (-(v t))) := by
    intro t ht
    exact c.axis_pair_coordinates (hdata t ht).1 (hdata t ht).2.1
      (hdata t ht).2.2.1 (hdata t ht).2.2.2.1 (hdata t ht).2.2.2.2
  have hAiimage : A '' Icc 0 ε = Γ '' {t : I | (t:ℝ) ≤ ε} := by
    apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨θ t,?_,rfl⟩
      change (θ t:ℝ) ≤ ε
      rw [hθval t ht]
      exact ht.2
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨(t:ℝ),⟨t.property.1,ht⟩,?_⟩
      change Γ (θ (t:ℝ)) = Γ t
      congr 1
      exact Subtype.ext (hθval t ⟨t.property.1,ht⟩)
  refine ⟨ε,s,d,hε,hεsmall,hs,hd,?_,?_,?_⟩
  · rw [← hAiimage]
    apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      obtain ⟨u,hu,rfl⟩ := himage.symm.subset ht
      refine ⟨u,hu,?_⟩
      dsimp only
      rw [← mul_assoc,hss,one_mul]
      exact hpair u hu
    · rintro y ⟨u,hu,rfl⟩
      refine ⟨s*v u,himage.subset ⟨u,hu,rfl⟩,?_⟩
      dsimp only
      rw [← mul_assoc,hss,one_mul]
      exact (hpair u hu).symm
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := himage.symm.subset ht
    dsimp only
    rw [← mul_assoc,hss,one_mul]
    have hx : crosscapAxis (v u) = c.source (A u).1 := by
      rw [crosscapAxis_apply]
      ext i
      fin_cases i
      · exact (hdata u hu).2.2.1.symm
      · rfl
    have hy : crosscapAxis (-(v u)) = c.source (A u).2 := by
      rw [crosscapAxis_apply]
      ext i
      fin_cases i
      · exact (hdata u hu).2.2.2.1.symm
      · have h := (hdata u hu).2.2.2.2
        change -(c.source (A u).1 1) = c.source (A u).2 1
        linarith
    rw [hx,hy]
    exact ⟨c.source.map_source (hdata u hu).1,c.source.map_source (hdata u hu).2.1⟩

  · intro u hu
    change (c.axisCurve (s*(s*v ε)),c.axisCurve (-(s*(s*v ε)))) = Γ u
    rw [← mul_assoc,hss,one_mul,← hpair ε (right_mem_Icc.mpr hε.le)]
    change Γ (θ ε) = Γ u
    apply congrArg Γ
    apply Subtype.ext
    exact (hθval ε (right_mem_Icc.mpr hε.le)).trans hu.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SignedCrosscapAxis
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed kernel-axis curves are smooth, regular and injective throughout
the actual domain of the crosscap source chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem signed_axis_curve (c : SurfaceCrosscapCoordinates f p) {s : ℝ} (hs : s ≠ 0) :
    ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => c.axisCurve (s*t))
      {t | crosscapAxis (s*t) ∈ c.source.target} ∧
    (∀ t, crosscapAxis (s*t) ∈ c.source.target →
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => c.axisCurve (s*t)) t)) ∧
    ({t | crosscapAxis (s*t) ∈ c.source.target}).InjOn (fun t => c.axisCurve (s*t)) := by
  let L : ℝ →L[ℝ] Base := crosscapAxis.comp (s • ContinuousLinearMap.id ℝ ℝ)
  have hL : ∀ t, L t = crosscapAxis (s*t) := fun _ => rfl
  have hLi : Function.Injective L := by
    intro x y he
    exact mul_left_cancel₀ hs (crosscapAxis_injective he)
  have hLs : ContMDiff 𝓘(ℝ) 𝓘(ℝ,Base) ∞ L := L.contDiff.contMDiff
  have hLd (t : ℝ) : Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) L t) := by
    have hd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,Base) L t L := L.hasFDerivAt.hasMFDerivAt
    exact hd.mfderiv.symm ▸ hLi
  have hdif : c.source.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨c.source_inverse_smooth.mdifferentiableOn (by simp),c.source_smooth.mdifferentiableOn (by simp)⟩
  refine ⟨?_,?_,?_⟩
  · change ContMDiffOn 𝓘(ℝ) planeModel ∞ (c.source.symm ∘ L) (L ⁻¹' c.source.target)
    exact c.source_inverse_smooth.comp hLs.contMDiffOn (fun _ ht => ht)
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (c.source.symm ∘ L) t)
    rw [mfderiv_comp t
      ((c.source_inverse_smooth.contMDiffAt (c.source.open_target.mem_nhds ht)).mdifferentiableAt (by simp))
      (hLs.mdifferentiable (by simp) t)]
    exact (hdif.mfderiv_injective ht).comp (hLd t)
  · intro x hx y hy he
    apply hLi
    exact c.source.symm.injOn hx hy he

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapEndpointSmoothArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual initial crosscap branch has a smooth regular embedded
parameterization including its singular endpoint, with both source projections regular. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_endpoint_smooth_arc (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ (ε : ℝ) (P : SmoothCompactArc (planeModel.prod planeModel) (M × M)),
      0 < ε ∧ ε < 1/3 ∧ P.start = 0 ∧
      P.curve '' Icc P.start P.finish = Γ '' {t : I | (t:ℝ) ≤ ε} ∧
      P.curve P.start = (p,p) ∧
      (∀ u : I, (u:ℝ) = ε → P.curve P.finish = Γ u) ∧
      (∀ t ∈ P.domain, t ≠ P.start → P.curve t ∈ surfaceDoublePairs f) ∧
      ∀ t ∈ P.domain,
        Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (P.curve u).1) t) ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (P.curve u).2) t) := by
  obtain ⟨ε,s,d,hε,hε1,hs,hd,himage,htarget,hend⟩ :=
    crosscap_endpoint_parameter c hΓ hinj hzero heq hne
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  let A : ℝ → M := fun t => c.axisCurve (s*t)
  let B : ℝ → M := fun t => c.axisCurve (-(s*t))
  let V : Set ℝ := {t | crosscapAxis (s*t) ∈ c.source.target}
  let W : Set ℝ := {t | crosscapAxis (-(s*t)) ∈ c.source.target}
  let U := V ∩ W
  have hV : IsOpen V := c.source.open_target.preimage
    (crosscapAxis.continuous.comp (continuous_const.mul continuous_id))
  have hW : IsOpen W := c.source.open_target.preimage
    (crosscapAxis.continuous.comp ((continuous_const.mul continuous_id).neg))
  obtain ⟨hAs,hAi,hAj⟩ := c.signed_axis_curve hs0
  have hBs : ContMDiffOn 𝓘(ℝ) planeModel ∞ B W := by
    simpa only [neg_mul] using (c.signed_axis_curve (neg_ne_zero.mpr hs0)).1
  have hBi : ∀ t ∈ W, Function.Injective (mfderiv 𝓘(ℝ) planeModel B t) := by
    intro t ht
    change crosscapAxis (-(s*t)) ∈ c.source.target at ht
    have hb := (c.signed_axis_curve (neg_ne_zero.mpr hs0)).2.1 t (by simpa only [neg_mul] using ht)
    have he : (fun u => c.axisCurve (-s*u)) = B := by
      funext u
      dsimp only [B]
      rw [neg_mul]
    rw [he] at hb
    exact hb
  have hpair : ∀ t ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ) (planeModel.prod planeModel) (fun u => (A u,B u)) t) := by
    intro t ht
    have hAt := hAs.contMDiffAt (hV.mem_nhds ht.1)
    have hBt := hBs.contMDiffAt (hW.mem_nhds ht.2)
    have he := mfderiv_prodMk (hAt.mdifferentiableAt (by simp)) (hBt.mdifferentiableAt (by simp))
    have hj : Function.Injective
        ((mfderiv 𝓘(ℝ) planeModel A t).prod (mfderiv 𝓘(ℝ) planeModel B t)) := by
      intro x y hxy
      exact hAi t ht.1 (congrArg Prod.fst hxy)
    exact he.symm ▸ hj
  have hPi : InjOn (fun t => (A t,B t)) (Icc 0 d) := by
    intro x hx y hy hxy
    exact hAj (htarget x hx).1 (htarget y hy).1 (congrArg Prod.fst hxy)
  let P : SmoothCompactArc (planeModel.prod planeModel) (M × M) :=
    ⟨(fun t => (A t,B t)),0,d,hd,U,hV.inter hW,htarget,
      (hAs.mono inter_subset_left).prodMk (hBs.mono inter_subset_right),hpair,hPi⟩
  obtain ⟨_,_,_,_,_,hK0,_⟩ := c.axis_curve
  refine ⟨ε,P,hε,hε1,rfl,himage,?_,hend,?_,?_⟩
  · change (c.axisCurve (s*0),c.axisCurve (-(s*0))) = (p,p)
    simp only [mul_zero,neg_zero,hK0]
  · intro t ht htn
    exact c.axis_double_pair (mul_ne_zero hs0 htn) ht.1 ht.2
  · intro t ht
    exact ⟨hAi t ht.1,hBi t ht.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcReverse
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing a compact smooth regular arc preserves its image and
exchanges the endpoint germs, with no loss of regularity. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
namespace SmoothCompactArc

theorem reverse_arc (P : SmoothCompactArc I N) :
    ∃ R : SmoothCompactArc I N,
      R.start = -P.finish ∧ R.finish = -P.start ∧
      R.domain = (fun t : ℝ => -t) ⁻¹' P.domain ∧
      R.curve = (fun t => P.curve (-t)) ∧
      R.curve '' Icc R.start R.finish = P.curve '' Icc P.start P.finish := by
  let e : ℝ ≃ₜ ℝ := Homeomorph.neg ℝ
  have hes : ContDiff ℝ ∞ e := contDiff_neg
  have hei : ContDiff ℝ ∞ e.symm := contDiff_neg
  have heD : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.mdifferentiableOn⟩
  let U := e ⁻¹' P.domain
  have hsub : Icc (-P.finish) (-P.start) ⊆ U := by
    intro t ht
    apply P.interval_subset
    change P.start ≤ -t ∧ -t ≤ P.finish
    constructor <;> linarith [ht.1,ht.2]
  have hs : ContMDiffOn 𝓘(ℝ) I ∞ (P.curve ∘ e) U :=
    P.smooth.comp hes.contMDiff.contMDiffOn (fun _ ht => ht)
  have hr : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I (P.curve ∘ e) t) := by
    intro t ht
    rw [mfderiv_comp t
      ((P.smooth.contMDiffAt (P.domain_open.mem_nhds ht)).mdifferentiableAt (by simp))
      (hes.contMDiff.mdifferentiable (by simp) t)]
    exact (P.regular _ ht).comp (heD.mfderiv_injective (mem_univ t))
  have hi : InjOn (P.curve ∘ e) (Icc (-P.finish) (-P.start)) := by
    intro t ht u hu heq
    have ht' : -t ∈ Icc P.start P.finish := by constructor <;> linarith [ht.1,ht.2]
    have hu' : -u ∈ Icc P.start P.finish := by constructor <;> linarith [hu.1,hu.2]
    exact neg_injective (P.injective ht' hu' heq)
  let R : SmoothCompactArc I N := ⟨P.curve ∘ e,-P.finish,-P.start,
    neg_lt_neg P.start_lt_finish,U,P.domain_open.preimage e.continuous,hsub,hs,hr,hi⟩
  refine ⟨R,rfl,rfl,rfl,rfl,?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    refine ⟨-t,?_,rfl⟩
    constructor <;> linarith [ht.1,ht.2]
  · rintro y ⟨t,ht,rfl⟩
    refine ⟨-t,?_,?_⟩
    · constructor <;> linarith [ht.1,ht.2]
    · change P.curve (- -t) = P.curve t
      rw [neg_neg]

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapEndArcs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose disjoint initial and terminal smooth pieces of the actual
crosscap-connecting arc, retaining genuine double-locus germs at their inner ends. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_end_arcs_regular (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ (a b : ℝ) (P Q : SmoothCompactArc (planeModel.prod planeModel) (M × M)),
      0 < a ∧ a < b ∧ b < 1 ∧
      P.curve '' Icc P.start P.finish = Γ '' {t : I | (t:ℝ) ≤ a} ∧
      Q.curve '' Icc Q.start Q.finish = Γ '' {t : I | b ≤ (t:ℝ)} ∧
      P.curve P.start = (p,p) ∧ Q.curve Q.finish = (q,q) ∧
      (∀ u : I, (u:ℝ) = a → P.curve P.finish = Γ u) ∧
      (∀ u : I, (u:ℝ) = b → Q.curve Q.start = Γ u) ∧
      (∀ᶠ t in 𝓝 P.finish, P.curve t ∈ surfaceDoublePairs f) ∧
      (∀ᶠ t in 𝓝 Q.start, Q.curve t ∈ surfaceDoublePairs f) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (P.curve t).1) P.start) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (Q.curve t).1) Q.finish) := by
  obtain ⟨a,P,ha,ha3,hPstart,hPi,hP0,hPa,hPg,hPreg⟩ :=
    crosscap_endpoint_smooth_arc cp hΓ hinj hzero heq hne
  have hrev : Continuous (Γ ∘ unitInterval.symm) := hΓ.comp continuous_symm
  have hrevInj : Function.Injective (Γ ∘ unitInterval.symm) := hinj.comp symm_bijective.injective
  have hrev0 : (Γ ∘ unitInterval.symm) 0 = (q,q) := by simpa using hone
  have hrevEq : ∀ t, f ((Γ ∘ unitInterval.symm) t).1 = f ((Γ ∘ unitInterval.symm) t).2 :=
    fun t => heq (unitInterval.symm t)
  have hrevNe : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 →
      ((Γ ∘ unitInterval.symm) t).1 ≠ ((Γ ∘ unitInterval.symm) t).2 := by
    intro t ht0 ht1
    apply hne
    · change 0 < 1-(t:ℝ)
      linarith
    · change 1-(t:ℝ) < 1
      linarith
  obtain ⟨d,R,hd,hd3,hRstart,hRi,hR0,hRd,hRg,hRreg⟩ :=
    crosscap_endpoint_smooth_arc cq hrev hrevInj hrev0 hrevEq hrevNe
  obtain ⟨Q,hQs,hQf,hQdom,hQc,hQi⟩ := R.reverse_arc
  have hQimage : Q.curve '' Icc Q.start Q.finish = Γ '' {t : I | 1-d ≤ (t:ℝ)} := by
    rw [hQi,hRi]
    apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨unitInterval.symm t,?_,rfl⟩
      change (t:ℝ) ≤ d at ht
      change 1-d ≤ 1-(t:ℝ)
      linarith
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨unitInterval.symm t,?_,?_⟩
      · change 1-d ≤ (t:ℝ) at ht
        change 1-(t:ℝ) ≤ d
        linarith
      · change Γ (unitInterval.symm (unitInterval.symm t)) = Γ t
        rw [symm_symm]
  have hQend : Q.curve Q.finish = (q,q) := by
    rw [hQc,hQf]
    dsimp only
    rw [neg_neg]
    exact hR0
  have hQbegin : ∀ u : I, (u:ℝ) = 1-d → Q.curve Q.start = Γ u := by
    intro u hu
    rw [hQc,hQs]
    dsimp only
    rw [neg_neg]
    have hd' : (unitInterval.symm u : ℝ) = d := by change 1-(u:ℝ) = d; linarith
    have hh := hRd (unitInterval.symm u) hd'
    simpa only [Function.comp_apply,symm_symm] using hh
  have hPgood : ∀ᶠ t in 𝓝 P.finish, P.curve t ∈ surfaceDoublePairs f := by
    filter_upwards [P.domain_open.mem_nhds (P.interval_subset (right_mem_Icc.mpr P.start_lt_finish.le)),
      eventually_ne_nhds (ne_of_gt P.start_lt_finish)] with t ht htn
    exact hPg t ht htn
  have hRgood : ∀ᶠ t in 𝓝 R.finish, R.curve t ∈ surfaceDoublePairs f := by
    filter_upwards [R.domain_open.mem_nhds (R.interval_subset (right_mem_Icc.mpr R.start_lt_finish.le)),
      eventually_ne_nhds (ne_of_gt R.start_lt_finish)] with t ht htn
    exact hRg t ht htn
  have hQgood : ∀ᶠ t in 𝓝 Q.start, Q.curve t ∈ surfaceDoublePairs f := by
    rw [hQc,hQs]
    have ht : Tendsto (fun t : ℝ => -t) (𝓝 (-R.finish)) (𝓝 R.finish) := by
      simpa only [ContinuousAt,neg_neg] using (continuous_neg.continuousAt (x := -R.finish))
    exact ht.eventually hRgood
  refine ⟨a,1-d,P,Q,ha,by linarith,by linarith,hPi,hQimage,hP0,hQend,hPa,hQbegin,hPgood,hQgood,?_,?_⟩
  · exact (hPreg _ (P.interval_subset (left_mem_Icc.mpr P.start_lt_finish.le))).1
  · have hfun : (fun t => (Q.curve t).1) = (fun t => (R.curve t).1) ∘ Homeomorph.neg ℝ := by
      funext t
      rw [hQc]
      rfl
    rw [hfun,hQf]
    have ht := R.interval_subset (left_mem_Icc.mpr R.start_lt_finish.le)
    apply regular_curve_reparameterization (Homeomorph.neg ℝ) contDiff_neg contDiff_neg
    · change ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (R.curve t).1) (- -R.start)
      rw [neg_neg]
      exact contMDiffAt_fst.comp R.start (R.smooth.contMDiffAt (R.domain_open.mem_nhds ht))
    · change Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (R.curve t).1) (- -R.start))
      rw [neg_neg]
      exact (hRreg R.start ht).1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_PairArcJoin
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two compact regular pair arcs meeting in the actual transverse double
locus can be joined smoothly. Their disjoint interiors force the orientation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3}

lemma compact_pair_arc_regular
    (P : SmoothCompactArc (planeModel.prod planeModel) (M × M)) {x : ℝ} (hx : x ∈ P.domain) :
    Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (P.curve t).1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (P.curve t).2) x)) := by
  have hP := P.smooth.contMDiffAt (P.domain_open.mem_nhds hx)
  have he := mfderiv_prodMk ((contMDiffAt_fst.comp x hP).mdifferentiableAt (by simp))
    ((contMDiffAt_snd.comp x hP).mdifferentiableAt (by simp))
  exact he ▸ P.regular x hx

variable [IsManifold planeModel ∞ M] [T2Space M]

theorem join_pair_arcs
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (P Q : SmoothCompactArc (planeModel.prod planeModel) (M × M))
    (p : surfaceDoublePairs f) (hp : p.val = P.curve P.finish) (hq : p.val = Q.curve Q.start)
    (hPgood : ∀ᶠ t in 𝓝 P.finish, P.curve t ∈ surfaceDoublePairs f)
    (hQgood : ∀ᶠ t in 𝓝 Q.start, Q.curve t ∈ surfaceDoublePairs f)
    (hcross : ∀ u ∈ Icc P.start P.finish, ∀ v ∈ Ioc Q.start Q.finish, P.curve u ≠ Q.curve v) :
    ∃ (R : SmoothCompactArc (planeModel.prod planeModel) (M × M)) (e : ℝ ≃ₜ ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
      R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve '' Icc R.start R.finish = P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish ∧
      R.curve R.start = P.curve P.start ∧ R.curve R.finish = Q.curve Q.finish ∧
      R.curve =ᶠ[𝓝 R.start] P.curve ∧ R.curve =ᶠ[𝓝 R.finish] Q.curve ∘ e := by
  obtain ⟨c,hpc⟩ := exists_smooth_double_chart hf p (hreg _ _ p.property.1 p.property.2)
  have hxP : P.finish ∈ P.domain := P.interval_subset (right_mem_Icc.mpr P.start_lt_finish.le)
  have hxQ : Q.start ∈ Q.domain := Q.interval_subset (left_mem_Icc.mpr Q.start_lt_finish.le)
  obtain ⟨U,h,hU,haU,_,hhs,hhn,hval,hPinv⟩ := c.smooth_pair_curve_parameter P.domain_open P.smooth
    hxP p hp hpc (compact_pair_arc_regular P hxP) hPgood
  obtain ⟨V,k,hV,hbV,_,hks,hkn,kval,hQinv⟩ := c.smooth_pair_curve_parameter Q.domain_open Q.smooth
    hxQ p hq hpc (compact_pair_arc_regular Q hxQ) hQgood
  obtain ⟨H,hHs,hHa,hHn,htrans⟩ := local_parameter_transition hU hV haU hbV hhs hks hhn hkn (hval.trans kval.symm)
  have hHt : Tendsto H (𝓝 P.finish) (𝓝 Q.start) := by
    rw [← hHa]
    exact (hHs.contDiffAt (hU.mem_nhds haU)).continuousAt
  have hQcomp := hQinv.comp_tendsto hHt
  have hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ H := by
    filter_upwards [hPinv,hQcomp,htrans] with t ht ht' he
    change P.curve t = Q.curve (H t)
    rw [ht,he]
    exact ht'.symm
  have hpos := arc_join_deriv_pos P.start_lt_finish Q.start_lt_finish
    ((hHs.contDiffAt (hU.mem_nhds haU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hHn hHa hmatch hcross
  obtain ⟨R,e,hes,hei,hem,hea,hRs,hRf,hRc,hRi⟩ :=
    P.join Q hU hHs haU hpos hHa hmatch hcross
  have hcut : P.finish < R.finish := by
    rw [hRf]
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact Q.start_lt_finish
  have hleft : R.curve =ᶠ[𝓝 R.start] P.curve := by
    rw [hRc]
    exact joinedCurve_germ_left P.finish P.curve (Q.curve ∘ e) (hRs ▸ P.start_lt_finish)
  have hright : R.curve =ᶠ[𝓝 R.finish] Q.curve ∘ e := by
    rw [hRc]
    exact joinedCurve_germ_right P.finish P.curve (Q.curve ∘ e) hcut
  refine ⟨R,e,hes,hei,hem,hRs,hRf,hRi,?_,?_,hleft,hright⟩
  · exact hleft.eq_of_nhds.trans (congrArg P.curve hRs)
  · have heR : e R.finish = Q.finish := by rw [hRf,e.apply_symm_apply]
    exact hright.eq_of_nhds.trans (congrArg Q.curve heR)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleLocusSmoothStructure
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transverse ordered double locus carries its actual smooth
one-dimensional manifold structure, built from the proved submersion charts. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

lemma transverseDoubleChart_mem
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (p : surfaceDoublePairs f) : p ∈ (transverseDoubleChart hf hreg p).coord.source :=
  (exists_smooth_double_chart hf p (hreg _ _ p.property.1 p.property.2)).choose_spec

@[instance_reducible]
def doubleLocusChartedSpace
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y)) :
    ChartedSpace ℝ (surfaceDoublePairs f) where
  atlas := range fun p => (transverseDoubleChart hf hreg p).coord
  chartAt := fun p => (transverseDoubleChart hf hreg p).coord
  mem_chart_source := transverseDoubleChart_mem hf hreg
  chart_mem_atlas := fun p => ⟨p,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleArcChartPartition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact embedded arc in the actual transverse double locus has a
finite ordered subdivision into the smooth regular chart arcs constructed above. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem double_arc_chart_partition
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    {γ : ℝ → surfaceDoublePairs f} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ), τ 0 = a ∧ Monotone τ ∧
      (∀ n, a ≤ τ n ∧ τ n ≤ b) ∧ (∀ n ≥ N, τ n = b) ∧
      ∀ n, ∃ c : SmoothDoubleChart f,
        MapsTo γ (Icc (τ n) (τ (n+1))) c.coord.source := by
  let C : surfaceDoublePairs f → Set (Icc a b) := fun p =>
    (fun t : Icc a b => γ t) ⁻¹' (transverseDoubleChart hf hreg p).coord.source
  have hC : ∀ p, IsOpen (C p) := fun p =>
    (transverseDoubleChart hf hreg p).coord.open_source.preimage hγ.domRestrict
  have hcover : univ ⊆ ⋃ p, C p := by
    intro t _
    refine mem_iUnion.mpr ⟨γ t,?_⟩
    exact transverseDoubleChart_mem hf hreg (γ t)
  obtain ⟨τ,hzero,hmono,⟨N,hend⟩,hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hC hcover
  refine ⟨fun n => (τ n).val,N,hzero,fun _ _ h => hmono h,
    fun n => (τ n).property,hend,?_⟩
  intro n
  obtain ⟨p,hp⟩ := hsub n
  refine ⟨transverseDoubleChart hf hreg p,?_⟩
  intro r hr
  have hrab : r ∈ Icc a b := ⟨(τ n).property.1.trans hr.1,hr.2.trans (τ (n+1)).property.2⟩
  exact hp (show (⟨r,hrab⟩ : Icc a b) ∈ Icc (τ n) (τ (n+1)) from hr)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OrderedArcSeparation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Consecutive subarcs of an embedded arc have disjoint interiors.
This supplies the separation needed by the smooth joining operation. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem ordered_arc_images_separated {γ : ℝ → N} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hi : InjOn γ (Icc a c))
    (P Q : SmoothCompactArc I N)
    (hP : P.curve '' Icc P.start P.finish = γ '' Icc a b)
    (hQ : Q.curve '' Icc Q.start Q.finish = γ '' Icc b c)
    (hstart : Q.curve Q.start = γ b) :
    ∀ u ∈ Icc P.start P.finish, ∀ v ∈ Ioc Q.start Q.finish,
      P.curve u ≠ Q.curve v := by
  intro u hu v hv he
  obtain ⟨s,hs,hes⟩ := hP.subset ⟨u,hu,rfl⟩
  obtain ⟨t,ht,het⟩ := hQ.subset ⟨v,⟨hv.1.le,hv.2⟩,rfl⟩
  have hst : s = t := hi ⟨hs.1,hs.2.trans hbc⟩ ⟨hab.trans ht.1,ht.2⟩
    (hes.trans (he.trans het.symm))
  have htb : t = b := le_antisymm (hst ▸ hs.2) ht.1
  have hev : Q.curve v = Q.curve Q.start := het.symm.trans ((congrArg γ htb).trans hstart.symm)
  have hv0 := Q.injective ⟨hv.1.le,hv.2⟩
    (left_mem_Icc.mpr Q.start_lt_finish.le) hev
  exact (ne_of_gt hv.1) hv0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact smooth double arc retains the final chart germ. This is
precisely the data needed to continue it through the next chart of a finite cover. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem smooth_double_arc (c : SmoothDoubleChart f) {γ : ℝ → surfaceDoublePairs f}
    {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) (hsource : MapsTo γ (Icc a b) c.coord.source) :
    ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish = (fun t => (γ t).val) '' Icc a b ∧
      P.lift P.arc.start = γ a ∧ P.lift P.arc.finish = γ b := by
  obtain ⟨A,s,hs,hcurve,hstart,hfinish,himage,hleft,hright⟩ :=
    c.oriented_arc hab hγ hinj hsource
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have htarget : s*A.finish ∈ c.coord.target := by
    rw [hfinish,← mul_assoc,hss,one_mul]
    exact c.coord.map_source (hsource (right_mem_Icc.mpr hab.le))
  let P : SmoothDoubleArc f := ⟨A,(fun t => c.coord.symm (s*t)),
    (fun t => congrFun hcurve t),c,s,hs,Homeomorph.refl ℝ,
    contDiff_id,contDiff_id,strictMono_id,Filter.Eventually.of_forall (fun _ => rfl),htarget⟩
  refine ⟨P,himage,?_,?_⟩
  · apply Subtype.val_injective
    exact (P.curve_eq P.arc.start).symm.trans hleft
  · apply Subtype.val_injective
    exact (P.curve_eq P.arc.finish).symm.trans hright

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleArcAppend
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue a compact smooth double arc through an actual next chart.
The chart orientation is forced by the disjointness of the two arc interiors. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3}
namespace SmoothDoubleArc

theorem append_chart (P : SmoothDoubleArc f)
    (Q : SmoothCompactArc (planeModel.prod planeModel) (M × M))
    (c : SmoothDoubleChart f) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hQ : ∀ t, Q.curve t = (c.coord.symm (s*t)).val)
    (hsource : P.lift P.arc.finish ∈ c.coord.source)
    (hstart : Q.start = s*c.coord (P.lift P.arc.finish))
    (hfinish : s*Q.finish ∈ c.coord.target)
    (hcross : ∀ u ∈ Icc P.arc.start P.arc.finish, ∀ v ∈ Ioc Q.start Q.finish,
      P.arc.curve u ≠ Q.curve v) :
    ∃ R : SmoothDoubleArc f,
      R.arc.curve '' Icc R.arc.start R.arc.finish =
        P.arc.curve '' Icc P.arc.start P.arc.finish ∪ Q.curve '' Icc Q.start Q.finish ∧
      R.lift R.arc.start = P.lift P.arc.start ∧
      R.lift R.arc.finish = c.coord.symm (s*Q.finish) := by
  have hx : P.sign*P.parameter P.arc.finish ∈ c.overlap P.tail := by
    refine ⟨P.tail_target,?_⟩
    change P.tail.coord.symm (P.sign*P.parameter P.arc.finish) ∈ c.coord.source
    rw [← P.tail_germ.eq_of_nhds]
    exact hsource
  obtain ⟨U,h,hU,hxU,hhs,hhn,hval,heq⟩ :=
    P.tail.reparameterized_transition c P.sign_eq hs P.parameter
      P.parameter_smooth P.inverse_smooth hx
  have ha : h P.arc.finish = Q.start := by
    rw [hval,← P.tail_germ.eq_of_nhds,← hstart]
  have hmatch : P.arc.curve =ᶠ[𝓝 P.arc.finish] Q.curve ∘ h := by
    filter_upwards [P.tail_germ,heq] with t ht ht'
    change P.arc.curve t = Q.curve (h t)
    rw [P.curve_eq,hQ,ht,ht']
  have hpos : 0 < deriv h P.arc.finish :=
    arc_join_deriv_pos P.arc.start_lt_finish Q.start_lt_finish
      ((hhs.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hhn ha hmatch hcross
  obtain ⟨A,e,hes,hei,hem,hea,hAstart,hAfinish,hAcurve,hAimage⟩ :=
    P.arc.join Q hU hhs hxU hpos ha hmatch hcross
  have hcut : P.arc.finish < A.finish := by
    rw [hAfinish]
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact Q.start_lt_finish
  let L : ℝ → surfaceDoublePairs f := joinedCurve P.arc.finish P.lift
    (fun t => c.coord.symm (s*e t))
  have hcurve : ∀ t, A.curve t = (L t).val := by
    intro t
    rw [hAcurve]
    dsimp only [L,joinedCurve,Function.comp_apply]
    split_ifs with ht
    · exact P.curve_eq t
    · exact hQ (e t)
  have htail : L =ᶠ[𝓝 A.finish] (fun t => c.coord.symm (s*e t)) :=
    joinedCurve_germ_right P.arc.finish P.lift (fun t => c.coord.symm (s*e t)) hcut
  have htarget : s*e A.finish ∈ c.coord.target := by
    rw [hAfinish,e.apply_symm_apply]
    exact hfinish
  let R : SmoothDoubleArc f := ⟨A,L,hcurve,c,s,hs,e,hes,hei,hem,htail,htarget⟩
  refine ⟨R,hAimage,?_,?_⟩
  · change L A.start = P.lift P.arc.start
    rw [hAstart]
    dsimp only [L,joinedCurve]
    rw [ite_eq_left P.arc.start_lt_finish.le]
  · change L A.finish = c.coord.symm (s*Q.finish)
    dsimp only [L,joinedCurve]
    rw [ite_eq_right (not_le.mpr hcut),hAfinish,e.apply_symm_apply]

end SmoothDoubleArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleArcExtension
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual extension step for an embedded topological double arc:
append the next chart segment and retain the exact image and endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3}

theorem extend_smooth_double_arc {γ : ℝ → surfaceDoublePairs f} {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (hγ : ContinuousOn γ (Icc a c))
    (hi : InjOn γ (Icc a c)) (P : SmoothDoubleArc f)
    (hP : P.arc.curve '' Icc P.arc.start P.arc.finish = (fun t => (γ t).val) '' Icc a b)
    (hleft : P.lift P.arc.start = γ a) (hright : P.lift P.arc.finish = γ b)
    (d : SmoothDoubleChart f) (hd : MapsTo γ (Icc b c) d.coord.source) :
    ∃ R : SmoothDoubleArc f,
      R.arc.curve '' Icc R.arc.start R.arc.finish = (fun t => (γ t).val) '' Icc a c ∧
      R.lift R.arc.start = γ a ∧ R.lift R.arc.finish = γ c := by
  have hsub : Icc b c ⊆ Icc a c := Icc_subset_Icc hab.le le_rfl
  obtain ⟨Q,s,hs,hQ,hQs,hQf,hQi,hQl,hQr⟩ :=
    d.oriented_arc hbc (hγ.mono hsub) (hi.mono hsub) hd
  have hcross := ordered_arc_images_separated hab.le hbc.le
    (Subtype.val_injective.comp_injOn hi) P.arc Q hP hQi hQl
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsource : P.lift P.arc.finish ∈ d.coord.source := by
    rw [hright]
    exact hd (left_mem_Icc.mpr hbc.le)
  have hstart : Q.start = s*d.coord (P.lift P.arc.finish) := by rw [hright]; exact hQs
  have hfinish : s*Q.finish ∈ d.coord.target := by
    rw [hQf,← mul_assoc,hss,one_mul]
    exact d.coord.map_source (hd (right_mem_Icc.mpr hbc.le))
  obtain ⟨R,hRi,hRl,hRr⟩ := P.append_chart Q d hs (fun t => congrFun hQ t)
    hsource hstart hfinish hcross
  refine ⟨R,?_,hRl.trans hleft,?_⟩
  · rw [hRi,hP,hQi,← Set.image_union,Icc_union_Icc_eq_Icc hab.le hbc.le]
  · apply Subtype.val_injective
    rw [hRr]
    exact (congrFun hQ Q.finish).symm.trans hQr

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleArcParameterization
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded compact topological arc in the actual transverse double
locus admits a smooth regular parameterization with the same image and endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem smooth_double_arc_parameterization
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    {γ : ℝ → surfaceDoublePairs f} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (hi : InjOn γ (Icc a b)) :
    ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish = (fun t => (γ t).val) '' Icc a b ∧
      P.lift P.arc.start = γ a ∧ P.lift P.arc.finish = γ b := by
  obtain ⟨τ,N,hzero,hmono,hbounds,hend,hcharts⟩ :=
    double_arc_chart_partition hf hreg hab.le hγ
  have hstep : ∀ n, τ n = a ∨ (a < τ n ∧ ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish = (fun t => (γ t).val) '' Icc a (τ n) ∧
      P.lift P.arc.start = γ a ∧ P.lift P.arc.finish = γ (τ n)) := by
    intro n
    induction n with
    | zero => exact Or.inl hzero
    | succ n ih =>
      have hle : τ n ≤ τ (n+1) := hmono (Nat.le_succ n)
      by_cases heq : τ n = τ (n+1)
      · simpa only [Nat.succ_eq_add_one,← heq] using ih
      have hlt : τ n < τ (n+1) := lt_of_le_of_ne hle heq
      obtain ⟨c,hc⟩ := hcharts n
      have hsub : Icc (τ n) (τ (n+1)) ⊆ Icc a b :=
        Icc_subset_Icc (hbounds n).1 (hbounds (n+1)).2
      rcases ih with hna | ⟨han,P,hPi,hPl,hPr⟩
      · obtain ⟨P,hPi,hPl,hPr⟩ := c.smooth_double_arc hlt (hγ.mono hsub) (hi.mono hsub) hc
        refine Or.inr ⟨hna ▸ hlt,P,?_,?_,hPr⟩
        · simpa only [hna] using hPi
        · simpa only [hna] using hPl
      · have hsub' : Icc a (τ (n+1)) ⊆ Icc a b := Icc_subset_Icc le_rfl (hbounds (n+1)).2
        obtain ⟨R,hRi,hRl,hRr⟩ := extend_smooth_double_arc han hlt
          (hγ.mono hsub') (hi.mono hsub') P hPi hPl hPr c hc
        exact Or.inr ⟨han.trans hlt,R,hRi,hRl,hRr⟩
  have hN : τ N = b := hend N le_rfl
  rcases hstep N with he | ⟨_,P,hPi,hPl,hPr⟩
  · exact False.elim (hab.ne (he.symm.trans hN))
  · exact ⟨P,by simpa only [hN] using hPi,hPl,by simpa only [hN] using hPr⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothInteriorDoubleArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact interior segments of the actual crosscap-connecting path
inherit smooth regular embedded double-curve parameterizations. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem smooth_interior_double_arc
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish =
        Γ '' {t : I | a ≤ (t:ℝ) ∧ (t:ℝ) ≤ b} ∧
      P.arc.curve P.arc.start = Γ ⟨a,⟨ha.le,(hab.trans hb).le⟩⟩ ∧
      P.arc.curve P.arc.finish = Γ ⟨b,⟨(ha.trans hab).le,hb.le⟩⟩ := by
  let κ := projIcc a b hab.le
  let θ : ℝ → I := fun t => ⟨(κ t).val,⟨ha.le.trans (κ t).property.1,(κ t).property.2.trans hb.le⟩⟩
  have hκc : Continuous κ := continuous_projIcc
  have hθ : Continuous θ := (continuous_subtype_val.comp hκc).subtype_mk _
  let γ : ℝ → surfaceDoublePairs f := fun t =>
    ⟨Γ (θ t),hne (θ t) (ha.trans_le (κ t).property.1) ((κ t).property.2.trans_lt hb),heq (θ t)⟩
  have hγ : Continuous γ := (hΓ.comp hθ).subtype_mk _
  have hκ : ∀ t ∈ Icc a b, (κ t).val = t := by
    intro t ht
    exact congrArg Subtype.val (projIcc_of_mem hab.le ht)
  have hγinj : InjOn γ (Icc a b) := by
    intro t ht u hu he
    have hθeq : θ t = θ u := hinj (congrArg Subtype.val he)
    have hval := congrArg Subtype.val hθeq
    change (κ t).val = (κ u).val at hval
    rwa [hκ t ht,hκ u hu] at hval
  obtain ⟨P,hPi,hPl,hPr⟩ := smooth_double_arc_parameterization hf hreg hab hγ.continuousOn hγinj
  have hi : (fun t => (γ t).val) '' Icc a b = Γ '' {t : I | a ≤ (t:ℝ) ∧ (t:ℝ) ≤ b} := by
    apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      exact ⟨θ t,⟨(κ t).property.1,(κ t).property.2⟩,rfl⟩
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨(t:ℝ),ht,?_⟩
      change Γ (θ (t:ℝ)) = Γ t
      apply congrArg Γ
      apply Subtype.ext
      exact hκ t ht
  refine ⟨P,hPi.trans hi,?_,?_⟩
  · rw [P.curve_eq,hPl]
    change Γ (θ a) = _
    apply congrArg Γ
    apply Subtype.ext
    exact hκ a (left_mem_Icc.mpr hab.le)
  · rw [P.curve_eq,hPr]
    change Γ (θ b) = _
    apply congrArg Γ
    apply Subtype.ext
    exact hκ b (right_mem_Icc.mpr hab.le)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_UnitIntervalArcImages
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact compact subarc images under extension of a unit-interval path. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*} {Γ : I → N}

lemma unitInterval_extension_injective (hΓ : Function.Injective Γ) :
    (Icc (0:ℝ) 1).InjOn (Γ ∘ projIcc 0 1 zero_le_one) := by
  intro s hs t ht he
  have hh := congrArg Subtype.val (hΓ he)
  simpa only [projIcc_of_mem zero_le_one hs,projIcc_of_mem zero_le_one ht] using hh

lemma unitInterval_extension_image {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (Γ ∘ projIcc 0 1 zero_le_one) '' Icc a b =
      Γ '' {t : I | a ≤ (t:ℝ) ∧ (t:ℝ) ≤ b} := by
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    have ht01 : t ∈ Icc (0:ℝ) 1 := ⟨ha.trans ht.1,ht.2.trans hb⟩
    refine ⟨projIcc 0 1 zero_le_one t,?_,rfl⟩
    simpa only [mem_ofPred_eq,mem_Icc,projIcc_of_mem zero_le_one ht01] using ht
  · rintro y ⟨t,ht,rfl⟩
    refine ⟨(t:ℝ),ht,?_⟩
    change Γ (projIcc 0 1 zero_le_one t) = Γ t
    rw [projIcc_val]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothCrosscapConnectingArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the two actual crosscap endpoint pieces and the compact
interior into one smooth regular embedded ordered connecting arc. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem smooth_crosscap_connecting_arc_endpoint_regular
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ S : SmoothCompactArc (planeModel.prod planeModel) (M × M),
      S.curve '' Icc S.start S.finish = range Γ ∧
      S.curve S.start = (p,p) ∧ S.curve S.finish = (q,q) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (S.curve t).1) S.start) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (S.curve t).1) S.finish) := by
  obtain ⟨a,b,P,Q,ha,hab,hb,hPi,hQi,hP0,hQ1,hPa,hQb,hPg,hQg,hPreg,hQreg⟩ :=
    crosscap_end_arcs_regular cp cq hΓ hinj hzero hone heq hne
  let ua : I := ⟨a,⟨ha.le,(hab.trans hb).le⟩⟩
  let ub : I := ⟨b,⟨(ha.trans hab).le,hb.le⟩⟩
  obtain ⟨T,hTi,hTa,hTb⟩ := smooth_interior_double_arc hf hreg hΓ hinj heq hne ha hab hb
  let C : ℝ → M × M := Γ ∘ projIcc 0 1 zero_le_one
  have hCv (u : I) : C (u:ℝ) = Γ u := by
    change Γ (projIcc 0 1 zero_le_one u) = Γ u
    rw [projIcc_val]
  have hCi : (Icc (0:ℝ) 1).InjOn C := unitInterval_extension_injective hinj
  have hPiC : P.curve '' Icc P.start P.finish = C '' Icc 0 a := by
    rw [hPi,unitInterval_extension_image (Γ := Γ) (a := 0) (b := a) le_rfl (hab.trans hb).le]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨u.property.1,h⟩,fun h => h.2⟩
  have hQiC : Q.curve '' Icc Q.start Q.finish = C '' Icc b 1 := by
    rw [hQi,unitInterval_extension_image (Γ := Γ) (a := b) (b := 1) (ha.trans hab).le le_rfl]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨h,u.property.2⟩,fun h => h.1⟩
  have hTiC : T.arc.curve '' Icc T.arc.start T.arc.finish = C '' Icc a b := by
    rw [unitInterval_extension_image (Γ := Γ) ha.le hb.le]
    exact hTi
  have hTstart : T.arc.curve T.arc.start = C a := hTa.trans (hCv ua).symm
  have hTfinish : T.arc.curve T.arc.finish = C b := hTb.trans (hCv ub).symm
  have hTgood (t : ℝ) : T.arc.curve t ∈ surfaceDoublePairs f := by
    rw [T.curve_eq]
    exact (T.lift t).property
  let pa : surfaceDoublePairs f := ⟨Γ ua,hne ua ha (hab.trans hb),heq ua⟩
  have hpaP : pa.val = P.curve P.finish := (hPa ua rfl).symm
  have hpaT : pa.val = T.arc.curve T.arc.start := hTa.symm
  have hcrossPT := ordered_arc_images_separated ha.le hab.le
    (hCi.mono (Icc_subset_Icc le_rfl hb.le)) P T.arc hPiC hTiC hTstart
  obtain ⟨J,e,_,_,_,hJs,_,hJi,hJ0,hJ1,hJleft,hJgerm⟩ := join_pair_arcs hf hreg P T.arc pa hpaP hpaT hPg
    (Filter.Eventually.of_forall hTgood) hcrossPT
  have hJiC : J.curve '' Icc J.start J.finish = C '' Icc 0 b := by
    rw [hJi,hPiC,hTiC,← Set.image_union,Icc_union_Icc_eq_Icc ha.le hab.le]
  have hJgood : ∀ᶠ t in 𝓝 J.finish, J.curve t ∈ surfaceDoublePairs f := by
    filter_upwards [hJgerm] with t ht
    rw [ht]
    exact hTgood (e t)
  have hQstart : Q.curve Q.start = C b := (hQb ub rfl).trans (hCv ub).symm
  let pb : surfaceDoublePairs f := ⟨Γ ub,hne ub (ha.trans hab) hb,heq ub⟩
  have hpbJ : pb.val = J.curve J.finish := by
    exact (hJ1.trans hTb).symm
  have hpbQ : pb.val = Q.curve Q.start := (hQb ub rfl).symm
  have hcrossJQ := ordered_arc_images_separated (ha.trans hab).le hb.le hCi J Q hJiC hQiC hQstart
  obtain ⟨S,eS,heSs,heSi,_,hSs,hSf,hSi,hS0,hS1,hSleft,hSright⟩ := join_pair_arcs hf hreg J Q pb hpbJ hpbQ hJgood hQg hcrossJQ
  refine ⟨S,?_,hS0.trans (hJ0.trans hP0),hS1.trans hQ1,?_,?_⟩
  · rw [hSi,hJiC,hQiC,← Set.image_union,Icc_union_Icc_eq_Icc (ha.trans hab).le hb.le,
      unitInterval_extension_image (Γ := Γ) (a := 0) (b := 1) le_rfl le_rfl]
    have hset : {t : I | (0:ℝ) ≤ t ∧ (t:ℝ) ≤ 1} = univ := by
      ext t
      simp only [mem_ofPred_eq,mem_univ,iff_true]
      exact t.property
    rw [hset,image_univ]
  · have hstart : S.start = P.start := hSs.trans hJs
    have hg : S.curve =ᶠ[𝓝 P.start] P.curve := by
      rw [hstart] at hSleft
      rw [hJs] at hJleft
      exact hSleft.trans hJleft
    rw [hstart]
    have hPs := P.smooth.contMDiffAt (P.domain_open.mem_nhds
      (P.interval_subset (left_mem_Icc.mpr P.start_lt_finish.le)))
    exact regular_curve_germ (contMDiffAt_fst.comp _ hPs) (hg.fun_comp Prod.fst) hPreg
  · have heEnd : eS S.finish = Q.finish := by rw [hSf,eS.apply_symm_apply]
    have hQs := contMDiffAt_fst.comp Q.finish (Q.smooth.contMDiffAt (Q.domain_open.mem_nhds
      (Q.interval_subset (right_mem_Icc.mpr Q.start_lt_finish.le))))
    have hQr := regular_curve_reparameterization eS heSs heSi
      (by rw [heEnd]; exact hQs) (by rw [heEnd]; exact hQreg)
    have hQat : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (Q.curve t).1) (eS S.finish) := by
      rw [heEnd]
      exact hQs
    exact regular_curve_germ (hQat.comp S.finish (heSs.contMDiff.contMDiffAt))
      (hSright.fun_comp Prod.fst) hQr

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OrderedArcEndpointUnique
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton fibers over crosscaps prevent the source projection of an
ordered connecting arc from revisiting either singular endpoint. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} {Y : Type*} {f : M → Y} {p q : M} {Γ : I → M × M}

lemma ordered_arc_endpoints_distinct (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q)) : p ≠ q := by
  intro hpq
  have hpair : Γ 0 = Γ 1 := by rw [hzero,hone,hpq]
  have h := congrArg (fun t : I => (t:ℝ)) (hi hpair)
  norm_num at h

lemma ordered_arc_source_start_unique (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hne : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2)
    (hsing : ∀ x, f x = f p → x = p) :
    ∀ u : I, (Γ u).1 = p → u = 0 := by
  intro u hu
  by_contra hu0
  have hu1 : u ≠ 1 := by
    intro he
    rw [he,hone] at hu
    exact ordered_arc_endpoints_distinct hi hzero hone hu.symm
  have h0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (by
    intro he
    exact hu0 (Subtype.ext he.symm))
  have h1 : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
    intro he
    exact hu1 (Subtype.ext he))
  have hsecond : (Γ u).2 = p := hsing _ ((heq u).symm.trans (congrArg f hu))
  exact hne u h0 h1 (hu.trans hsecond.symm)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleCurveVelocities
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At two regular sheets the smooth paired double curve projects to
regular curves on both sheets.  Equal image velocities supply the key relation. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma equal_image_curve_derivatives {f : M → ProjectionTarget 3} {A B : ℝ → M} {t : ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ A t)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ B t)
    (heq : f ∘ A =ᶠ[𝓝 t] f ∘ B) :
    (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)).comp
        (mfderiv 𝓘(ℝ) planeModel A t) =
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t)).comp
        (mfderiv 𝓘(ℝ) planeModel B t) := by
  have he := heq.mfderiv_eq (I := 𝓘(ℝ)) (I' := 𝓘(ℝ,ProjectionTarget 3))
  rw [mfderiv_comp t (hf.mdifferentiable (by simp)).mdifferentiableAt
    (hA.mdifferentiableAt (by simp)),
    mfderiv_comp t (hf.mdifferentiable (by simp)).mdifferentiableAt
    (hB.mdifferentiableAt (by simp))] at he
  exact he

theorem regular_double_curve_velocities {f : M → ProjectionTarget 3}
    {A B : ℝ → M} {t : ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ A t)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ B t)
    (heq : f ∘ A =ᶠ[𝓝 t] f ∘ B)
    (hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel A t).prod (mfderiv 𝓘(ℝ) planeModel B t)))
    (hAf : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)))
    (hBf : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t))) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel A t) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel B t) :=
by
  have hrel := equal_image_curve_derivatives hf hA hB heq
  constructor
  · intro u v huv
    apply hpair
    apply Prod.ext huv
    change mfderiv 𝓘(ℝ) planeModel B t u = mfderiv 𝓘(ℝ) planeModel B t v
    apply hBf
    have hh := congrArg (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)) huv
    change ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)).comp
      (mfderiv 𝓘(ℝ) planeModel A t)) u =
      ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)).comp
      (mfderiv 𝓘(ℝ) planeModel A t)) v at hh
    rw [hrel] at hh
    exact hh
  · intro u v huv
    apply hpair
    apply Prod.ext _ huv
    change mfderiv 𝓘(ℝ) planeModel A t u = mfderiv 𝓘(ℝ) planeModel A t v
    apply hAf
    have hh := congrArg (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t)) huv
    change ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t)).comp
      (mfderiv 𝓘(ℝ) planeModel B t)) u =
      ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t)).comp
      (mfderiv 𝓘(ℝ) planeModel B t)) v at hh
    rw [← hrel] at hh
    exact hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularPairedArcProjection
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior regularity of both source sheets, together with the actual
endpoint germs, makes the first projection of the whole arc regular. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem regular_paired_arc_projection
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {Γ : I → M × M} (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 →
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (S : SmoothCompactArc (planeModel.prod planeModel) (M × M))
    (hSi : S.curve '' Icc S.start S.finish = range Γ)
    (hS0 : S.curve S.start = (p,p)) (hS1 : S.curve S.finish = (q,q))
    (hr0 : Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (S.curve t).1) S.start))
    (hr1 : Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (S.curve t).1) S.finish)) :
    ∀ t ∈ Icc S.start S.finish,
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (S.curve u).1) t) := by
  intro t ht
  by_cases hts : t = S.start
  · subst t
    exact hr0
  by_cases htf : t = S.finish
  · subst t
    exact hr1
  have hto : t ∈ Ioo S.start S.finish :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hts),lt_of_le_of_ne ht.2 htf⟩
  obtain ⟨u,hu⟩ := hSi.subset ⟨t,ht,rfl⟩
  have hu0 : u ≠ 0 := by
    intro he
    have hh : S.curve t = S.curve S.start := by rw [← hu,he,hzero,hS0]
    exact hts (S.injective ht (left_mem_Icc.mpr S.start_lt_finish.le) hh)
  have hu1 : u ≠ 1 := by
    intro he
    have hh : S.curve t = S.curve S.finish := by rw [← hu,he,hone,hS1]
    exact htf (S.injective ht (right_mem_Icc.mpr S.start_lt_finish.le) hh)
  have hureg := hgood u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm)))
    (lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he)))
  have hSt := S.smooth.contMDiffAt (S.domain_open.mem_nhds (S.interval_subset ht))
  have hA := contMDiffAt_fst.comp t hSt
  have hB := contMDiffAt_snd.comp t hSt
  have he : (fun r => f (S.curve r).1) =ᶠ[𝓝 t] (fun r => f (S.curve r).2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hto] with r hr
    obtain ⟨v,hv⟩ := hSi.subset ⟨r,⟨hr.1.le,hr.2.le⟩,rfl⟩
    rw [← hv]
    exact heq v
  exact (regular_double_curve_velocities hf hA hB he (compact_pair_arc_regular S (S.interval_subset ht))
    (by dsimp only [Function.comp_apply]; rw [← hu]; exact hureg.1)
    (by dsimp only [Function.comp_apply]; rw [← hu]; exact hureg.2)).1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapSourceEmbeddedPath
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual ordered crosscap connection gives an embedded source path
made from finitely many regular smooth pieces, inside the original source image. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_source_embedded_path_oai
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2 ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (hsing : ∀ x, f x = f p → x = p) :
    ∃ P : Path p q, FiniteRegularPath planeModel P ∧ Function.Injective P ∧
      range P ⊆ Prod.fst '' range Γ := by
  obtain ⟨S,hSi,hS0,hS1,hr0,hr1⟩ := smooth_crosscap_connecting_arc_endpoint_regular hf hreg
    cp cq hΓ hi hzero hone heq (fun u h0 h1 => (hgood u h0 h1).1)
  let γ : ℝ → M := fun t => (S.curve t).1
  have hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ S.domain := contMDiff_fst.comp_contMDiffOn S.smooth
  let U : Set ℝ := {t | t ∈ S.domain ∧ Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)}
  have hU : IsOpen U := curve_regular_locus_open S.domain_open hγ
  have hclosed : Icc S.start S.finish ⊆ U := by
    intro t ht
    exact ⟨S.interval_subset ht,regular_paired_arc_projection hf hzero hone heq
      (fun u h0 h1 => (hgood u h0 h1).2) S hSi hS0 hS1 hr0 hr1 t ht⟩
  have hγ0 : γ S.start = p := congrArg Prod.fst hS0
  have hγ1 : γ S.finish = q := congrArg Prod.fst hS1
  have havoid : ∀ t ∈ Ioc S.start S.finish, γ t ≠ γ S.start := by
    intro t ht he
    obtain ⟨u,hu⟩ := hSi.subset ⟨t,⟨ht.1.le,ht.2⟩,rfl⟩
    have hup : (Γ u).1 = p := (congrArg Prod.fst hu).trans (he.trans hγ0)
    have hu0 := ordered_arc_source_start_unique hi hzero hone heq
      (fun u h0 h1 => (hgood u h0 h1).1) hsing u hup
    have heS : S.curve t = S.curve S.start := by rw [← hu,hu0,hzero,hS0]
    exact (ne_of_gt ht.1) (S.injective ⟨ht.1.le,ht.2⟩
      (left_mem_Icc.mpr S.start_lt_finish.le) heS)
  obtain ⟨P,hPp,hPi,hPr⟩ := regular_curve_loop_removal hU (hγ.mono (fun _ ht => ht.1))
    (fun _ ht => ht.2) S.start_lt_finish hclosed havoid
  let Q : Path p q := P.cast hγ0.symm hγ1.symm
  refine ⟨Q,hPp.cast _ _,hPi,hPr.trans ?_⟩
  rintro x ⟨t,ht,rfl⟩
  exact ⟨S.curve t,hSi.subset ⟨t,ht,rfl⟩,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscap_source_embedded_path_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscap_source_embedded_path_oai.{u_1}
