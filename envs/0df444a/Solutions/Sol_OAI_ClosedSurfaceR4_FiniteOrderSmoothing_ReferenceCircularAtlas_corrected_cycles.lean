-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:13.458478+00:00
-- url     : https://prove2.me/submissions/0ee9e7e4-2687-41cb-a917-d9540f6974cf

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_corrected_smooth_family

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPartition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

lemma finite_positive_threshold {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ i, z ≤ v i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image v)
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,Finset.min'_le s 1 (Finset.mem_insert_self _ _),?_⟩
  · have hm := s.min'_mem hs
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hm
    rcases hm with he | ⟨i,hi⟩
    · rw [he]; norm_num
    · rw [← hi]; exact hv i
  · intro i
    exact Finset.min'_le s (v i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma linear_apply_basis (A : Base →L[ℝ] Base) (v : Base) :
    A v = v.1 • A dx + v.2 • A dy := by
  calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
       _ = _ := by simp

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JacobianBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter

lemma coordDet_comp (A B : Base →L[ℝ] Base) :
    coordDet (A.comp B) = coordDet A * coordDet B := by
  simp only [coordDet,ContinuousLinearMap.comp_apply]
  rw [linear_apply_basis A (B dx),linear_apply_basis A (B dy)]
  simp
  ring

lemma coordDet_id : coordDet (ContinuousLinearMap.id ℝ Base) = 1 := by
  simp [coordDet,dx,dy]

lemma coordDet_fderiv_ne_zero_of_local_inverse {φ ψ : Base → Base} {U V : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) {p : Base} (hp : p ∈ U) :
    coordDet (fderiv ℝ φ p) ≠ 0 := by
  have hφp := ((hφ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hψp := ((hψ (φ p) (hmap hp)).contDiffAt (hV.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : ψ ∘ φ =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hinv hq
  have hcomp : (fderiv ℝ ψ (φ p)).comp (fderiv ℝ φ p) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p hψp hφp,he.fderiv_eq,fderiv_id]
  have hdet := congrArg coordDet hcomp
  rw [coordDet_comp,coordDet_id] at hdet
  intro hz
  simp [hz] at hdet



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

lemma coordinateTransition_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p) (coordinateTransition q p).source := by
  apply ContMDiffOn.contDiffOn
  exact (coordinateChart_smoothOn q).comp
    ((coordinateChart_symm_smoothOn p).mono (fun x hx => hx.1)) (fun x hx => hx.2)

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_symm (q p : M) :
    (coordinateTransition q p).symm = coordinateTransition p q := by
  simp [coordinateTransition,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

lemma coordinateTransition_symm_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p).symm (coordinateTransition q p).target := by
  have h := coordinateTransition_smoothOn p q
  rw [← coordinateTransition_symm q p] at h
  exact h



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


lemma phaseLinear_apply (ξ x : SmallModes.Base) : phaseLinear ξ x = ξ.1*x.1+ξ.2*x.2 := rfl

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_apply_chart (q p : M) {a : M}
    (ha : a ∈ (coordinateChart p).source) :
    coordinateTransition q p (coordinateChart p a) = coordinateChart q a := by
  change coordinateChart q ((coordinateChart p).symm (coordinateChart p a)) = _
  rw [(coordinateChart p).left_inv ha]

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_mem_chart (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    coordinateChart p a ∈ (coordinateTransition q p).source := by
  constructor
  · exact (coordinateChart p).map_source hap
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rwa [(coordinateChart p).left_inv hap]



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

/-- Each overlap transports a global weighted bound with fixed constants. -/
theorem pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m C h →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m (D * C)
        (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.localize_restore]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasJetCoordinateRelation
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized atlas maps on a coordinate overlap.  The transition
scalar is the square of the outer cutoff.  A nonzero partition weight gives
the needed equality of germs without any extra plateau hypothesis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma outer_eventually_one_of_weight_ne_zero (i : A.centers) {p : M}
    (hp : A.weight i p ≠ 0) :
    A.outer i =ᶠ[𝓝 p] (fun _ => 1) := by
  have hn : ∀ᶠ q in 𝓝 p, A.weight i q ≠ 0 :=
    (isOpen_ne.preimage (A.weight_smooth i).continuous).mem_nhds hp
  filter_upwards [hn] with q hq
  exact A.outer_one i q (subset_tsupport (A.weight i) hq)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPhaseChart
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A noncritical smooth phase is the first coordinate of a smooth local chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma phaseLinear_phaseDerivative (φ : Base → ℝ) (p : Base) :
    phaseLinear (phaseDerivative φ p) = fderiv ℝ φ p := by
  apply ContinuousLinearMap.ext
  intro v
  have he : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]
  conv_rhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,phaseLinear_apply,phaseDerivative]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ConvexQuadraticPhase
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual convex phases used in finite primitive preparation. Their
coordinate covariant Hessians are uniformly positive on a sufficiently
small disk when the metric connection has a fixed bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma convexQuadraticPhase_smooth (ell : Base) (L : ℝ) :
    ContDiff ℝ ∞ (convexQuadraticPhase ell L) := by
  exact (phaseLinear ell).contDiff.add
    (contDiff_const.mul ((contDiff_fst.pow 2).add (contDiff_snd.pow 2)))

lemma convexQuadraticPhase_hasFDerivAt (ell : Base) (L : ℝ) (p : Base) :
    HasFDerivAt (convexQuadraticPhase ell L) (phaseLinear (ell + L • p)) p := by
  have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := p)
  have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p)
  have hh := (phaseLinear ell).hasFDerivAt (x := p) |>.add
    (((h1.pow 2).add (h2.pow 2)).const_mul (L / 2))
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, smul_apply, phaseLinear_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    two_smul, smul_eq_mul]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredConvexPhase
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex phases centered at the actual coordinate center of a circular
patch. The connection is evaluated at the original point, so translation
of the phase does not silently translate the metric. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma centeredConvexPhase_smooth (ell : Base) (L : ℝ) (c : Base) :
    ContDiff ℝ ∞ (centeredConvexPhase ell L c) :=
  (convexQuadraticPhase_smooth ell L).comp (contDiff_id.sub contDiff_const)

lemma centeredConvexPhase_hasFDerivAt (ell : Base) (L : ℝ) (c p : Base) :
    HasFDerivAt (centeredConvexPhase ell L c) (phaseLinear (ell+L • (p-c))) p := by
  have ht : HasFDerivAt (fun x : Base => x-c) (ContinuousLinearMap.id ℝ Base) p :=
    (hasFDerivAt_id p).sub_const c
  simpa only [centeredConvexPhase,Function.comp_def,ContinuousLinearMap.comp_id] using!
    (convexQuadraticPhase_hasFDerivAt ell L (p-c)).comp p ht

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PublishedInputs
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Whitney immersion and Sard regular-value statements for surfaces

The compact surface specialization of Whitney's immersion theorem and
the equal-dimensional surface case of Sard's theorem provide the
initial immersion and the regular parameters of the construction.
-/

noncomputable section

namespace ClosedSurfaceR4.PublishedInputs

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

/-- The critical values of a smooth map between planes have zero volume. -/
theorem sardSurfaceInput : SardSurfaceInput := by
  intro f hf
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun x => fderiv ℝ f x)
  · intro x _
    exact (hf.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    change ¬ Function.Surjective (fderiv ℝ f x) at hx
    change LinearMap.det (fderiv ℝ f x).toLinearMap = 0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    exact fun hinj => hx (LinearMap.injective_iff_surjective.mp hinj)

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteRegularFibers
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular two-dimensional coordinate values have finite fibers on a
compact set. This supplies the finite crossing sets for generic radii. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PublishedInputs

lemma regular_point_locally_injective {f : Plane → Plane} (hf : ContDiff ℝ ∞ f)
    {x : Plane} (hreg : Function.Surjective (fderiv ℝ f x)) :
    ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧ U.InjOn f := by
  have hinj : Function.Injective (fderiv ℝ f x) :=
    LinearMap.injective_iff_surjective.mpr hreg
  let L : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.ofBijective (fderiv ℝ f x)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hreg)
  have hd : HasFDerivAt f L.toContinuousLinearMap x :=
    (hf.differentiable (by simp) x).hasFDerivAt
  let e := hf.contDiffAt.toOpenPartialHomeomorph f hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ⟨e.source,e.open_source,hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),e.injOn⟩

theorem finite_compact_regular_fiber {f : Plane → Plane} (hf : ContDiff ℝ ∞ f)
    {K : Set Plane} (hK : IsCompact K) (y : Plane)
    (hreg : ∀ x ∈ K, f x = y → Function.Surjective (fderiv ℝ f x)) :
    (K ∩ {x | f x = y}).Finite := by
  have hcompact : IsCompact (K ∩ {x | f x = y}) :=
    hK.inter_right (isClosed_eq hf.continuous continuous_const)
  apply hcompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨U,hU,hxU,hUinj⟩ := regular_point_locally_injective hf (hreg x hx.1 hx.2)
  refine ⟨U,hU,?_⟩
  ext z
  constructor
  · rintro ⟨hzU,hzK,hzy⟩
    exact mem_singleton_iff.mpr (hUinj hzU hxU (hzy.trans hx.2.symm))
  · rintro rfl
    exact ⟨hxU,hx⟩

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowerDimensionalImage
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The triple-radius exceptional set is null. Extend a map from two to
three coordinates constantly in the final coordinate and apply the proved
fixed-dimensional Jacobian null-image theorem. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

local instance tripleVolumeHaar : (volume : Measure (Plane × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem smooth_surface_image_volume_zero (f : Plane → Plane × ℝ)
    (hf : ContDiff ℝ ∞ f) : volume (Set.range f) = 0 := by
  let g : Plane × ℝ → Plane × ℝ := fun x => f x.1
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  have hdet (x : Plane × ℝ) : LinearMap.det (fderiv ℝ g x).toLinearMap = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hinj
    have hd : fderiv ℝ g x = (fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ Plane ℝ) := by
      change fderiv ℝ (f ∘ (Prod.fst : Plane × ℝ → Plane)) x = _
      rw [fderiv_comp x (hf.differentiable (by simp) x.1) differentiableAt_fst, fderiv_fst]
    have hzero : fderiv ℝ g x (0,1) = fderiv ℝ g x 0 := by
      rw [hd]
      simp
    have he := congrArg Prod.snd (hinj hzero)
    exact one_ne_zero he
  have hnull : volume (g '' (univ : Set (Plane × ℝ))) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ g x)
    · intro x _
      exact (hg.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
    · intro x _
      exact hdet x
  have he : g '' (univ : Set (Plane × ℝ)) = Set.range f := by
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      exact ⟨x.1,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨(x,0),mem_univ _,rfl⟩
  rwa [he] at hnull

/-- On a compact chart set, parameters avoiding a triple intersection form
an open dense set. -/
theorem compact_surface_image_open_dense (f : Plane → Plane × ℝ)
    (hf : ContDiff ℝ ∞ f) {K : Set Plane} (hK : IsCompact K) :
    IsOpen (f '' K)ᶜ ∧ Dense (f '' K)ᶜ := by
  refine ⟨(hK.image hf.continuous).isClosed.isOpen_compl,?_⟩
  have hnull : volume (f '' K) = 0 := measure_mono_null (image_subset_range _ _)
    (smooth_surface_image_volume_zero f hf)
  apply Measure.dense_of_ae (μ := (volume : Measure (Plane × ℝ)))
  simpa only [ae_iff,mem_compl_iff,not_not,Set.ofPred_mem_eq] using hnull

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CurvePhaseParameterGraph
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A chart of the critical-point equation for an affine perturbation of
a quadratic phase along a regular plane curve. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry

lemma curvePhaseParameterGraph_eq {u v : ℝ → CurvePlane} {L t : ℝ} {ell : CurvePlane}
    (hspeed : (v t).1 ≠ 0) (hcrit : curvePhaseVelocity u v L t ell = 0) :
    curvePhaseParameterGraph u v L (t,ell.2) = ell := by
  apply Prod.ext
  · change (-ell.2*(v t).2-L*((u t).1*(v t).1+(u t).2*(v t).2))/(v t).1 = ell.1
    apply (div_eq_iff hspeed).mpr
    dsimp [curvePhaseVelocity] at hcrit
    nlinarith
  · rfl

lemma curvePhaseParameterGraph_deriv_zero {u v w : ℝ → CurvePlane}
    {L t : ℝ} {ell : CurvePlane}
    (hu : HasDerivAt u (v t) t) (hv : HasDerivAt v (w t) t)
    (hspeed : (v t).1 ≠ 0)
    (hcrit : curvePhaseVelocity u v L t ell = 0)
    (hdeg : curvePhaseAcceleration u v w L t ell = 0) :
    HasDerivAt (fun s => curvePhaseParameterGraph u v L (s,ell.2)) 0 t := by
  have hu1 : HasDerivAt (fun s => (u s).1) (v t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hu2 : HasDerivAt (fun s => (u s).2) (v t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hv1 : HasDerivAt (fun s => (v s).1) (w t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hv2 : HasDerivAt (fun s => (v s).2) (w t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hn := (hv2.const_mul (-ell.2)).sub
    (((hu1.mul hv1).add (hu2.mul hv2)).const_mul L)
  have hquot := hn.div hv1 hspeed
  have hnval : -ell.2*(v t).2-L*((u t).1*(v t).1+(u t).2*(v t).2) =
      ell.1*(v t).1 := by
    dsimp [curvePhaseVelocity] at hcrit
    nlinarith
  have hnprime : -ell.2*(w t).2-
      L*(((v t).1*(v t).1+(u t).1*(w t).1)+
        ((v t).2*(v t).2+(u t).2*(w t).2)) = ell.1*(w t).1 := by
    dsimp [curvePhaseAcceleration] at hdeg
    nlinarith
  have hd := hquot.prodMk (hasDerivAt_const t ell.2)
  refine hd.congr_deriv (Eq.symm ?_)
  · change (0 : CurvePlane) =
      (((-ell.2*(w t).2-L*(((v t).1*(v t).1+(u t).1*(w t).1)+
      ((v t).2*(v t).2+(u t).2*(w t).2)))*(v t).1-
      (-ell.2*(v t).2-L*((u t).1*(v t).1+(u t).2*(v t).2))*(w t).1)/
        ((v t).1)^2,0)
    rw [hnval,hnprime]
    ext <;> dsimp
    ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CurvePhaseCriticalValues
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degenerate tangencies along a curve form a null set of linear phase
parameters. The first-coordinate chart of the critical equation suffices
where the first velocity component is nonzero. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
local instance curvePlaneVolumeHaar : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

lemma curvePhaseParameterGraph_differentiableAt {u v : ℝ → CurvePlane} {L : ℝ}
    {x : CurvePlane} (hu : DifferentiableAt ℝ u x.1) (hv : DifferentiableAt ℝ v x.1)
    (hspeed : (v x.1).1 ≠ 0) :
    DifferentiableAt ℝ (curvePhaseParameterGraph u v L) x := by
  have huc : DifferentiableAt ℝ (fun z : CurvePlane => u z.1) x :=
    hu.comp x differentiableAt_fst
  have hvc : DifferentiableAt ℝ (fun z : CurvePlane => v z.1) x :=
    hv.comp x differentiableAt_fst
  have hsnd : DifferentiableAt ℝ (Prod.snd : CurvePlane → ℝ) x := differentiableAt_snd
  have hnum : DifferentiableAt ℝ (fun z : CurvePlane =>
      -z.2*(v z.1).2-L*((u z.1).1*(v z.1).1+(u z.1).2*(v z.1).2)) x :=
    (hsnd.neg.mul hvc.snd).sub
    (((huc.fst.mul hvc.fst).add (huc.snd.mul hvc.snd)).const_mul L)
  have hquot := hnum.mul (hvc.fst.inv hspeed)
  convert hquot.prodMk hsnd using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [curvePhaseParameterGraph,Pi.mul_apply,Pi.inv_apply,div_eq_mul_inv]

lemma curvePhaseParameterGraph_singular {u v w : ℝ → CurvePlane} {L t : ℝ}
    {ell : CurvePlane} (hu : HasDerivAt u (v t) t) (hv : HasDerivAt v (w t) t)
    (hspeed : (v t).1 ≠ 0)
    (hcrit : curvePhaseVelocity u v L t ell = 0)
    (hdeg : curvePhaseAcceleration u v w L t ell = 0) :
    ¬ Function.Surjective (fderiv ℝ (curvePhaseParameterGraph u v L) (t,ell.2)) := by
  have hdiff := curvePhaseParameterGraph_differentiableAt (L := L) (x := (t,ell.2))
    hu.differentiableAt hv.differentiableAt hspeed
  have hline : HasDerivAt (fun s : ℝ => (s,ell.2)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t ell.2)
  have hchain := hdiff.hasFDerivAt.comp_hasDerivAt t hline
  have hz := curvePhaseParameterGraph_deriv_zero hu hv hspeed hcrit hdeg
  have hval : fderiv ℝ (curvePhaseParameterGraph u v L) (t,ell.2) (1,0) = 0 :=
    hchain.unique hz
  intro hsurj
  have hinj : Function.Injective (fderiv ℝ (curvePhaseParameterGraph u v L) (t,ell.2)) :=
    LinearMap.injective_iff_surjective.mpr hsurj
  have he : (1,0) = (0 : CurvePlane) := hinj (hval.trans (map_zero _).symm)
  exact one_ne_zero (congrArg Prod.fst he)

/-- The bad parameter set is contained in the critical values of the explicit
two-dimensional parameter graph. -/
theorem curve_phase_degenerate_parameters_null
    (u v w : ℝ → CurvePlane) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hdu : ∀ t, HasDerivAt u (v t) t) (hdv : ∀ t, HasDerivAt v (w t) t) (L : ℝ) :
    volume {ell : CurvePlane | ∃ t, (v t).1 ≠ 0 ∧
      curvePhaseVelocity u v L t ell = 0 ∧ curvePhaseAcceleration u v w L t ell = 0} = 0 := by
  let f := curvePhaseParameterGraph u v L
  let S : Set CurvePlane := {z | (v z.1).1 ≠ 0 ∧ ¬ Function.Surjective (fderiv ℝ f z)}
  have hnull : volume (f '' S) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ f x)
    · intro x hx
      exact (curvePhaseParameterGraph_differentiableAt
        (hu.differentiable (by simp) x.1) (hv.differentiable (by simp) x.1) hx.1).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      change LinearMap.det (fderiv ℝ f x).toLinearMap = 0
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot,ne_eq,LinearMap.ker_eq_bot]
      exact fun hi => hx.2 (LinearMap.injective_iff_surjective.mp hi)
  apply measure_mono_null _ hnull
  rintro ell ⟨t,hspeed,hcrit,hdeg⟩
  exact ⟨(t,ell.2),⟨hspeed,curvePhaseParameterGraph_singular (hdu t) (hdv t)
    hspeed hcrit hdeg⟩,curvePhaseParameterGraph_eq hspeed hcrit⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GenericCurvePhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic linear parts of the convex quadratic phases have only
nondegenerate critical points on each prescribed regular boundary arc. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
local instance genericCurveVolumeHaar : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

lemma curvePhaseVelocity_swap (u v : ℝ → CurvePlane) (L t : ℝ) (ell : CurvePlane) :
    curvePhaseVelocity (fun s => (u s).swap) (fun s => (v s).swap) L t ell.swap =
      curvePhaseVelocity u v L t ell := by
  dsimp [curvePhaseVelocity]
  ring

lemma curvePhaseAcceleration_swap (u v w : ℝ → CurvePlane) (L t : ℝ) (ell : CurvePlane) :
    curvePhaseAcceleration (fun s => (u s).swap) (fun s => (v s).swap)
      (fun s => (w s).swap) L t ell.swap = curvePhaseAcceleration u v w L t ell := by
  dsimp [curvePhaseAcceleration]
  ring

theorem curve_phase_all_degenerate_parameters_null
    (u v w : ℝ → CurvePlane) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hdu : ∀ t, HasDerivAt u (v t) t) (hdv : ∀ t, HasDerivAt v (w t) t) (L : ℝ) :
    volume {ell : CurvePlane | ∃ t, v t ≠ 0 ∧
      curvePhaseVelocity u v L t ell = 0 ∧ curvePhaseAcceleration u v w L t ell = 0} = 0 := by
  let B1 : Set CurvePlane := {ell | ∃ t, (v t).1 ≠ 0 ∧
    curvePhaseVelocity u v L t ell = 0 ∧ curvePhaseAcceleration u v w L t ell = 0}
  let B2 : Set CurvePlane := {ell | ∃ t, (v t).2 ≠ 0 ∧
    curvePhaseVelocity (fun s => (u s).swap) (fun s => (v s).swap) L t ell = 0 ∧
    curvePhaseAcceleration (fun s => (u s).swap) (fun s => (v s).swap)
      (fun s => (w s).swap) L t ell = 0}
  have h1 : volume B1 = 0 := curve_phase_degenerate_parameters_null u v w hu hv hdu hdv L
  have h2 : volume B2 = 0 := curve_phase_degenerate_parameters_null
    (fun s => (u s).swap) (fun s => (v s).swap) (fun s => (w s).swap)
    (hu.snd.prodMk hu.fst) (hv.snd.prodMk hv.fst)
    (fun t => (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hdu t))
    (fun t => (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hdv t)) L
  have hswap : Differentiable ℝ (Prod.swap : CurvePlane → CurvePlane) :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).differentiable
  have himage : volume (Prod.swap '' B2) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hswap.differentiableOn h2
  apply measure_mono_null _ (measure_union_null h1 himage)
  rintro ell ⟨t,hv0,hcrit,hdeg⟩
  by_cases hfirst : (v t).1 = 0
  · right
    have hsecond : (v t).2 ≠ 0 := by
      intro he
      apply hv0
      exact Prod.ext hfirst he
    refine ⟨ell.swap,⟨t,hsecond,?_,?_⟩,Prod.swap_swap ell⟩
    · simpa only [curvePhaseVelocity_swap] using hcrit
    · simpa only [curvePhaseAcceleration_swap] using hdeg
  · left
    exact ⟨t,hfirst,hcrit,hdeg⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonparallelPhaseCovectors
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two independently perturbed phase covectors can avoid parallelism in
every open parameter set. Only the two-dimensional determinant is used. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ClosedSurfaceR4.PhaseGeometry
local instance nonparallelVolumeHaar : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

lemma covectorDetMap_surjective {v : CurvePlane} (hv : v ≠ 0) :
    Function.Surjective (covectorDetMap v) := by
  intro r
  by_cases hfirst : v.1 = 0
  · have hsecond : v.2 ≠ 0 := by
      intro hs
      exact hv (Prod.ext hfirst hs)
    refine ⟨(-r/v.2,0),?_⟩
    change v.1*0-v.2*(-r/v.2) = r
    field_simp
    ring
  · refine ⟨(0,r/v.1),?_⟩
    change v.1*(r/v.1)-v.2*0 = r
    field_simp
    ring

lemma dense_nonzero_covectors : Dense ({0} : Set CurvePlane)ᶜ := by
  apply Measure.dense_of_ae (μ := (volume : Measure CurvePlane))
  simp only [ae_iff,mem_singleton_iff,not_not]
  exact measure_singleton 0

lemma covectorDet_open_dense :
    IsOpen {z : CurvePlane × CurvePlane | covectorDet z.1 z.2 ≠ 0} ∧
      Dense {z : CurvePlane × CurvePlane | covectorDet z.1 z.2 ≠ 0} := by
  have hc : Continuous (fun z : CurvePlane × CurvePlane => covectorDet z.1 z.2) := by
    dsimp [covectorDet]
    fun_prop
  refine ⟨isOpen_ne.preimage hc,?_⟩
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨⟨v,w⟩,hvw⟩ := hne
  obtain ⟨A,B,hA,hB,hvA,hwB,hAB⟩ := isOpen_prod_iff.mp hU v w hvw
  obtain ⟨v',hv'A,hv'⟩ := dense_nonzero_covectors.inter_open_nonempty A hA ⟨v,hvA⟩
  have hv0 : v' ≠ 0 := hv'
  have hR : Dense ({0} : Set ℝ)ᶜ := by
    apply Measure.dense_of_ae (μ := (volume : Measure ℝ))
    simp only [ae_iff,mem_singleton_iff,not_not]
    exact measure_singleton 0
  have hd := hR.preimage ((covectorDetMap v').isOpenMap (covectorDetMap_surjective hv0))
  obtain ⟨w',hw'B,hw'⟩ := hd.inter_open_nonempty B hB ⟨w,hwB⟩
  refine ⟨(v',w'),hAB ⟨hv'A,hw'B⟩,?_⟩
  exact hw'

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_IndependentPhaseProjections
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent linear phase parameters give open surjective projections.
This transfers the elementary nonparallel-covector condition to any finite
family of independently perturbed phases. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma phasePairProjection_surjective {i j : ι} (hij : i ≠ j) :
    Function.Surjective (phasePairProjection i j) := by
  intro y
  refine ⟨Function.update (Function.update (fun _ => 0) i y.1) j y.2,?_⟩
  apply Prod.ext
  · simp [phasePairProjection,hij]
  · simp [phasePairProjection]

omit [Fintype ι] [DecidableEq ι] in
lemma phaseProjection_surjective (i : ι) :
    Function.Surjective (ContinuousLinearMap.proj i : (ι → CurvePlane) →L[ℝ] CurvePlane) := by
  intro y
  exact ⟨fun _ => y,rfl⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CovectorPullbackParameters
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual pullback of phase covectors by a chart derivative. Its parameter
map is open when the chart determinant is nonzero. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma pullCovectorMap_apply (A : CurvePlane →L[ℝ] CurvePlane) (v : CurvePlane) :
    pullCovectorMap A v = pullCovector A v := by
  ext <;> simp [pullCovectorMap,pullCovector] <;> ring

lemma pullCovectorMap_surjective (A : CurvePlane →L[ℝ] CurvePlane)
    (hA : coordDet A ≠ 0) : Function.Surjective (pullCovectorMap A) := by
  intro y
  refine ⟨(((A dy).2*y.1-(A dx).2*y.2)/coordDet A,
    ((A dx).1*y.2-(A dy).1*y.1)/coordDet A),?_⟩
  rw [pullCovectorMap_apply]
  ext <;> dsimp [pullCovector] <;> field_simp [hA] <;> dsimp [coordDet] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independent_pulled_covectors_open_dense {i j : ι} (hij : i ≠ j)
    (A B : CurvePlane →L[ℝ] CurvePlane) (hA : coordDet A ≠ 0) (hB : coordDet B ≠ 0)
    (a b : CurvePlane) :
    IsOpen {ell : ι → CurvePlane |
      covectorDet (pullCovector A (ell i+a)) (pullCovector B (ell j+b)) ≠ 0} ∧
    Dense {ell : ι → CurvePlane |
      covectorDet (pullCovector A (ell i+a)) (pullCovector B (ell j+b)) ≠ 0} := by
  let T : (CurvePlane × CurvePlane) →L[ℝ] (CurvePlane × CurvePlane) :=
    ((pullCovectorMap A).comp (ContinuousLinearMap.fst ℝ CurvePlane CurvePlane)).prod
      ((pullCovectorMap B).comp (ContinuousLinearMap.snd ℝ CurvePlane CurvePlane))
  have hT : Function.Surjective T := by
    intro y
    obtain ⟨v,hv⟩ := pullCovectorMap_surjective A hA y.1
    obtain ⟨w,hw⟩ := pullCovectorMap_surjective B hB y.2
    exact ⟨(v,w),Prod.ext hv hw⟩
  let F : (ι → CurvePlane) → CurvePlane × CurvePlane :=
    fun ell => T (phasePairProjection i j ell+(a,b))
  have hF : Continuous F := by fun_prop
  have hopen : IsOpenMap F := (T.isOpenMap hT).comp
    ((isOpenMap_add_right (a,b)).comp
      ((phasePairProjection i j).isOpenMap (phasePairProjection_surjective hij)))
  have he : {ell : ι → CurvePlane |
      covectorDet (pullCovector A (ell i+a)) (pullCovector B (ell j+b)) ≠ 0} =
      F ⁻¹' {z | covectorDet z.1 z.2 ≠ 0} := by
    ext ell
    change covectorDet (pullCovector A (ell i+a)) (pullCovector B (ell j+b)) ≠ 0 ↔
      covectorDet (pullCovectorMap A (ell i+a)) (pullCovectorMap B (ell j+b)) ≠ 0
    rw [pullCovectorMap_apply,pullCovectorMap_apply]
  rw [he]
  exact ⟨covectorDet_open_dense.1.preimage hF,covectorDet_open_dense.2.preimage hopen⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredAtlasDifferentials
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered quadratic phase covectors expressed through actual chart
transitions, with the Jacobian nondegeneracy needed for parameter selection. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma centered_phaseDerivative_comp {f : CurvePlane → CurvePlane}
    {x : CurvePlane} (hf : DifferentiableAt ℝ f x) (ell c : CurvePlane) (L : ℝ) :
    phaseDerivative (centeredConvexPhase ell L c ∘ f) x =
      pullCovector (fderiv ℝ f x) (ell+L • (f x-c)) := by
  unfold phaseDerivative
  rw [fderiv_comp x ((centeredConvexPhase_smooth ell L c).differentiable (by simp) _) hf,
    (centeredConvexPhase_hasFDerivAt ell L c (f x)).fderiv]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateTransition_det_ne (q p : M) {x : CurvePlane}
    (hx : x ∈ (coordinateTransition q p).source) :
    coordDet (fderiv ℝ (coordinateTransition q p) x) ≠ 0 := by
  let e := coordinateTransition q p
  exact coordDet_fderiv_ne_zero_of_local_inverse e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun y hy => e.left_inv hy) hx

lemma actual_centered_phase_differential (q p : M) (ell c : CurvePlane) (L : ℝ)
    {x : CurvePlane} (hx : x ∈ (coordinateTransition q p).source) :
    phaseDerivative ((centeredConvexPhase ell L c ∘ coordinateChart q) ∘
      (coordinateChart p).symm) x =
      pullCovector (fderiv ℝ (coordinateTransition q p) x)
        (ell+L • (coordinateTransition q p x-c)) := by
  change phaseDerivative (centeredConvexPhase ell L c ∘ coordinateTransition q p) x = _
  exact centered_phaseDerivative_comp
    ((((coordinateTransition_smoothOn q p) x hx).contDiffAt
      ((coordinateTransition q p).open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ell c L

lemma actual_centered_phase_at (q p : M) (ell c : CurvePlane) (L : ℝ) {z : M}
    (hzp : z ∈ (coordinateChart p).source) (hzq : z ∈ (coordinateChart q).source) :
    phaseDerivative ((centeredConvexPhase ell L c ∘ coordinateChart q) ∘
      (coordinateChart p).symm) (coordinateChart p z) =
      pullCovector (fderiv ℝ (coordinateTransition q p) (coordinateChart p z))
        (ell+L • (coordinateChart q z-c)) := by
  rw [actual_centered_phase_differential q p ell c L (coordinateTransition_mem_chart q p hzp hzq),
    coordinateTransition_apply_chart q p hzp]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteCurveTangencies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nondegenerate critical points of a restricted phase are isolated, so
only finitely many lie in a compact boundary arc. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry

lemma finite_compact_simple_zeros {f df : ℝ → ℝ} (hf : Continuous f)
    {K : Set ℝ} (hK : IsCompact K)
    (hd : ∀ t ∈ K, HasDerivAt f (df t) t)
    (hn : ∀ t ∈ K, f t = 0 → df t ≠ 0) :
    (K ∩ {t | f t = 0}).Finite := by
  apply (hK.inter_right (isClosed_eq hf continuous_const)).finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro t ht
  have he : ∀ᶠ s in 𝓝 t, s ≠ t → f s ≠ 0 := by
    simpa only [mem_compl_iff,mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp ((hd t ht.1).eventually_ne (c := 0) (hn t ht.1 ht.2)))
  obtain ⟨U,hsub,hU,htU⟩ := mem_nhds_iff.mp he
  refine ⟨U,hU,?_⟩
  ext s
  constructor
  · rintro ⟨hsU,hsK,hs0⟩
    apply mem_singleton_iff.mpr
    by_contra hst
    exact hsub hsU hst hs0
  · rintro rfl
    exact ⟨htU,ht⟩

lemma curvePhaseVelocity_hasDerivAt {u v w : ℝ → CurvePlane} {L t : ℝ} {ell : CurvePlane}
    (hu : HasDerivAt u (v t) t) (hv : HasDerivAt v (w t) t) :
    HasDerivAt (fun s => curvePhaseVelocity u v L s ell)
      (curvePhaseAcceleration u v w L t ell) t := by
  have hu1 : HasDerivAt (fun s => (u s).1) (v t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hu2 : HasDerivAt (fun s => (u s).2) (v t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hv1 : HasDerivAt (fun s => (v s).1) (w t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hv2 : HasDerivAt (fun s => (v s).2) (w t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hh := (((hu1.const_mul L).const_add ell.1).mul hv1).add
    (((hu2.const_mul L).const_add ell.2).mul hv2)
  refine hh.congr_deriv (Eq.symm ?_)
  · dsimp [curvePhaseAcceleration]
    ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactCurvePhaseParameters
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On compact regular arcs the nondegenerate phase parameters form an
open dense set, suitable for independent choices in a finite product. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry

local instance compactCurveVolumeHaar_r10f131_1 : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _
theorem goodCompactCurvePhases_open (u v w : ℝ → CurvePlane) (L : ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    {K : Set ℝ} (hK : IsCompact K) : IsOpen (goodCompactCurvePhases u v w L K) := by
  rw [isOpen_iff_mem_nhds]
  intro ell hell
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  let F : CurvePlane × ℝ → CurvePlane := fun z =>
    (curvePhaseVelocity u v L z.2 z.1,curvePhaseAcceleration u v w L z.2 z.1)
  have hF : Continuous F := by
    dsimp [F,curvePhaseVelocity,curvePhaseAcceleration]
    fun_prop
  have hne : F (ell,t) ≠ 0 := by
    intro he
    have hv0 : curvePhaseVelocity u v L t ell = 0 := congrArg Prod.fst he
    have ha0 : curvePhaseAcceleration u v w L t ell = 0 := congrArg Prod.snd he
    exact hell t ht hv0 ha0
  filter_upwards [hF.continuousAt.eventually_ne hne] with z hz
  intro hv0 ha0
  apply hz
  exact Prod.ext hv0 ha0

theorem goodCompactCurvePhases_dense
    (u v w : ℝ → CurvePlane) (L : ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hdu : ∀ t, HasDerivAt u (v t) t) (hdv : ∀ t, HasDerivAt v (w t) t)
    (K : Set ℝ) (hregular : ∀ t ∈ K, v t ≠ 0) :
    Dense (goodCompactCurvePhases u v w L K) := by
  have hnull : volume (goodCompactCurvePhases u v w L K)ᶜ = 0 := by
    apply measure_mono_null _ (curve_phase_all_degenerate_parameters_null u v w hu hv hdu hdv L)
    intro ell hell
    change ¬ (∀ t ∈ K, curvePhaseVelocity u v L t ell = 0 →
      curvePhaseAcceleration u v w L t ell ≠ 0) at hell
    push Not at hell
    obtain ⟨t,ht,hcrit,hdeg⟩ := hell
    exact ⟨t,hregular t ht,hcrit,hdeg⟩
  apply Measure.dense_of_ae (μ := (volume : Measure CurvePlane))
  rw [ae_iff]
  exact hnull

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FiniteCriticalQuadraticPhases
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic-parameter statement for the actual quadratic phases used
by the primitive construction, retaining finite tangencies on compact arcs. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry

lemma quadraticPhaseAlongCurve_hasDerivAt {u : ℝ → CurvePlane} {v ell : CurvePlane}
    {L t : ℝ} (hu : HasDerivAt u v t) :
    HasDerivAt (fun s => convexQuadraticPhase ell L (u s))
      ((ell.1+L*(u t).1)*v.1+(ell.2+L*(u t).2)*v.2) t := by
  have hd := (convexQuadraticPhase_hasFDerivAt ell L (u t)).comp_hasDerivAt t hu
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [phaseLinear_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]

lemma quadraticPhaseAlongCurve_deriv (u : ℝ → CurvePlane) (hu : ContDiff ℝ ∞ u)
    (ell : CurvePlane) (L : ℝ) :
    deriv (fun s => convexQuadraticPhase ell L (u s)) =
      fun t => curvePhaseVelocity u (deriv u) L t ell := by
  funext t
  exact (quadraticPhaseAlongCurve_hasDerivAt (ell := ell) (L := L)
    ((hu.differentiable (by simp) t).hasDerivAt)).deriv

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GenericPulledPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic phase selection after the actual invertible chart pullbacks.
The two phase covectors at each crossing are expressed in one tangent chart
before testing their determinant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Countable α] [Countable κ]

theorem exists_generic_pulled_phases
    (index : α → ι) (u : α → ℝ → CurvePlane) (hu : ∀ a, ContDiff ℝ ∞ (u a))
    (K : α → Set ℝ) (hK : ∀ a, IsCompact (K a))
    (hregular : ∀ a t, t ∈ K a → deriv (u a) t ≠ 0) (L : α → ℝ)
    (first second : κ → ι) (hdistinct : ∀ k, first k ≠ second k)
    (A B : κ → CurvePlane →L[ℝ] CurvePlane)
    (hA : ∀ k, RealModes.coordDet (A k) ≠ 0) (hB : ∀ k, RealModes.coordDet (B k) ≠ 0)
    (offset₁ offset₂ : κ → CurvePlane)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U,
      (∀ a, (K a ∩ {t | deriv (fun s =>
        convexQuadraticPhase (ell (index a)) (L a) (u a s)) t = 0}).Finite) ∧
      (∀ a t, t ∈ K a → deriv (fun s =>
        convexQuadraticPhase (ell (index a)) (L a) (u a s)) t = 0 →
          deriv (deriv (fun s =>
            convexQuadraticPhase (ell (index a)) (L a) (u a s))) t ≠ 0) ∧
      (∀ k, covectorDet (RealModes.pullCovector (A k) (ell (first k)+offset₁ k))
        (RealModes.pullCovector (B k) (ell (second k)+offset₂ k)) ≠ 0) := by
  let v := fun a => deriv (u a)
  let w := fun a => deriv (v a)
  have hv : ∀ a, ContDiff ℝ ∞ (v a) := fun a => (contDiff_infty_iff_deriv.mp (hu a)).2
  have hw : ∀ a, ContDiff ℝ ∞ (w a) := fun a => (contDiff_infty_iff_deriv.mp (hv a)).2
  have hdu : ∀ a t, HasDerivAt (u a) (v a t) t := fun a t =>
    ((hu a).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt
  have hdv : ∀ a t, HasDerivAt (v a) (w a t) t := fun a t =>
    ((hv a).differentiable (by simp) t).hasDerivAt
  let O : Sum α κ → Set (ι → CurvePlane)
    | .inl a => (fun ell => ell (index a)) ⁻¹'
        goodCompactCurvePhases (u a) (v a) (w a) (L a) (K a)
    | .inr k => {ell | covectorDet (RealModes.pullCovector (A k) (ell (first k)+offset₁ k))
        (RealModes.pullCovector (B k) (ell (second k)+offset₂ k)) ≠ 0}
  have ho : ∀ s, IsOpen (O s) := by
    intro s
    cases s with
    | inl a =>
        exact (goodCompactCurvePhases_open (u a) (v a) (w a) (L a)
        (hu a).continuous (hv a).continuous (hw a).continuous (hK a)).preimage
          (show Continuous (fun ell : ι → CurvePlane => ell (index a)) from continuous_apply (index a))
    | inr k =>
        exact (independent_pulled_covectors_open_dense (hdistinct k) (A k) (B k)
          (hA k) (hB k) (offset₁ k) (offset₂ k)).1
  have hd : ∀ s, Dense (O s) := by
    intro s
    cases s with
    | inl a =>
        exact (goodCompactCurvePhases_dense (u a) (v a) (w a) (L a)
        (hu a) (hv a) (hdu a) (hdv a) (K a) (hregular a)).preimage
          ((ContinuousLinearMap.proj (index a) : (ι → CurvePlane) →L[ℝ] CurvePlane).isOpenMap
            (phaseProjection_surjective (index a)))
    | inr k =>
        exact (independent_pulled_covectors_open_dense (hdistinct k) (A k) (B k)
          (hA k) (hB k) (offset₁ k) (offset₂ k)).2
  obtain ⟨ell,hell,he⟩ := (dense_iInter_of_isOpen ho hd).inter_open_nonempty U hU hne
  have hn (a : α) : ∀ t ∈ K a, curvePhaseVelocity (u a) (v a) (L a) t (ell (index a)) = 0 →
      curvePhaseAcceleration (u a) (v a) (w a) (L a) t (ell (index a)) ≠ 0 :=
    mem_iInter.mp he (Sum.inl a)
  have hfirst (a : α) := quadraticPhaseAlongCurve_deriv (u a) (hu a) (ell (index a)) (L a)
  have hsecond (a : α) : deriv (deriv (fun s =>
      convexQuadraticPhase (ell (index a)) (L a) (u a s))) =
      fun t => curvePhaseAcceleration (u a) (v a) (w a) (L a) t (ell (index a)) := by
    rw [hfirst]
    funext t
    exact (curvePhaseVelocity_hasDerivAt (L := L a) (ell := ell (index a))
      (hdu a t) (hdv a t)).deriv
  refine ⟨ell,hell,?_,?_,?_⟩
  · intro a
    rw [hfirst]
    exact finite_compact_simple_zeros
      (df := fun t => curvePhaseAcceleration (u a) (v a) (w a) (L a) t (ell (index a)))
      (by
        have huc := (hu a).continuous
        have hvc : Continuous (deriv (u a)) := (hv a).continuous
        dsimp [curvePhaseVelocity]
        fun_prop) (hK a)
      (fun t _ => curvePhaseVelocity_hasDerivAt (hdu a t) (hdv a t)) (hn a)
  · intro a t ht hc
    rw [hsecond]
    apply hn a t ht
    simpa only [hfirst] using hc
  · intro k
    exact mem_iInter.mp he (Sum.inr k)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GenericAtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic centered phases in different surface charts. At crossing points
both differentials are pulled to the same actual tangent chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Countable α] [Countable κ]

theorem exists_generic_atlas_phases
    (center : ι → M) (L : ι → ℝ) (index : α → ι)
    (u : α → ℝ → CurvePlane) (hu : ∀ a, ContDiff ℝ ∞ (u a))
    (K : α → Set ℝ) (hK : ∀ a, IsCompact (K a))
    (hregular : ∀ a t, t ∈ K a → deriv (u a) t ≠ 0)
    (first second : κ → ι) (hdistinct : ∀ k, first k ≠ second k)
    (base point : κ → M)
    (hbase : ∀ k, point k ∈ (coordinateChart (base k)).source)
    (hfirst : ∀ k, point k ∈ (coordinateChart (center (first k))).source)
    (hsecond : ∀ k, point k ∈ (coordinateChart (center (second k))).source)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U,
      (∀ a, (K a ∩ {t | deriv (fun s =>
        centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s)) t = 0}).Finite) ∧
      (∀ a t, t ∈ K a → deriv (fun s =>
        centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s)) t = 0 →
        deriv (deriv (fun s => centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s))) t ≠ 0) ∧
      (∀ k, covectorDet
        (phaseDerivative (centeredAtlasPhase (center (first k)) (ell (first k)) (L (first k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k)))
        (phaseDerivative (centeredAtlasPhase (center (second k)) (ell (second k)) (L (second k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k))) ≠ 0) := by
  let c : ι → CurvePlane := fun i => coordinateChart (center i) (center i)
  let A : κ → CurvePlane →L[ℝ] CurvePlane := fun k =>
    fderiv ℝ (coordinateTransition (center (first k)) (base k)) (coordinateChart (base k) (point k))
  let B : κ → CurvePlane →L[ℝ] CurvePlane := fun k =>
    fderiv ℝ (coordinateTransition (center (second k)) (base k)) (coordinateChart (base k) (point k))
  have hA (k : κ) : coordDet (A k) ≠ 0 := coordinateTransition_det_ne _ _
    (coordinateTransition_mem_chart _ _ (hbase k) (hfirst k))
  have hB (k : κ) : coordDet (B k) ≠ 0 := coordinateTransition_det_ne _ _
    (coordinateTransition_mem_chart _ _ (hbase k) (hsecond k))
  have hur (a : α) : ContDiff ℝ ∞ (fun t => u a t-c (index a)) := (hu a).sub contDiff_const
  have hr : ∀ a t, t ∈ K a → deriv (fun t => u a t-c (index a)) t ≠ 0 := by
    intro a t ht
    simpa only [deriv_sub_const] using hregular a t ht
  obtain ⟨ell,hell,he,hn,hcross⟩ := exists_generic_pulled_phases index
    (fun a t => u a t-c (index a)) hur K hK hr (fun a => L (index a))
    first second hdistinct A B hA hB
    (fun k => L (first k) • (coordinateChart (center (first k)) (point k)-c (first k)))
    (fun k => L (second k) • (coordinateChart (center (second k)) (point k)-c (second k))) U hU hne
  refine ⟨ell,hell,he,hn,?_⟩
  intro k
  simp only [centeredAtlasPhase]
  rw [actual_centered_phase_at _ _ _ _ _ (hbase k) (hfirst k),
    actual_centered_phase_at _ _ _ _ _ (hbase k) (hsecond k)]
  exact hcross k

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactRegularParameters
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact-chart regular-value conditions are open as well as dense.
This permits independent radius parameters in a finite product. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

theorem compact_regular_values_open_dense (f : Plane → Plane)
    (hf : ContDiff ℝ ∞ f) {K : Set Plane} (hK : IsCompact K) :
    IsOpen (compactRegularValues f K) ∧ Dense (compactRegularValues f K) := by
  let C : Set Plane := {x | ¬ Function.Surjective (fderiv ℝ f x)}
  have heq : C = {x | (fderiv ℝ f x).det = 0} := by
    ext x
    change (¬ Function.Surjective (fderiv ℝ f x)) ↔
      LinearMap.det (fderiv ℝ f x).toLinearMap = 0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    exact not_congr LinearMap.injective_iff_surjective.symm
  have hC : IsClosed C := by
    rw [heq]
    exact isClosed_eq (ContinuousLinearMap.continuous_det.comp
      (hf.continuous_fderiv (by simp))) continuous_const
  have hbad : IsCompact (f '' (K ∩ C)) := (hK.inter_right hC).image hf.continuous
  have hvalues : compactRegularValues f K = (f '' (K ∩ C))ᶜ := by
    ext y
    simp only [compactRegularValues,mem_ofPred_eq,mem_compl_iff,mem_image,mem_inter_iff,C]
    constructor
    · intro hy ⟨x,⟨hx,hc⟩,hxy⟩
      exact hc (hy x hx hxy)
    · intro hy x hx hxy
      by_contra hc
      exact hy ⟨x,⟨hx,hc⟩,hxy⟩
  rw [hvalues]
  refine ⟨hbad.isClosed.isOpen_compl,?_⟩
  have hnull : volume (f '' (K ∩ C)) = 0 :=
    measure_mono_null (image_mono inter_subset_right) (sardSurfaceInput f hf)
  apply Measure.dense_of_ae (μ := (volume : Measure Plane))
  simpa only [ae_iff,mem_compl_iff,not_not,Set.ofPred_mem_eq] using hnull

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GenericRadiusParameters
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous independent radius selection. Pair projections avoid
critical values and triple projections avoid surface images in three
coordinates, within every allowed open parameter box. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι κ : Type*} [Countable ι] [Countable κ]

theorem exists_generic_radius_parameters
    (pair : ι → E →L[ℝ] Plane) (hpair : ∀ i, Function.Surjective (pair i))
    (triple : κ → E →L[ℝ] (Plane × ℝ)) (htriple : ∀ j, Function.Surjective (triple j))
    (f : ι → Plane → Plane) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (K : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (g : κ → Plane → Plane × ℝ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (L : κ → Set Plane) (hL : ∀ j, IsCompact (L j))
    (U : Set E) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ t ∈ U,
      (∀ i x, x ∈ K i → f i x = pair i t → Function.Surjective (fderiv ℝ (f i) x)) ∧
      (∀ i, (K i ∩ {x | f i x = pair i t}).Finite) ∧
      ∀ j x, x ∈ L j → g j x ≠ triple j t := by
  let O : Sum ι κ → Set E
    | .inl i => (pair i) ⁻¹' compactRegularValues (f i) (K i)
    | .inr j => (triple j) ⁻¹' (g j '' L j)ᶜ
  have ho : ∀ a, IsOpen (O a) := by
    intro a
    cases a with
    | inl i =>
        exact (compact_regular_values_open_dense (f i) (hf i) (hK i)).1.preimage
          (pair i).continuous
    | inr j =>
        exact (compact_surface_image_open_dense (g j) (hg j) (hL j)).1.preimage
          (triple j).continuous
  have hd : ∀ a, Dense (O a) := by
    intro a
    cases a with
    | inl i =>
        exact (compact_regular_values_open_dense (f i) (hf i) (hK i)).2.preimage
          ((pair i).isOpenMap (hpair i))
    | inr j =>
        exact (compact_surface_image_open_dense (g j) (hg j) (hL j)).2.preimage
          ((triple j).isOpenMap (htriple j))
  obtain ⟨t,htU,ht⟩ := (dense_iInter_of_isOpen ho hd).inter_open_nonempty U hU hne
  have hreg (i : ι) : ∀ x ∈ K i, f i x = pair i t →
      Function.Surjective (fderiv ℝ (f i) x) := mem_iInter.mp ht (Sum.inl i)
  refine ⟨t,htU,hreg,fun i => finite_compact_regular_fiber (hf i) (hK i) _ (hreg i),?_⟩
  intro j x hx he
  have hn : triple j t ∉ g j '' L j := mem_iInter.mp ht (Sum.inr j)
  exact hn ⟨x,hx,he⟩

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentRadiusProjections
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pair and triple projections used for independently perturbed disk
radii are actual surjective bounded linear maps. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PublishedInputs
variable {ι : Type*} [DecidableEq ι]

lemma radiusPairProjection_surjective {i j : ι} (hij : i ≠ j) :
    Function.Surjective (radiusPairProjection i j) := by
  intro y
  refine ⟨Function.update (Function.update (fun _ => 0) i (y 0)) j (y 1),?_⟩
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).injective
  funext a
  fin_cases a
  · simp [hij]
  · simp

lemma radiusTripleProjection_surjective {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Surjective (radiusTripleProjection i j k) := by
  intro y
  refine ⟨Function.update
    (Function.update (Function.update (fun _ => 0) i (y.1 0)) j (y.1 1)) k y.2,?_⟩
  apply Prod.ext
  · change radiusPairProjection i j _ = y.1
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).injective
    funext a
    fin_cases a
    · simp [hij,hik]
    · simp [hjk]
  · simp [radiusTripleProjection]

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GenericCoordinateLevels
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic common levels for finitely many radius functions in countably
many surface charts. This is the radius-selection step of the global preparation. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Countable α]

theorem exists_generic_coordinate_levels
    (ρ : α → ι → Plane → ℝ) (hρ : ∀ a i, ContDiff ℝ ∞ (ρ a i))
    (K : α → Set Plane) (hK : ∀ a, IsCompact (K a))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ r ∈ U,
      (∀ a i j, i ≠ j → ∀ x ∈ K a,
        ρ a i x = r i → ρ a j x = r j →
        Function.Surjective (fderiv ℝ (fun y =>
          radiusPairProjection i j (fun k => ρ a k y)) x)) ∧
      (∀ a i j, i ≠ j → (K a ∩ {x | ρ a i x = r i ∧ ρ a j x = r j}).Finite) ∧
      ∀ a i j k, i ≠ j → i ≠ k → j ≠ k → ∀ x ∈ K a,
        ¬ (ρ a i x = r i ∧ ρ a j x = r j ∧ ρ a k x = r k) := by
  let p : α × DistinctRadiusPairs ι → (ι → ℝ) →L[ℝ] Plane :=
    fun a => radiusPairProjection a.2.1.1 a.2.1.2
  let q : α × DistinctRadiusTriples ι → (ι → ℝ) →L[ℝ] (Plane × ℝ) :=
    fun a => radiusTripleProjection a.2.1.1.1 a.2.1.1.2 a.2.1.2
  let f : α × DistinctRadiusPairs ι → Plane → Plane :=
    fun a x => p a (fun k => ρ a.1 k x)
  let g : α × DistinctRadiusTriples ι → Plane → Plane × ℝ :=
    fun a x => q a (fun k => ρ a.1 k x)
  have hf : ∀ a, ContDiff ℝ ∞ (f a) := fun a =>
    (p a).contDiff.comp (contDiff_pi.mpr (hρ a.1))
  have hg : ∀ a, ContDiff ℝ ∞ (g a) := fun a =>
    (q a).contDiff.comp (contDiff_pi.mpr (hρ a.1))
  obtain ⟨r,hr,hreg,hfinite,htriple⟩ := exists_generic_radius_parameters p
    (fun a => radiusPairProjection_surjective a.2.2) q
    (fun a => radiusTripleProjection_surjective a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    f hf (fun a => K a.1) (fun a => hK a.1)
    g hg (fun a => K a.1) (fun a => hK a.1) U hU hne
  have hpairEq (a : α) (i j : ι) (hij : i ≠ j) (x : Plane) :
      f (a,⟨(i,j),hij⟩) x = p (a,⟨(i,j),hij⟩) r ↔
        ρ a i x = r i ∧ ρ a j x = r j := by
    constructor
    · intro he
      exact ⟨congrArg (fun z : Plane => z 0) he,congrArg (fun z : Plane => z 1) he⟩
    · rintro ⟨hi,hj⟩
      apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).injective
      funext b
      fin_cases b
      · exact hi
      · exact hj
  refine ⟨r,hr,?_,?_,?_⟩
  · intro a i j hij x hx hi hj
    exact hreg (a,⟨(i,j),hij⟩) x hx ((hpairEq a i j hij x).mpr ⟨hi,hj⟩)
  · intro a i j hij
    exact (hfinite (a,⟨(i,j),hij⟩)).subset (fun x hx =>
      ⟨hx.1,(hpairEq a i j hij x).mpr hx.2⟩)
  · intro a i j k hij hik hjk x hx he
    apply htriple (a,⟨((i,j),k),hij,hik,hjk⟩) x hx
    apply Prod.ext
    · exact (hpairEq a i j hij x).mpr ⟨he.1,he.2.1⟩
    · exact he.2.2

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFlatBump
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat cutoffs for the actual circular disks in primitive preparation.
Their centers and radii are smooth parameters. -/
noncomputable section
open Set Function Filter
open scoped Topology
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma circularRadiusSquared_smooth (c : Base) :
    ContDiff ℝ ∞ (circularRadiusSquared c) := by
  unfold circularRadiusSquared
  fun_prop

lemma circularFlatBump_joint_smooth :
    ContDiff ℝ ∞ (fun z : (Base × ℝ) × Base => circularFlatBump z.1.1 z.1.2 z.2) := by
  apply expNegInvGlue.contDiff.comp
  unfold circularRadiusSquared
  fun_prop

lemma circularFlatBump_smooth (c : Base) (r : ℝ) :
    ContDiff ℝ ∞ (circularFlatBump c r) := by
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (circularRadiusSquared_smooth c))

lemma circularFlatBump_nonneg (c : Base) (r : ℝ) (p : Base) :
    0 ≤ circularFlatBump c r p := expNegInvGlue.nonneg _

lemma circularFlatBump_zero_iff (c : Base) (r : ℝ) (p : Base) :
    circularFlatBump c r p = 0 ↔ r^2 ≤ circularRadiusSquared c p := by
  simp only [circularFlatBump, expNegInvGlue.zero_iff_nonpos, sub_nonpos]

lemma circularFlatBump_pos_iff (c : Base) (r : ℝ) (p : Base) :
    0 < circularFlatBump c r p ↔ circularRadiusSquared c p < r^2 := by
  constructor
  · intro hp
    apply lt_of_not_ge
    intro hge
    exact (ne_of_gt hp) ((circularFlatBump_zero_iff c r p).mpr hge)
  · intro hp
    exact expNegInvGlue.pos_of_pos (sub_pos.mpr hp)

lemma circularRadiusSquared_le_norm {c p : Base} {r : ℝ}
    (hp : circularRadiusSquared c p ≤ r^2) : ‖p-c‖ ≤ |r| := by
  have h₁ : |p.1-c.1| ≤ |r| := by
    apply sq_le_sq.mp
    unfold circularRadiusSquared at hp
    nlinarith [sq_nonneg (p.2-c.2)]
  have h₂ : |p.2-c.2| ≤ |r| := by
    apply sq_le_sq.mp
    unfold circularRadiusSquared at hp
    nlinarith [sq_nonneg (p.1-c.1)]
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, max_le_iff]
    using And.intro h₁ h₂

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CircularSmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite smoothing atlas whose positive loci are actual coordinate disks.
The cutoffs are flat circular functions, not arbitrary subordinate bumps. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma circularCoordinateRegion_compact (p : M) (r : ℝ) :
    IsCompact (circularCoordinateRegion p r) := by
  apply (isCompact_closedBall (coordinateChart p p) |r|).of_isClosed_subset
    (isClosed_le (circularRadiusSquared_smooth _).continuous continuous_const)
  intro x hx
  rw [Metric.mem_closedBall,dist_eq_norm]
  exact circularRadiusSquared_le_norm hx

lemma circularManifoldBump_nonneg (p x : M) (r : ℝ) :
    0 ≤ circularManifoldBump p r x := by
  classical
  by_cases hx : x ∈ (coordinateChart p).source
  · rw [circularManifoldBump,indicator_of_mem hx]
    exact circularFlatBump_nonneg _ _ _
  · rw [circularManifoldBump,indicator_of_notMem hx]

lemma circularManifoldBump_pos_iff (p x : M) (r : ℝ) :
    0 < circularManifoldBump p r x ↔ x ∈ circularCoordinateDisk p r := by
  classical
  by_cases hx : x ∈ (coordinateChart p).source
  · simp only [circularManifoldBump,indicator_of_mem hx,circularCoordinateDisk,
      mem_inter_iff,hx,true_and,mem_preimage,Set.mem_ofPred_eq,circularFlatBump_pos_iff]
  · simp only [circularManifoldBump,indicator_of_notMem hx,circularCoordinateDisk,
      mem_inter_iff,hx,false_and,lt_self_iff_false]

variable [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_open (p : M) (r : ℝ) :
    IsOpen (circularCoordinateDisk p r) := by
  exact (coordinateChart p).continuousOn.isOpen_inter_preimage
    (coordinateChart p).open_source
    (isOpen_lt (circularRadiusSquared_smooth _).continuous continuous_const)

variable [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_compact (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsCompact (circularDiskClosure p r) :=
  (circularCoordinateRegion_compact p r).image_of_continuousOn
    ((coordinateChart p).continuousOn_symm.mono hregion)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_source (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    circularDiskClosure p r ⊆ (coordinateChart p).source := by
  rintro x ⟨y,hy,rfl⟩
  exact (coordinateChart p).map_target (hregion hy)

lemma circularManifoldBump_smooth_support (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (circularManifoldBump p r) ∧
      tsupport (circularManifoldBump p r) ⊆ circularDiskClosure p r := by
  apply contMDiff_indicator_of_support (coordinateChart p).open_source
    (circularDiskClosure_compact p r hregion).isClosed
    (circularDiskClosure_source p r hregion)
    ((circularFlatBump_smooth _ r).contMDiff.comp_contMDiffOn (coordinateChart_smoothOn p))
  intro x hx hnot
  apply (circularFlatBump_zero_iff _ r _).mpr
  by_contra hlt
  apply hnot
  refine ⟨coordinateChart p x,?_,(coordinateChart p).left_inv hx⟩
  exact (not_le.mp hlt).le

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PerturbedCircularCutoffs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual independent radius perturbations of circular manifold cutoffs.
A fixed larger disk supplies common support and uniform continuity. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularCoordinateRegion_mono (p : M) {r R : ℝ} (h : r^2 ≤ R^2) :
    circularCoordinateRegion p r ⊆ circularCoordinateRegion p R := by
  intro x hx
  exact hx.trans h

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_mono (p : M) {r R : ℝ} (h : r^2 ≤ R^2) :
    circularDiskClosure p r ⊆ circularDiskClosure p R :=
  image_mono (circularCoordinateRegion_mono p h)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ShrinkingCircularWeight
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight-preserving independent disk shrinkage. The quotient is only
used where the original bump is positive; the smaller compact support
makes the resulting weight globally smooth. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularManifoldBump_mono_sq (p x : M) {r R : ℝ} (h : r^2 ≤ R^2) :
    circularManifoldBump p r x ≤ circularManifoldBump p R x := by
  classical
  by_cases hx : x ∈ (coordinateChart p).source
  · simp only [circularManifoldBump,indicator_of_mem hx,circularFlatBump]
    exact expNegInvGlue.monotone (sub_le_sub_right h _)
  · simp only [circularManifoldBump,indicator_of_notMem hx,le_refl]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_subset_disk (p : M) {r R : ℝ} (h : r^2 < R^2)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    circularDiskClosure p r ⊆ circularCoordinateDisk p R := by
  rintro x ⟨y,hy,rfl⟩
  refine ⟨(coordinateChart p).map_target (hreg hy),?_⟩
  change circularRadiusSquared (coordinateChart p p)
    (coordinateChart p ((coordinateChart p).symm y)) < R^2
  rw [(coordinateChart p).right_inv (hreg hy)]
  exact hy.trans_lt h

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_nonneg_le (p : M) (w : M → ℝ)
    (hw : ∀ x, 0 ≤ w x) {r0 r : ℝ} (hr : r^2 ≤ r0^2) (x : M) :
    0 ≤ shrinkingCircularWeight p w r0 r x ∧ shrinkingCircularWeight p w r0 r x ≤ w x := by
  have hb := circularManifoldBump_mono_sq p x hr
  have hn := circularManifoldBump_nonneg p x r
  have hd := circularManifoldBump_nonneg p x r0
  refine ⟨mul_nonneg (hw x) (div_nonneg hn hd),?_⟩
  by_cases hp : 0 < circularManifoldBump p r0 x
  · exact mul_le_of_le_one_right (hw x) ((div_le_one hp).mpr hb)
  · have hz : circularManifoldBump p r0 x = 0 := le_antisymm (not_lt.mp hp) hd
    simpa only [shrinkingCircularWeight,hz,div_zero,mul_zero] using hw x

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_reference (p : M) (w : M → ℝ) (r0 : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hpos : ∀ x, 0 < w x ↔ x ∈ circularCoordinateDisk p r0) :
    shrinkingCircularWeight p w r0 r0 = w := by
  funext x
  by_cases hb : circularManifoldBump p r0 x = 0
  · have hz : w x = 0 := le_antisymm (le_of_not_gt (fun hp =>
      ((circularManifoldBump_pos_iff p x r0).mpr ((hpos x).mp hp)).ne' hb)) (hw x)
    simp only [shrinkingCircularWeight,hz,zero_mul]
  · simp only [shrinkingCircularWeight,div_self hb,mul_one]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_pos_iff (p : M) (w : M → ℝ)
    (_hw : ∀ x, 0 ≤ w x) {r0 r : ℝ} (hr : r^2 ≤ r0^2)
    (hpos : ∀ x, 0 < w x ↔ x ∈ circularCoordinateDisk p r0) (x : M) :
    0 < shrinkingCircularWeight p w r0 r x ↔ x ∈ circularCoordinateDisk p r := by
  constructor
  · intro h
    apply (circularManifoldBump_pos_iff p x r).mp
    apply lt_of_le_of_ne (circularManifoldBump_nonneg p x r)
    intro hb
    have hz : shrinkingCircularWeight p w r0 r x = 0 := by
      simp only [shrinkingCircularWeight,← hb,zero_div,mul_zero]
    exact h.ne' hz
  · intro hx
    have hb := (circularManifoldBump_pos_iff p x r).mpr hx
    have hb0 := hb.trans_le (circularManifoldBump_mono_sq p x hr)
    have hw0 := (hpos x).mpr ((circularManifoldBump_pos_iff p x r0).mp hb0)
    exact mul_pos hw0 (div_pos hb hb0)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_support (p : M) (w : M → ℝ) (r0 r : ℝ) :
    tsupport (shrinkingCircularWeight p w r0 r) ⊆ tsupport (circularManifoldBump p r) := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  simp only [shrinkingCircularWeight,hx,zero_div,mul_zero]

/-- Every strictly smaller radius gives a globally smooth actual weight,
with support in the smaller closed disk. -/
theorem shrinkingCircularWeight_smooth (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) {r0 r : ℝ}
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hr : r^2 < r0^2) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (shrinkingCircularWeight p w r0 r) ∧
      tsupport (shrinkingCircularWeight p w r0 r) ⊆ circularDiskClosure p r := by
  have hreg := (circularCoordinateRegion_mono p hr.le).trans hreg0
  have hb := circularManifoldBump_smooth_support p r hreg
  have hb0 := circularManifoldBump_smooth_support p r0 hreg0
  have hs := (shrinkingCircularWeight_support p w r0 r).trans hb.2
  refine ⟨?_,hs⟩
  apply contMDiff_of_tsupport
  intro x hx
  have hd := (circularDiskClosure_subset_disk p hr hreg) (hs hx)
  have hp := (circularManifoldBump_pos_iff p x r0).mpr hd
  exact (hw x).mul ((hb.1 x).div₀ (hb0.1 x) hp.ne')

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ShrinkingWeightContinuity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform convergence of the actual ratio cutoffs from smaller radii.
The upper clamp permits an ordinary product-neighborhood argument at the
original radius, including the boundary where numerator and denominator vanish. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularManifoldBump_joint_continuousAt_of_source (p : M) (r : ℝ) {x : M}
    (hx : x ∈ (coordinateChart p).source) :
    ContinuousAt (fun z : ℝ × M => circularManifoldBump p z.1 z.2) (r,x) := by
  classical
  have hc := ((coordinateChart p).continuousOn.continuousAt
    ((coordinateChart p).open_source.mem_nhds hx)).comp (x := (r,x))
      continuous_snd.continuousAt
  have hg : ContinuousAt (fun z : ℝ × M =>
      ((coordinateChart p p,z.1),coordinateChart p z.2)) (r,x) :=
    (continuousAt_const.prodMk continuous_fst.continuousAt).prodMk hc
  have hf := circularFlatBump_joint_smooth.continuous.continuousAt.comp (x := (r,x)) hg
  apply hf.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually
    ((coordinateChart p).open_source.mem_nhds hx)] with z hz
  exact indicator_of_mem hz _

lemma shrinkingRadius_bounds {r0 : ℝ} (hr0 : 0 ≤ r0) (r : ℝ) :
    0 ≤ shrinkingRadius r0 r ∧ shrinkingRadius r0 r ≤ r0 := by
  exact ⟨le_max_left _ _,max_le hr0 (min_le_left _ _)⟩

lemma shrinkingRadius_of_mem {r0 r : ℝ} (hr : 0 ≤ r) (hr0 : r ≤ r0) :
    shrinkingRadius r0 r = r := by
  simp only [shrinkingRadius,min_eq_right hr0,max_eq_right hr]

lemma shrinkingRadius_continuous (r0 : ℝ) : Continuous (shrinkingRadius r0) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Joint continuity remains valid at a vanishing denominator, because the
ratio cutoff lies between zero and the original continuous weight. -/
theorem shrinkingCircularWeight_joint_continuousAt_reference (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) (hnon : ∀ x, 0 ≤ w x) {r0 : ℝ}
    (hr0 : 0 < r0)
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hpos : ∀ x, 0 < w x ↔ x ∈ circularCoordinateDisk p r0) (x : M) :
    ContinuousAt (fun z : ℝ × M =>
      shrinkingCircularWeight p w r0 (shrinkingRadius r0 z.1) z.2) (r0,x) := by
  have hclip := shrinkingRadius_of_mem hr0.le (le_refl r0)
  have href := congrFun (shrinkingCircularWeight_reference p w r0 hnon hpos) x
  have hb := (circularManifoldBump_smooth_support p r0 hreg0).1.continuous
  by_cases hp : 0 < circularManifoldBump p r0 x
  · have hx := ((circularManifoldBump_pos_iff p x r0).mp hp).1
    have hc : ContinuousAt (fun z : ℝ × M => (shrinkingRadius r0 z.1,z.2)) (r0,x) :=
      (((shrinkingRadius_continuous r0).comp continuous_fst).prodMk continuous_snd).continuousAt
    have ho : ContinuousAt (fun z : ℝ × M => circularManifoldBump p z.1 z.2)
        (shrinkingRadius r0 r0,x) := by
      rw [hclip]
      exact circularManifoldBump_joint_continuousAt_of_source p r0 hx
    have hn := ho.comp (x := (r0,x)) hc
    exact (hw.continuous.comp continuous_snd).continuousAt.mul
      (hn.div (hb.comp continuous_snd).continuousAt hp.ne')
  · have hz : w x = 0 := le_antisymm (le_of_not_gt (fun hwx => hp
      ((circularManifoldBump_pos_iff p x r0).mpr ((hpos x).mp hwx)))) (hnon x)
    have hu : Tendsto (fun z : ℝ × M => w z.2) (𝓝 (r0,x)) (𝓝 0) := by
      have hc : ContinuousAt (fun z : ℝ × M => w z.2) (r0,x) :=
        (hw.continuous.comp continuous_snd).continuousAt
      change Tendsto (fun z : ℝ × M => w z.2) (𝓝 (r0,x)) (𝓝 (w x)) at hc
      rw [hz] at hc
      exact hc
    have hs : Tendsto (fun z : ℝ × M =>
        shrinkingCircularWeight p w r0 (shrinkingRadius r0 z.1) z.2)
        (𝓝 (r0,x)) (𝓝 0) := by
      apply tendsto_const_nhds.squeeze hu
      · intro z
        have hc := shrinkingRadius_bounds hr0.le z.1
        exact (shrinkingCircularWeight_nonneg_le p w hnon
          (show (shrinkingRadius r0 z.1)^2 ≤ r0^2 by nlinarith) z.2).1
      · intro z
        have hc := shrinkingRadius_bounds hr0.le z.1
        exact (shrinkingCircularWeight_nonneg_le p w hnon
          (show (shrinkingRadius r0 z.1)^2 ≤ r0^2 by nlinarith) z.2).2
    simpa only [ContinuousAt,hclip,href,hz] using hs

variable [CompactSpace M]

/-- Independent smaller radii can be chosen in one left neighborhood while
preserving the weight uniformly on the entire compact manifold. -/
theorem shrinkingCircularWeight_uniform_perturbation (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) (hnon : ∀ x, 0 ≤ w x) {r0 : ℝ}
    (hr0 : 0 < r0)
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hpos : ∀ x, 0 < w x ↔ x ∈ circularCoordinateDisk p r0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ r0 / 2 ∧ ∀ r : ℝ,
      r0-delta < r → r < r0 →
      ContMDiff planeModel 𝓘(ℝ) ∞ (shrinkingCircularWeight p w r0 r) ∧
      (∀ x, 0 < shrinkingCircularWeight p w r0 r x ↔ x ∈ circularCoordinateDisk p r) ∧
      tsupport (shrinkingCircularWeight p w r0 r) ⊆ circularDiskClosure p r ∧
      ∀ x, |shrinkingCircularWeight p w r0 r x-w x| < eps := by
  have hv : ∀ᶠ r in 𝓝 r0, ∀ x : M,
      |shrinkingCircularWeight p w r0 (shrinkingRadius r0 r) x-w x| < eps := by
    have hv' : ∀ᶠ r in 𝓝 r0, ∀ x ∈ (univ : Set M),
        |shrinkingCircularWeight p w r0 (shrinkingRadius r0 r) x-w x| < eps := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro x _
      have hc := ((shrinkingCircularWeight_joint_continuousAt_reference
        p w hw hnon hr0 hreg0 hpos x).sub
        (hw.continuous.comp continuous_snd).continuousAt).abs
      have hz : |shrinkingCircularWeight p w r0 (shrinkingRadius r0 r0) x-w x| < eps := by
        rw [shrinkingRadius_of_mem hr0.le le_rfl,
          shrinkingCircularWeight_reference p w r0 hnon hpos,sub_self,abs_zero]
        exact heps
      exact hc.eventually (gt_mem_nhds hz)
    exact hv'.mono (fun r hh x => hh x (mem_univ x))
  obtain ⟨d,hd,hnear⟩ := Metric.eventually_nhds_iff.mp hv
  refine ⟨min d (r0/2),lt_min hd (half_pos hr0),min_le_right _ _,?_⟩
  intro r hr hrmax
  have hrpos : 0 < r := by have := min_le_right d (r0/2); linarith
  have hs : r^2 < r0^2 := by nlinarith
  have hsm := shrinkingCircularWeight_smooth p w hw hreg0 hs
  refine ⟨hsm.1,shrinkingCircularWeight_pos_iff p w hnon hs.le hpos,hsm.2,?_⟩
  have habs : |r-r0| < d := by
    rw [abs_of_neg (sub_neg.mpr hrmax)]
    have := min_le_left d (r0/2)
    linarith
  simpa only [shrinkingRadius_of_mem hrpos.le hrmax.le] using
    hnear (y := r) (by simpa only [Real.dist_eq] using habs)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_IndependentShrinkingWeights
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One open box of independent radius choices preserves a finite family of
actual circular weights uniformly. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
variable {ι : Type*} [Fintype ι]

/-- The radius neighborhood is fixed before all independent choices. -/
theorem independent_shrinking_weights (p : ι → M) (w : ι → M → ℝ) (r0 : ι → ℝ)
    (hw : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (w i))
    (hnon : ∀ i x, 0 ≤ w i x) (hr0 : ∀ i, 0 < r0 i)
    (hreg : ∀ i, circularCoordinateRegion (p i) (r0 i) ⊆ (coordinateChart (p i)).target)
    (hpos : ∀ i x, 0 < w i x ↔ x ∈ circularCoordinateDisk (p i) (r0 i))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ (∀ i, delta ≤ r0 i / 2) ∧ ∀ r : ι → ℝ,
      (∀ i, r0 i-delta < r i ∧ r i < r0 i) →
      (∀ i, 0 < r i) ∧
      (∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (shrinkingCircularWeight (p i) (w i) (r0 i) (r i))) ∧
      (∀ i x, 0 < shrinkingCircularWeight (p i) (w i) (r0 i) (r i) x ↔
        x ∈ circularCoordinateDisk (p i) (r i)) ∧
      (∀ i, tsupport (shrinkingCircularWeight (p i) (w i) (r0 i) (r i)) ⊆
        circularDiskClosure (p i) (r i)) ∧
      (∀ i x, |shrinkingCircularWeight (p i) (w i) (r0 i) (r i) x-w i x| < eps) := by
  classical
  choose d hd hdR hnear using fun i => shrinkingCircularWeight_uniform_perturbation
    (p i) (w i) (hw i) (hnon i) (hr0 i) (hreg i) (hpos i) heps
  obtain ⟨delta,hdelta,_,hsmall⟩ := finite_positive_threshold d hd
  refine ⟨delta,hdelta,(fun i => (hsmall i).trans (hdR i)),?_⟩
  intro r hr
  have hri (i : ι) : r0 i-d i < r i := by
    have := hsmall i
    linarith [(hr i).1]
  have hres (i : ι) := hnear i (r i) (hri i) (hr i).2
  refine ⟨?_,fun i => (hres i).1,fun i => (hres i).2.1,
    fun i => (hres i).2.2.1,fun i => (hres i).2.2.2⟩
  intro i
  linarith [hdR i,hr0 i,hri i]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LocalGenericAtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase selection on compact portions of local boundary arcs. Smooth
extension supplies the global parameter argument without imposing global
chart-domain assumptions on an arc. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Countable α] [Countable κ]

theorem exists_generic_atlas_phases_on
    (center : ι → M) (L : ι → ℝ) (index : α → ι)
    (u : α → ℝ → CurvePlane) (V : α → Set ℝ) (hV : ∀ a, IsOpen (V a))
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) (V a))
    (K : α → Set ℝ) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (hregular : ∀ a t, t ∈ K a → deriv (u a) t ≠ 0)
    (first second : κ → ι) (hdistinct : ∀ k, first k ≠ second k)
    (base point : κ → M)
    (hbase : ∀ k, point k ∈ (coordinateChart (base k)).source)
    (hfirst : ∀ k, point k ∈ (coordinateChart (center (first k))).source)
    (hsecond : ∀ k, point k ∈ (coordinateChart (center (second k))).source)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U,
      (∀ a, (K a ∩ {t | deriv (fun s =>
        centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s)) t = 0}).Finite) ∧
      (∀ a t, t ∈ K a → deriv (fun s =>
        centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s)) t = 0 →
        deriv (deriv (fun s => centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s))) t ≠ 0) ∧
      (∀ k, covectorDet
        (phaseDerivative (centeredAtlasPhase (center (first k)) (ell (first k)) (L (first k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k)))
        (phaseDerivative (centeredAtlasPhase (center (second k)) (ell (second k)) (L (second k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k))) ≠ 0) := by
  choose W hW hKW hWV v hv he using fun a =>
    CollarVelocity.compact_smooth_extension (hK a) (hV a) (hKV a) (hu a)
  have hsame (a : α) (t : ℝ) (ht : t ∈ K a) : v a =ᶠ[𝓝 t] u a := by
    filter_upwards [(hW a).mem_nhds (hKW a ht)] with s hs
    exact he a hs
  have hreg : ∀ a t, t ∈ K a → deriv (v a) t ≠ 0 := by
    intro a t ht
    rw [(hsame a t ht).deriv_eq]
    exact hregular a t ht
  obtain ⟨ell,hell,hfinite,hn,hcross⟩ := exists_generic_atlas_phases center L index
    v hv K hK hreg first second hdistinct base point hbase hfirst hsecond U hU hne
  let phi (a : α) : CurvePlane → ℝ := centeredConvexPhase (ell (index a)) (L (index a))
    (coordinateChart (center (index a)) (center (index a)))
  have hc (a : α) (t : ℝ) (ht : t ∈ K a) :
      (fun s => phi a (v a s)) =ᶠ[𝓝 t] (fun s => phi a (u a s)) :=
    (hsame a t ht).fun_comp (phi a)
  refine ⟨ell,hell,?_,?_,hcross⟩
  · intro a
    apply (hfinite a).subset
    rintro t ⟨ht,hzero⟩
    exact ⟨ht,(hc a t ht).deriv_eq.trans hzero⟩
  · intro a t ht hzero
    change deriv (deriv (fun s => phi a (u a s))) t ≠ 0
    rw [← (hc a t ht).deriv.deriv_eq]
    apply hn a t ht
    exact (hc a t ht).deriv_eq.trans hzero

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ShrinkingWeightMultiplier
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth multiplier for a whole compact range of smaller radii.
This removes the apparent moving denominator from all derivative estimates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

/-- The ratio-cutoff family is multiplication by one fixed smooth function
on every smaller radius box. Constants for that multiplier are chosen before
any radius in the box. -/
theorem exists_shrinkingWeight_multiplier (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) {r0 R : ℝ}
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hR : R^2 < r0^2) :
    ∃ a : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ a ∧
      tsupport a ⊆ circularCoordinateDisk p r0 ∧
      ∀ r : ℝ, r^2 ≤ R^2 → shrinkingCircularWeight p w r0 r =
        fun x => a x * circularManifoldBump p r x := by
  have hreg := (circularCoordinateRegion_mono p hR.le).trans hreg0
  have hK := circularDiskClosure_compact p R hreg
  have hKO := circularDiskClosure_subset_disk p hR hreg
  obtain ⟨B,hB,hKB,hBc⟩ := hK.exists_isOpen_closure_subset
    ((circularCoordinateDisk_open p r0).mem_nhdsSet.mpr hKO)
  obtain ⟨chi,hchi,_,hsupp,hchiK⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
      hB hK.isClosed hKB
  let a : M → ℝ := fun x => chi x * (w x / circularManifoldBump p r0 x)
  have haS : tsupport a ⊆ circularCoordinateDisk p r0 := by
    apply Subset.trans (b := tsupport chi)
    · apply closure_mono
      intro x hx hzero
      exact hx (by simp only [a,hzero,zero_mul])
    · change closure (Function.support chi) ⊆ _
      rw [hsupp]
      exact hBc
  have ha : ContMDiff planeModel 𝓘(ℝ) ∞ a := by
    apply contMDiff_of_tsupport
    intro x hx
    have hp := (circularManifoldBump_pos_iff p x r0).mpr (haS hx)
    exact (hchi x).mul ((hw x).div₀
      ((circularManifoldBump_smooth_support p r0 hreg0).1 x) hp.ne')
  refine ⟨a,ha,haS,?_⟩
  intro r hr
  funext x
  by_cases hz : circularManifoldBump p r x = 0
  · simp only [shrinkingCircularWeight,hz,zero_div,mul_zero]
  · have hreg' := (circularCoordinateRegion_mono p hr).trans hreg
    have hx := (circularManifoldBump_smooth_support p r hreg').2 (subset_tsupport _ hz)
    have hchi1 := (hchiK x).mp (circularDiskClosure_mono p hr hx)
    simp only [a,hchi1,one_mul,shrinkingCircularWeight]
    ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ShrinkingWeightBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-order coordinate bounds for the actual radius family. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry WeightedEstimates

private lemma compact_parameter_slice_bounds {F : ℝ × SmallModes.Base → ℝ}
    (hF : ContDiff ℝ ∞ F) {K : Set ℝ} {Q : Set SmallModes.Base}
    (hK : IsCompact K) (hQ : IsCompact Q)
    (hs : ∀ r ∈ K, tsupport (fun x => F (r,x)) ⊆ Q) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ K,
      WeightedBound univ 1 m C (fun x => F (r,x)) := by
  obtain ⟨C,hC,hbound⟩ := compact_coefficient_bound uniqueDiffOn_univ
    (hK.prod hQ) (subset_univ _) hF.contDiffOn m
  refine ⟨C,zero_le_one.trans hC,?_⟩
  intro r hr j hj x _
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ]
  by_cases hx : x ∈ Q
  · let L : SmallModes.Base →L[ℝ] ℝ × SmallModes.Base := ContinuousLinearMap.inr ℝ ℝ SmallModes.Base
    let G : ℝ × SmallModes.Base → ℝ := fun y => F (y+(r,0))
    have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_id.add contDiff_const)
    have he : (fun x => F (r,x)) = G ∘ L := by
      funext y
      simp only [G,L,Function.comp_apply,ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk,zero_add,add_zero]
    rw [he,L.iteratedFDeriv_comp_right hG x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
    have hn := (iteratedFDeriv ℝ j G (L x)).norm_compContinuousLinearMap_le
      (fun _ : Fin j => L)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
    have hder : iteratedFDeriv ℝ j G (L x) = iteratedFDeriv ℝ j F (r,x) := by
      simpa only [G,L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,zero_add,add_zero]
        using iteratedFDeriv_comp_add_right j (r,0) (L x) (f := F)
    rw [hder] at hn
    have hbase : ‖iteratedFDeriv ℝ j F (r,x)‖ ≤ C := by
      simpa only [iteratedFDerivWithin_univ] using hbound j hj (r,x) ⟨hr,hx⟩
    rw [hder]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j F (r,x)‖ * ‖L‖^j := hn
      _ ≤ C * 1 := mul_le_mul hbase
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ ℝ SmallModes.Base))
        (pow_nonneg (norm_nonneg _) _) (zero_le_one.trans hC)
      _ = C := mul_one C
  · have hzero : iteratedFDeriv ℝ j (fun x => F (r,x)) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hh => hx (hs r hr (tsupport_iteratedFDeriv_subset j hh))
    simp only [hzero,norm_zero]
    exact zero_le_one.trans hC

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

/-- One globally smooth coordinate multiplier represents all smaller ratio
weights; its product with the circular bump has uniform finite-order bounds. -/
theorem shrinkingWeight_coordinate_bounds (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) {r0 R : ℝ}
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hR : R^2 < r0^2) :
    ∃ a : SmallModes.Base → ℝ, ContDiff ℝ ∞ a ∧
      (∀ r : ℝ, r^2 ≤ R^2 → ∀ x ∈ (coordinateChart p).target,
        shrinkingCircularWeight p w r0 r ((coordinateChart p).symm x) =
          a x * circularFlatBump (coordinateChart p p) r x) ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ r : ℝ, r^2 ≤ R^2 →
        ∀ m, WeightedBound univ 1 m (C m)
          (fun x => a x * circularFlatBump (coordinateChart p p) r x) := by
  obtain ⟨b,hb,hbs,hbeq⟩ := exists_shrinkingWeight_multiplier p w hw hreg0 hR
  have hreg := (circularCoordinateRegion_mono p hR.le).trans hreg0
  have hlocal : ContDiffOn ℝ ∞ (fun x => b ((coordinateChart p).symm x))
      (coordinateChart p).target := by
    exact (hb.comp_contMDiffOn (coordinateChart_symm_smoothOn p)).contDiffOn
  obtain ⟨U,hU,hKU,_,a,ha,heq⟩ := CollarVelocity.compact_smooth_extension
    (circularCoordinateRegion_compact p R) (coordinateChart p).open_target hreg hlocal
  let F : ℝ × SmallModes.Base → ℝ := fun z => a z.2 *
    circularFlatBump (coordinateChart p p) z.1 z.2
  have hF : ContDiff ℝ ∞ F := (ha.comp contDiff_snd).mul
    (circularFlatBump_joint_smooth.comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd))
  have hs (r : ℝ) (hr : r ∈ Icc (-|R|) |R|) :
      tsupport (fun x => F (r,x)) ⊆ circularCoordinateRegion p R := by
    have hr2 : r^2 ≤ R^2 := by
      have h := (sq_le_sq₀ (abs_nonneg r) (abs_nonneg R)).2 (abs_le.mpr hr)
      simpa only [sq_abs] using h
    apply closure_minimal _ (isClosed_le (circularRadiusSquared_smooth _).continuous continuous_const)
    intro x hx
    by_contra hxQ
    have hzero := (circularFlatBump_zero_iff (coordinateChart p p) r x).mpr
      (hr2.trans (le_of_not_ge hxQ))
    exact hx (by simp only [F,hzero,mul_zero])
  choose C hC hbound using fun m => compact_parameter_slice_bounds hF
    (isCompact_Icc : IsCompact (Icc (-|R|) |R|))
    (circularCoordinateRegion_compact p R) hs m
  refine ⟨a,ha,?_,C,hC,?_⟩
  · intro r hr x hx
    rw [congrFun (hbeq r hr) ((coordinateChart p).symm x)]
    have hsx := (coordinateChart p).map_target hx
    simp only [circularManifoldBump,indicator_of_mem hsx,
      (coordinateChart p).right_inv hx]
    by_cases hmem : x ∈ circularCoordinateRegion p R
    · rw [heq (hKU hmem)]
    · have hz := (circularFlatBump_zero_iff (coordinateChart p p) r x).mpr
        (hr.trans (le_of_not_ge hmem))
      simp only [hz,mul_zero]
  · intro r hr m
    have habs : |r| ≤ |R| := (sq_le_sq₀ (abs_nonneg r) (abs_nonneg R)).1
      (by simpa only [sq_abs] using hr)
    exact hbound m r (abs_le.mp habs)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ShrinkingAtlasWeightBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas bounds for an entire compact box of actual smaller-radius weights. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry weightedBound_comp_isometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- All finite derivative bounds are fixed before selecting the new radius. -/
theorem shrinking_weight_atlas_bounds (i : A.centers) {r0 R : ℝ}
    (hreg0 : circularCoordinateRegion (i : M) r0 ⊆ (coordinateChart (i : M)).target)
    (hR : R^2 < r0^2) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ r : ℝ, r^2 ≤ R^2 →
      ∀ m, A.WeightedBound 1 m (C m) (shrinkingCircularWeight (i : M) (A.weight i) r0 r) := by
  classical
  obtain ⟨a,ha,heq,B,hB,hbound⟩ := shrinkingWeight_coordinate_bounds
    (i : M) (A.weight i) (A.weight_smooth i) hreg0 hR
  let f : ℝ → SmallModes.Base → ℝ := fun r x =>
    a x * circularFlatBump (coordinateChart (i : M) (i : M)) r x
  have hf (r : ℝ) : ContDiff ℝ ∞ (f r) :=
    ha.mul (circularFlatBump_smooth _ r)
  have hrestore (r : ℝ) (hr : r^2 ≤ R^2) :
      shrinkingCircularWeight (i : M) (A.weight i) r0 r =
        restore (i : M) (A.outer i) (f r ∘ planeCoordinateIsometry) := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).source
    · have hx' : x ∈ (coordinateChart (i : M)).source := by
        simpa only [coordinateChart_source,chart_source] using hx
      have hval := heq r hr (coordinateChart (i : M) x)
        ((coordinateChart (i : M)).map_source hx')
      rw [(coordinateChart (i : M)).left_inv hx'] at hval
      have hval' : shrinkingCircularWeight (i : M) (A.weight i) r0 r x =
          f r (planeCoordinateIsometry (chart (i : M) x)) := hval
      rw [restore,indicator_of_mem hx,Function.comp_apply,← hval']
      by_cases hz : A.weight i x = 0
      · simp only [shrinkingCircularWeight,hz,zero_mul,smul_zero]
      · rw [A.outer_one i x (subset_tsupport _ hz),one_smul]
    · have hw : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hx (A.weight_support i hh))
      simp only [restore,indicator_of_notMem hx,shrinkingCircularWeight,hw,zero_mul]
  choose D hD hlocal using fun m j => A.pair_weighted_bound (V := ℝ) j i m
  refine ⟨fun m => (∑ j : A.centers, D m j)*B m,?_,?_⟩
  · intro m
    exact mul_nonneg (Finset.sum_nonneg (fun j _ => hD m j)) (hB m)
  · intro r hr m j
    rw [hrestore r hr]
    exact (hlocal m j (f r ∘ planeCoordinateIsometry) 1 (B m) zero_lt_one le_rfl (hB m) ( (hf r).comp planeCoordinateIsometry.contDiff)
      (weightedBound_comp_isometry planeCoordinateIsometry (hf r) (hbound r hr m))).mono_const (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD m k) (Finset.mem_univ j)) (hB m))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryParam
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit regular parametrizations of the actual coordinate circles.
The compact parameter interval covers the whole boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma circularParam_hasDerivAt (c : CurvePlane) (r t : ℝ) :
    HasDerivAt (circularParam c r) (circularVelocity r t) t := by
  have h := ((Real.hasDerivAt_cos t).const_mul r |>.const_add c.1).prodMk
    ((Real.hasDerivAt_sin t).const_mul r |>.const_add c.2)
  have he : circularVelocity r t = (r*(-Real.sin t),r*Real.cos t) := by
    simp only [circularVelocity, mul_neg, neg_mul]
  rw [he]
  exact h

lemma circularVelocity_ne_zero {r : ℝ} (hr : r ≠ 0) (t : ℝ) : circularVelocity r t ≠ 0 := by
  intro he
  have hs : Real.sin t = 0 := (mul_eq_zero.mp (congrArg Prod.fst he)).resolve_left (neg_ne_zero.mpr hr)
  have hc : Real.cos t = 0 := (mul_eq_zero.mp (congrArg Prod.snd he)).resolve_left hr
  have h := Real.sin_sq_add_cos_sq t
  simp [hs,hc] at h

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothCircularRadius
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth global radius field agrees with the actual squared coordinate
radius near every strictly smaller disk boundary. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma circularRadiusField_smooth (i : A.centers) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.circularRadiusField i) :=
  restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    ((circularRadiusSquared_smooth _).comp planeCoordinateIsometry.contDiff)

lemma circularRadiusField_germ (i : A.centers) {p : M} (hp : A.weight i p ≠ 0) :
    A.circularRadiusField i =ᶠ[𝓝 p]
      (fun x => circularRadiusSquared (coordinateChart (i : M) (i : M)) (coordinateChart (i : M) x)) := by
  have hs : p ∈ (chart (i : M)).source := A.weight_support i (subset_tsupport _ hp)
  filter_upwards [(chart (i : M)).open_source.mem_nhds hs,
    A.outer_eventually_one_of_weight_ne_zero i hp] with x hx ho
  simp only [circularRadiusField,restore,indicator_of_mem hx,ho,one_smul,Function.comp_apply]
  rfl

lemma circularBoundary_weight_pos (i : A.centers) {r r0 : ℝ}
    (hsmall : r^2 < r0^2)
    (hpos : ∀ x, 0 < A.weight i x ↔ x ∈ circularCoordinateDisk (i : M) r0)
    {p : M} (hp : p ∈ circularBoundary (i : M) r) : 0 < A.weight i p := by
  apply (hpos p).mpr
  exact ⟨hp.1,by change circularRadiusSquared _ _ < r0^2; rw [hp.2]; exact hsmall⟩

lemma circularBoundary_radiusField (i : A.centers) {r r0 : ℝ}
    (hsmall : r^2 < r0^2)
    (hpos : ∀ x, 0 < A.weight i x ↔ x ∈ circularCoordinateDisk (i : M) r0)
    {p : M} (hp : p ∈ circularBoundary (i : M) r) :
    A.circularRadiusField i p = r^2 := by
  rw [(A.circularRadiusField_germ i (A.circularBoundary_weight_pos i hsmall hpos hp).ne').eq_of_nhds]
  exact hp.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentRadiusBox
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed open radius box with uniform bounds for every independent
choice. The box and its derivative constants precede all later cycle counts. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
variable {ι : Type*} [Fintype ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- All radii may be varied independently inside the displayed nonempty
open box. The actual weights remain uniformly close to their reference and
have one common finite-order atlas bound. -/
theorem independent_radius_box (index : ι → A.centers) (r0 : ι → ℝ)
    (hnon : ∀ a x, 0 ≤ A.weight (index a) x) (hr0 : ∀ a, 0 < r0 a)
    (hreg : ∀ a, circularCoordinateRegion (index a : M) (r0 a) ⊆
      (coordinateChart (index a : M)).target)
    (hpos : ∀ a x, 0 < A.weight (index a) x ↔
      x ∈ circularCoordinateDisk (index a : M) (r0 a))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (delta : ℝ) (C : ℕ → ℝ), 0 < delta ∧ (∀ a, delta ≤ r0 a/2) ∧
      (∀ m, 0 ≤ C m) ∧ ∀ r : ι → ℝ,
      (∀ a, r0 a-delta < r a ∧ r a < r0 a-delta/2) →
      (∀ a, 0 < r a) ∧
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞
        (shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a))) ∧
      (∀ a x, 0 < shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a) x ↔
        x ∈ circularCoordinateDisk (index a : M) (r a)) ∧
      (∀ a, tsupport (shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a)) ⊆
        circularDiskClosure (index a : M) (r a)) ∧
      (∀ a x, |shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a) x-
        A.weight (index a) x| < eps) ∧
      ∀ a m, A.WeightedBound 1 m (C m)
        (shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a)) := by
  classical
  obtain ⟨delta,hdelta,hdeltaR,hnear⟩ := independent_shrinking_weights
    (fun a => (index a : M)) (fun a => A.weight (index a)) r0
    (fun a => A.weight_smooth (index a)) hnon hr0 hreg hpos heps
  have hR (a : ι) : (r0 a-delta/2)^2 < (r0 a)^2 := by
    have := hdeltaR a
    have := hr0 a
    nlinarith
  choose B hB hb using fun a => A.shrinking_weight_atlas_bounds (index a) (hreg a) (hR a)
  refine ⟨delta,fun m => ∑ a : ι, B a m,hdelta,hdeltaR,
    (fun m => Finset.sum_nonneg (fun a _ => hB a m)),?_⟩
  intro r hr
  have hr' : ∀ a, r0 a-delta < r a ∧ r a < r0 a := by
    intro a
    exact ⟨(hr a).1,lt_trans (hr a).2 (by linarith)⟩
  obtain ⟨hrpos,hsmooth,hpositive,hsupport,hclose⟩ := hnear r hr'
  refine ⟨hrpos,hsmooth,hpositive,hsupport,hclose,?_⟩
  intro a m
  have hr2 : (r a)^2 ≤ (r0 a-delta/2)^2 := by
    have := hrpos a
    have := (hr a).2
    nlinarith
  intro i
  exact (hb a (r a) hr2 m i).mono_const
    (Finset.single_le_sum (fun b _ => hB b m) (Finset.mem_univ a))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CurvedAtlasPrimitives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive primitive amplitudes for point-dependent phase bases.
The basis can be the actual nonlinear gradient basis constructed in
`SpatialPhaseBasis`; no constant-phase restriction enters the algebra. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance curvedPrimitiveFiberNormed_r10f131_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance curvedPrimitiveFiberSpace_r10f131_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance curvedPrimitiveDualAdd_r10f131_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance curvedPrimitiveDualSmul_r10f131_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M) (P : A.centers → JetPolynomial.Base → PhaseBasis)
  (u : ∀ p : M, CovariantTwoTensor p)

local instance curvedPrimitiveSectionNormed_r10f131_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance curvedPrimitiveSectionSpace_r10f131_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma curvedAtlasPhase_eventually (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (a : A.centers × Fin 3)
    (houter : ∀ p ∈ tsupport (A.weight a.1), A.outer a.1 =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight a.1)) :
    A.curvedAtlasPhase phi a =ᶠ[𝓝 p] (phi a.1 a.2 ∘ coordinateChart (a.1 : M)) := by
  filter_upwards [houter p hp,
    (chart (a.1 : M)).open_source.mem_nhds (A.weight_support a.1 hp)] with x hx hxs
  rw [curvedAtlasPhase,restore,indicator_of_mem hxs,hx,one_smul]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteBoundaryCrossingSets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact crossing sets for the remaining curves in a finite induction.
The no-three-curves condition keeps these points off the next boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

omit [CompactSpace M] [Fintype ι] in
lemma boundaryCrossingSet_pair (curves : ι → PhaseBoundaryCurve B) {s : Set ι}
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) {p : M}
    (hpi : p ∈ (curves i).carrier) (hpj : p ∈ (curves j).carrier) :
    p ∈ boundaryCrossingSet curves s := ⟨i,hi,j,hj,hij,hpi,hpj⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CircularBoundaryArcs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact boundary portions in another phase chart have actual smooth
regular coordinate arcs, extended later only for parameter selection. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

lemma coordinateTransition_derivative_injective (q p : M) {x : CurvePlane}
    (hx : x ∈ (coordinateTransition q p).source) :
    Function.Injective (fderiv ℝ (coordinateTransition q p) x) := by
  let e := coordinateTransition q p
  have hd := (((coordinateTransition_smoothOn q p) x hx).contDiffAt
    (e.open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hi := (((coordinateTransition_symm_smoothOn q p) (e x) (e.map_source hx)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hc : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ CurvePlane := by
    rw [← fderiv_comp x hi hd,he.fderiv_eq,fderiv_id]
  intro v w hvw
  have hh := congrArg (fderiv ℝ e.symm (e x)) hvw
  change ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) v =
    ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) w at hh
  simpa only [hc,ContinuousLinearMap.id_apply] using hh

end ClosedSurfaceR4.PhaseGeometry
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

lemma circularArcDomain_open (q p : M) {r : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsOpen (circularArcDomain q p r) :=
  (coordinateChart q).open_source.preimage (circularBoundaryParam_smooth p hreg).continuous

lemma circularArc_smooth (q p : M) {r : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    ContDiffOn ℝ ∞ (circularArc q p r) (circularArcDomain q p r) := by
  exact ((coordinateChart_smoothOn q).comp
    (circularBoundaryParam_smooth p hreg).contMDiffOn (fun _ ht => ht)).contDiffOn

lemma circularArc_regular (q p : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    {t : ℝ} (ht : t ∈ circularArcDomain q p r) : deriv (circularArc q p r) t ≠ 0 := by
  let x := circularParam (coordinateChart p p) r t
  have hx : x ∈ (coordinateTransition q p).source := ⟨circularBoundaryParam_target p hreg t,ht⟩
  have hd := ((((coordinateTransition_smoothOn q p) x hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hcurve := hd.comp_hasDerivAt t (circularParam_hasDerivAt (coordinateChart p p) r t)
  have he : circularArc q p r = coordinateTransition q p ∘ circularParam (coordinateChart p p) r := rfl
  rw [he,hcurve.deriv]
  intro hz
  have hinj := coordinateTransition_derivative_injective q p hx
  apply circularVelocity_ne_zero hr.ne' t
  apply hinj
  simpa only [map_zero] using hz

variable [T2Space M]

lemma circularArcCompact_compact (q p : M) {r R : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    (hQ : circularCoordinateRegion q R ⊆ (coordinateChart q).target) :
    IsCompact (circularArcCompact q p r R) :=
  isCompact_Icc.inter_right ((circularDiskClosure_compact q R hQ).isClosed.preimage
    (circularBoundaryParam_smooth p hreg).continuous)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularArcCompact_subset (q p : M) {r R : ℝ}
    (hQ : circularCoordinateRegion q R ⊆ (coordinateChart q).target) :
    circularArcCompact q p r R ⊆ circularArcDomain q p r := by
  intro t ht
  exact circularDiskClosure_source q R hQ ht.2

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularArcCompact_covers (q p : M) {r R : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    {x : M} (hx : x ∈ circularBoundary p r ∩ circularDiskClosure q R) :
    ∃ t ∈ circularArcCompact q p r R, circularBoundaryParam p r t = x := by
  rw [circularBoundary_image p hr hreg] at hx
  obtain ⟨t,ht,he⟩ := hx.1
  exact ⟨t,⟨ht,by simpa only [mem_preimage,he] using hx.2⟩,he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryTangencies
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives along the explicit circle equal evaluation of the actual
phase covector on its nonzero angular tangent. Compact parameter finiteness
therefore gives finiteness of the genuine surface tangency set. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

lemma circularAngularTangent_param (c : CurvePlane) (r t : ℝ) :
    circularAngularTangent c (circularParam c r t) = circularVelocity r t := by
  ext <;> dsimp [circularAngularTangent,circularParam,circularVelocity] <;> ring

lemma circularPhaseDerivative_eq_deriv (q p : M) (ell : CurvePlane) (L : ℝ) {r t : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    (ht : t ∈ circularArcDomain q p r) :
    circularPhaseDerivative q p ell L (circularBoundaryParam p r t) =
      deriv (fun s => centeredAtlasPhase q ell L (circularBoundaryParam p r s)) t := by
  let x := circularParam (coordinateChart p p) r t
  let f : CurvePlane → ℝ := centeredAtlasPhase q ell L ∘ (coordinateChart p).symm
  have hx : x ∈ (coordinateTransition q p).source := ⟨circularBoundaryParam_target p hreg t,ht⟩
  have hf : DifferentiableAt ℝ f x :=
    ((centeredConvexPhase_smooth ell L (coordinateChart q q)).differentiable (by simp) _).comp x
      ((((coordinateTransition_smoothOn q p) x hx).contDiffAt
        ((coordinateTransition q p).open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hd := hf.hasFDerivAt.comp_hasDerivAt t (circularParam_hasDerivAt (coordinateChart p p) r t)
  have he : (fun s => centeredAtlasPhase q ell L (circularBoundaryParam p r s)) =
      f ∘ circularParam (coordinateChart p p) r := rfl
  rw [he,hd.deriv]
  unfold circularPhaseDerivative
  simp only [circularBoundaryParam]
  rw [(coordinateChart p).right_inv (circularBoundaryParam_target p hreg t),
    circularAngularTangent_param,phaseLinear_phaseDerivative]

lemma circularPhaseTangencies_finite (q p : M) (ell : CurvePlane) (L : ℝ) {r R : ℝ}
    (hr : 0 < r) (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    (hQ : circularCoordinateRegion q R ⊆ (coordinateChart q).target)
    (hfinite : (circularArcCompact q p r R ∩ {t |
      deriv (fun s => centeredAtlasPhase q ell L (circularBoundaryParam p r s)) t = 0}).Finite) :
    (circularPhaseTangencies q p ell L r R).Finite := by
  apply (hfinite.image (circularBoundaryParam p r)).subset
  rintro x ⟨⟨hx,hQx⟩,hzero⟩
  obtain ⟨t,ht,rfl⟩ := circularArcCompact_covers q p hr hreg ⟨hx,hQx⟩
  refine ⟨t,⟨ht,?_⟩,rfl⟩
  change deriv (fun s => centeredAtlasPhase q ell L (circularBoundaryParam p r s)) t = 0
  rw [← circularPhaseDerivative_eq_deriv q p ell L hreg
    (circularArcCompact_subset q p hQ ht)]
  exact hzero

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GenericSurfaceLevels
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic levels of actual smooth functions on a closed surface. Finite
chart extensions reduce the selection to the proved Euclidean Sard input;
no coordinate extension or transversality premise is assumed. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_generic_surface_levels (A : SmoothingAtlas M)
    (ρ : ι → M → ℝ) (hρ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ρ i))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ r ∈ U,
      (∀ i j, i ≠ j → {p : M | ρ i p = r i ∧ ρ j p = r j}.Finite) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        ∀ p : M, ¬ (ρ i p = r i ∧ ρ j p = r j ∧ ρ k p = r k)) ∧
      (∀ i j, i ≠ j → ∀ p : M, ρ i p = r i → ρ j p = r j →
        ∃ q : M, p ∈ (chartAt Plane q).source ∧
          Function.Surjective (fderiv ℝ (fun y => radiusPairProjection i j
            (fun k => ρ k ((chartAt Plane q).symm y))) (chartAt Plane q p))) := by
  classical
  let K : A.centers → Set Plane := fun a => (chartAt Plane (a : M)) '' tsupport (A.weight a)
  have hsource (a : A.centers) : tsupport (A.weight a) ⊆ (chartAt Plane (a : M)).source := by
    simpa only [chart_source] using A.weight_support a
  have hK (a : A.centers) : IsCompact (K a) :=
    (isClosed_tsupport (A.weight a)).isCompact.image_of_continuousOn
      ((chartAt Plane (a : M)).continuousOn.mono (hsource a))
  have hKt (a : A.centers) : K a ⊆ (chartAt Plane (a : M)).target := by
    rintro x ⟨p,hp,rfl⟩
    exact (chartAt Plane (a : M)).map_source (hsource a hp)
  have hs (a : A.centers) (i : ι) : ContDiffOn ℝ ∞
      (fun y => ρ i ((chartAt Plane (a : M)).symm y)) (chartAt Plane (a : M)).target :=
    ((hρ i).comp_contMDiffOn (contMDiffOn_chart_symm (I := planeModel) (x := (a : M)))).contDiffOn
  choose W hW hKW hWt f hf he using fun a i =>
    CollarVelocity.compact_smooth_extension (hK a) (chartAt Plane (a : M)).open_target
      (hKt a) (hs a i)
  have hgerm (a : A.centers) (i : ι) {x : Plane} (hx : x ∈ K a) :
      f a i =ᶠ[𝓝 x] (fun y => ρ i ((chartAt Plane (a : M)).symm y)) := by
    filter_upwards [(hW a i).mem_nhds (hKW a i hx)] with y hy
    exact he a i hy
  obtain ⟨r,hr,hreg,hfinite,htriple⟩ := exists_generic_coordinate_levels f hf K hK U hU hne
  have hcover (p : M) : ∃ a : A.centers, p ∈ tsupport (A.weight a) := by
    by_contra hn
    push Not at hn
    have hz : ∀ a : A.centers, A.weight a p = 0 :=
      fun a => image_eq_zero_of_notMem_tsupport (hn a)
    have hh := A.partition p
    simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  have heval (a : A.centers) {p : M} (hp : p ∈ tsupport (A.weight a)) (i : ι) :
      f a i (chartAt Plane (a : M) p) = ρ i p := by
    rw [he a i (hKW a i ⟨p,hp,rfl⟩)]
    change ρ i ((chartAt Plane (a : M)).symm (chartAt Plane (a : M) p)) = ρ i p
    rw [(chartAt Plane (a : M)).left_inv (hsource a hp)]
  refine ⟨r,hr,?_,?_,?_⟩
  · intro i j hij
    have hfin : (⋃ a : A.centers, (chartAt Plane (a : M)).symm ''
        (K a ∩ {x | f a i x = r i ∧ f a j x = r j})).Finite :=
      Set.finite_iUnion (fun a => (hfinite a i j hij).image _)
    apply hfin.subset
    intro p hp
    obtain ⟨a,ha⟩ := hcover p
    exact mem_iUnion.mpr ⟨a,⟨chartAt Plane (a : M) p,
      ⟨⟨p,ha,rfl⟩,by
        change f a i (chartAt Plane (a : M) p) = r i ∧ f a j (chartAt Plane (a : M) p) = r j
        rw [heval a ha i,heval a ha j]
        exact hp⟩,
      (chartAt Plane (a : M)).left_inv (hsource a ha)⟩⟩
  · intro i j k hij hik hjk p hp
    obtain ⟨a,ha⟩ := hcover p
    apply htriple a i j k hij hik hjk (chartAt Plane (a : M) p) ⟨p,ha,rfl⟩
    simpa only [heval a ha i,heval a ha j,heval a ha k] using hp
  · intro i j hij p hi hj
    obtain ⟨a,ha⟩ := hcover p
    let x : Plane := chartAt Plane (a : M) p
    have hx : x ∈ K a := ⟨p,ha,rfl⟩
    have hh := hreg a i j hij x hx
      ((heval a ha i).trans hi) ((heval a ha j).trans hj)
    have heq : (fun y => radiusPairProjection i j (fun k => f a k y)) =ᶠ[𝓝 x]
        (fun y => radiusPairProjection i j (fun k => ρ k ((chartAt Plane (a : M)).symm y))) := by
      have hevery : ∀ᶠ y in 𝓝 x, ∀ k, f a k y = ρ k ((chartAt Plane (a : M)).symm y) :=
        eventually_all.mpr (fun k => hgerm a k hx)
      filter_upwards [hevery] with y hy
      congr 1
      funext k
      exact hy k
    exact ⟨(a : M),hsource a ha,by rw [← heq.fderiv_eq]; exact hh⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularPairCovectors
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular pair of real functions on a surface has independent
coordinate covectors. This is the local form of transverse level curves. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma coordDet_ne_of_surjective (A : CurvePlane →L[ℝ] CurvePlane)
    (hA : Function.Surjective A) : coordDet A ≠ 0 := by
  obtain ⟨x,hx⟩ := hA dx
  obtain ⟨y,hy⟩ := hA dy
  let B : CurvePlane →L[ℝ] CurvePlane :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight x + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight y
  have he : A.comp B = ContinuousLinearMap.id ℝ CurvePlane := by
    apply ContinuousLinearMap.ext
    intro v
    change A (v.1 • x+v.2 • y) = v
    rw [map_add,map_smul,map_smul,hx,hy]
    exact (base_eq_basis v).symm
  have hd := congrArg coordDet he
  rw [coordDet_comp,coordDet_id] at hd
  intro hz
  rw [hz,zero_mul] at hd
  exact zero_ne_one hd

lemma regular_pair_covectors {f g : CurvePlane → ℝ} {x : CurvePlane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hreg : Function.Surjective (fderiv ℝ (fun y => (f y,g y)) x)) :
    covectorDet (phaseDerivative f x) (phaseDerivative g x) ≠ 0 := by
  have h := coordDet_ne_of_surjective _ hreg
  have hd : fderiv ℝ (fun y => (f y,g y)) x = (fderiv ℝ f x).prod (fderiv ℝ g x) :=
    (hf.hasFDerivAt.prodMk hg.hasFDerivAt).fderiv
  rw [hd] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [coordDet,covectorDet,phaseDerivative]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceRegularPair
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regular-value condition in Euclidean surface charts implies the
nonzero determinant of the actual two covectors in our real coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PublishedInputs PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]
variable {ι : Type*} [Fintype ι]

lemma surface_regular_pair_covectors
    (ρ : ι → M → ℝ) (hρ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ρ i))
    (i j : ι) (q : M) {p : M} (hp : p ∈ (chartAt Plane q).source)
    (hreg : Function.Surjective (fderiv ℝ (fun y => radiusPairProjection i j
      (fun k => ρ k ((chartAt Plane q).symm y))) (chartAt Plane q p))) :
    covectorDet
      (phaseDerivative (ρ i ∘ (coordinateChart q).symm) (coordinateChart q p))
      (phaseDerivative (ρ j ∘ (coordinateChart q).symm) (coordinateChart q p)) ≠ 0 := by
  let x : Plane := chartAt Plane q p
  let z : CurvePlane := coordinateChart q p
  let F : Plane → Plane := fun y => radiusPairProjection i j (fun k => ρ k ((chartAt Plane q).symm y))
  have hx : x ∈ (chartAt Plane q).target := (chartAt Plane q).map_source hp
  have hd (k : ι) : DifferentiableAt ℝ (fun y => ρ k ((chartAt Plane q).symm y)) x :=
    (((hρ k).comp_contMDiffOn (contMDiffOn_chart_symm (I := planeModel) (x := q))).contDiffOn
      x hx).contDiffAt ((chartAt Plane q).open_target.mem_nhds hx) |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hF : DifferentiableAt ℝ F x :=
    (radiusPairProjection i j).differentiableAt.comp x (differentiableAt_pi.mpr hd)
  have hfx : planeCoordinates.symm z = x := by
    change planeCoordinates.symm (planeCoordinates (chartAt Plane q p)) = x
    exact planeCoordinates.symm_apply_apply x
  have heq : (fun y => (ρ i ((coordinateChart q).symm y),ρ j ((coordinateChart q).symm y))) =
      planeCoordinates ∘ F ∘ planeCoordinates.symm := by
    funext y
    apply Prod.ext <;> rfl
  have hFx : HasFDerivAt F (fderiv ℝ F x) (planeCoordinates.symm z) := by
    rw [hfx]
    exact hF.hasFDerivAt
  have hinner := hFx.comp z planeCoordinates.symm.hasFDerivAt
  have hcomp := planeCoordinates.hasFDerivAt.comp z hinner
  have hsurj : Function.Surjective (fderiv ℝ
      (fun y => (ρ i ((coordinateChart q).symm y),ρ j ((coordinateChart q).symm y))) z) := by
    rw [heq,hcomp.fderiv]
    exact planeCoordinates.surjective.comp (hreg.comp planeCoordinates.symm.surjective)
  have hsmall (k : ι) : DifferentiableAt ℝ (ρ k ∘ (coordinateChart q).symm) z := by
    have hk : DifferentiableAt ℝ (fun y => ρ k ((chartAt Plane q).symm y))
        (planeCoordinates.symm z) := by rw [hfx]; exact hd k
    exact hk.comp z planeCoordinates.symm.differentiableAt
  exact regular_pair_covectors (hsmall i) (hsmall j) hsurj

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularRadiusCovectors
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth radius fields used for Sard have exactly the true circle
normal covectors on the new boundaries. Their regular pairs are transverse. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma circularRadiusField_covector (i : A.centers) {r r0 : ℝ}
    (hsmall : r^2 < r0^2)
    (hpos : ∀ x, 0 < A.weight i x ↔ x ∈ circularCoordinateDisk (i : M) r0)
    {p q : M} (hp : p ∈ circularBoundary (i : M) r) (hq : p ∈ (chartAt Plane q).source) :
    phaseDerivative (A.circularRadiusField i ∘ (coordinateChart q).symm) (coordinateChart q p) =
      circularNormalCovector (i : M) q p := by
  have hqs : p ∈ (coordinateChart q).source := by simpa only [coordinateChart_source] using hq
  have ht : Tendsto (coordinateChart q).symm (𝓝 (coordinateChart q p)) (𝓝 p) := by
    simpa only [(coordinateChart q).left_inv hqs] using
      ((coordinateChart q).continuousAt_symm ((coordinateChart q).map_source hqs)).tendsto
  have he := (A.circularRadiusField_germ i
    (A.circularBoundary_weight_pos i hsmall hpos hp).ne').comp_tendsto ht
  unfold phaseDerivative circularNormalCovector
  rw [he.fderiv_eq]
  rfl

variable {ι : Type*} [Fintype ι]

lemma actual_circular_normals_independent
    (index : ι → A.centers) (r r0 : ι → ℝ) (i j : ι)
    (hsmall : ∀ k, (r k)^2 < (r0 k)^2)
    (hpos : ∀ k x, 0 < A.weight (index k) x ↔ x ∈ circularCoordinateDisk (index k : M) (r0 k))
    {p q : M} (hp : p ∈ circularBoundary (index i : M) (r i) ∩
      circularBoundary (index j : M) (r j)) (hq : p ∈ (chartAt Plane q).source)
    (hreg : Function.Surjective (fderiv ℝ (fun y => PublishedInputs.radiusPairProjection i j
      (fun k => A.circularRadiusField (index k) ((chartAt Plane q).symm y))) (chartAt Plane q p))) :
    covectorDet (circularNormalCovector (index i : M) q p)
      (circularNormalCovector (index j : M) q p) ≠ 0 := by
  have hh := surface_regular_pair_covectors (fun k => A.circularRadiusField (index k))
    (fun k => A.circularRadiusField_smooth (index k)) i j q hq hreg
  rw [A.circularRadiusField_covector (index i) (hsmall i) (hpos i) hp.1 hq,
    A.circularRadiusField_covector (index j) (hsmall j) (hpos j) hp.2 hq] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_GenericCircularRadii
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent genuine disk radii can be chosen in every prescribed
positive box, with finite pair crossings and no triple crossings. The
regular-value statement is retained for the actual smooth radius fields. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_generic_circular_radii
    (index : ι → A.centers) (r0 lo hi : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (hlohi : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < r0 i)
    (hpos : ∀ i p, 0 < A.weight (index i) p ↔ p ∈ circularCoordinateDisk (index i : M) (r0 i)) :
    ∃ r : ι → ℝ, (∀ i, lo i < r i ∧ r i < hi i) ∧
      (∀ i j, i ≠ j → (circularBoundary (index i : M) (r i) ∩
        circularBoundary (index j : M) (r j)).Finite) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        circularBoundary (index i : M) (r i) ∩ circularBoundary (index j : M) (r j) ∩
          circularBoundary (index k : M) (r k) = ∅) ∧
      (∀ i j, i ≠ j → ∀ p ∈ circularBoundary (index i : M) (r i) ∩
          circularBoundary (index j : M) (r j),
        ∃ q : M, p ∈ (chartAt Plane q).source ∧
          Function.Surjective (fderiv ℝ (fun y => radiusPairProjection i j
            (fun k => A.circularRadiusField (index k) ((chartAt Plane q).symm y)))
            (chartAt Plane q p))) := by
  let U : Set (ι → ℝ) := {s | ∀ i, (lo i)^2 < s i ∧ s i < (hi i)^2}
  have hU : IsOpen U := by
    have heq : U = ⋂ i, {s : ι → ℝ | (lo i)^2 < s i ∧ s i < (hi i)^2} := by
      ext s
      simp only [mem_iInter,mem_ofPred_eq]
      rfl
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)
  have hUexists : U.Nonempty := by
    refine ⟨fun i => ((lo i)^2+(hi i)^2)/2,?_⟩
    intro i
    have hl := hlo i
    have hh := hlohi i
    constructor <;> nlinarith
  obtain ⟨s,hs,hfinite,htriple,hregular⟩ := exists_generic_surface_levels A
    (fun i => A.circularRadiusField (index i)) (fun i => A.circularRadiusField_smooth (index i))
    U hU hUexists
  let r : ι → ℝ := fun i => Real.sqrt (s i)
  have hspos (i : ι) : 0 < s i := (sq_nonneg (lo i)).trans_lt (hs i).1
  have hrsq (i : ι) : (r i)^2 = s i := Real.sq_sqrt (hspos i).le
  have hrpos (i : ι) : 0 < r i := Real.sqrt_pos.mpr (hspos i)
  have hb (i : ι) : lo i < r i ∧ r i < hi i := by
    have hl := hlo i
    have hh := hlohi i
    have hsq := hrsq i
    have hposr := hrpos i
    have hs' := hs i
    constructor <;> nlinarith
  have hsmall (i : ι) : (r i)^2 < (r0 i)^2 := by
    have h1 := (hb i).2
    have h2 := hhi i
    have h3 := hrpos i
    nlinarith
  have heval (i : ι) {p : M} (hp : p ∈ circularBoundary (index i : M) (r i)) :
      A.circularRadiusField (index i) p = s i :=
    (A.circularBoundary_radiusField (index i) (hsmall i) (hpos i) hp).trans (hrsq i)
  refine ⟨r,hb,?_,?_,?_⟩
  · intro i j hij
    exact (hfinite i j hij).subset (fun p hp => ⟨heval i hp.1,heval j hp.2⟩)
  · intro i j k hij hik hjk
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact htriple i j k hij hik hjk p ⟨heval i hp.1.1,heval j hp.1.2,heval k hp.2⟩
  · intro i j hij p hp
    exact hregular i j hij p (heval i hp.1) (heval j hp.2)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_TransverseCircularRadii
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic radii give transverse actual coordinate circles, not merely
regular levels of their auxiliary global extensions. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_transverse_circular_radii
    (index : ι → A.centers) (r0 lo hi : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (hlohi : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < r0 i)
    (hpos : ∀ i p, 0 < A.weight (index i) p ↔ p ∈ circularCoordinateDisk (index i : M) (r0 i)) :
    ∃ r : ι → ℝ, (∀ i, lo i < r i ∧ r i < hi i) ∧
      (∀ i j, i ≠ j → (circularBoundary (index i : M) (r i) ∩
        circularBoundary (index j : M) (r j)).Finite) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        circularBoundary (index i : M) (r i) ∩ circularBoundary (index j : M) (r j) ∩
          circularBoundary (index k : M) (r k) = ∅) ∧
      (∀ i j, i ≠ j → ∀ p ∈ circularBoundary (index i : M) (r i) ∩
          circularBoundary (index j : M) (r j),
        ∃ q : M, p ∈ (coordinateChart q).source ∧
          covectorDet (circularNormalCovector (index i : M) q p)
            (circularNormalCovector (index j : M) q p) ≠ 0) := by
  obtain ⟨r,hr,hfinite,htriple,hregular⟩ :=
    A.exists_generic_circular_radii index r0 lo hi hlo hlohi hhi hpos
  have hsmall (i : ι) : (r i)^2 < (r0 i)^2 := by
    have h1 := hlo i
    have h2 := hr i
    have h3 := hhi i
    nlinarith
  refine ⟨r,hr,hfinite,htriple,?_⟩
  intro i j hij p hp
  obtain ⟨q,hq,hreg⟩ := hregular i j hij p hp
  exact ⟨q,by simpa only [coordinateChart_source] using hq,
    A.actual_circular_normals_independent index r r0 i j hsmall hpos hp hq hreg⟩

end SmoothingAtlas

omit [IsManifold planeModel ∞ M] [CompactSpace M] [DecidableEq ι] in
lemma circularCrossingSet_finite (center : ι → M) (r : ι → ℝ)
    (hfinite : ∀ i j, i ≠ j → (circularBoundary (center i) (r i) ∩
      circularBoundary (center j) (r j)).Finite) : (circularCrossingSet center r).Finite :=
  Set.finite_iUnion (fun a => hfinite a.1.1 a.1.2 a.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCycleAssembly
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-cycle identities for independently chosen primitive families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance assemblyFiberNormed_r10f131_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance assemblyFiberSpace_r10f131_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance assemblyDualAdd_r10f131_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance assemblyDualSmul_r10f131_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

local instance assemblySectionNormed_r10f131_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance assemblySectionSpace_r10f131_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleAmplitude_square (N : ℕ) (a : ι) (p : M) :
    (d.cycleAmplitude N a p)^2 = (N : ℝ)⁻¹*(d.amplitude a p)^2 := by
  rw [cycleAmplitude,div_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  exact div_eq_inv_mul _ _

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleAmplitude_smooth (N : ℕ) (a : ι) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (d.cycleAmplitude N a) :=
  (d.smoothAmplitude a).div_const _

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleAmplitude_pos_iff {N : ℕ} (hN : 0 < N) (a : ι) (p : M) :
    0 < d.cycleAmplitude N a p ↔ 0 < d.amplitude a p :=
  div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (by exact_mod_cast hN))

end ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteCycleOrder
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered prefixes of a finite sequence of primitive cycles. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem finite_cycle_total_sum {V : Type*} [AddCommMonoid V] {N m : ℕ}
    (T : Fin N → Fin m → V) (u : V) (hsum : ∀ k, ∑ j, T k j = u) :
    (∑ a : Fin (N*m), T a.divNat a.modNat) = N • u := by
  rw [← Equiv.sum_comp finProdFinEquiv,Fintype.sum_prod_type]
  have hinv (k : Fin N) (j : Fin m) :
      (finProdFinEquiv (k,j)).divNat = k ∧ (finProdFinEquiv (k,j)).modNat = j :=
    Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k,j))
  simp_rw [(hinv _ _).1,(hinv _ _).2,hsum]
  simp

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularCycleMetrics
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered prefix metrics of a finite circular family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance flatCycleFiberNormed_r10f131_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance flatCycleFiberSpace_r10f131_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance flatCycleDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace CircularPrimitiveFamily
local instance flatCycleFiberNormed_r10f131_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance flatCycleFiberSpace_r10f131_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance flatCycleDualSmul_r10f131_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {B : SmoothingAtlas M} {N m : ℕ}
    (d : CircularPrimitiveFamily B (Fin (N*m)))
    {u : ∀ p : M, CovariantTwoTensor p}
    (f : Fin N → SmoothPrimitiveFamily (Fin m) u)
    (ha : ∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p)
    (hp : ∀ a, d.phase a = (f a.divNat).phase a.modNat)

include f ha hp

local instance flatCycleSectionNormed_r10f131_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance flatCycleSectionSpace_r10f131_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] [T2Space M] in
lemma flat_cycle_term (a : Fin (N*m)) (p : M) :
    (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p =
      (N : ℝ)⁻¹ • (f a.divNat).term a.modNat p := by
  rw [ha,hp,SmoothPrimitiveFamily.cycleAmplitude_square]
  simp only [SmoothPrimitiveFamily.term,smul_smul]

omit [CompactSpace M] [T2Space M] in
lemma totalTensor_cycle (hN : 0 < N) : d.totalTensor = u := by
  funext p
  change (∑ a, (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p) = u p
  simp_rw [d.flat_cycle_term f ha hp]
  rw [← Finset.smul_sum,finite_cycle_total_sum (fun a b => (f a).term b p) (u p)
    (fun a => (f a).sum_eq p),← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hN)),one_smul]

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_GenericCircularPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic phase choice for the actual finite circular disk family.
Both finiteness of tangencies on the surface and cross-chart covector
nonparallelism follow from the preceding explicit parameter construction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Countable κ]

theorem exists_generic_circular_phases
    (center : ι → M) (L r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hreg : ∀ i, circularCoordinateRegion (center i) (r i) ⊆ (coordinateChart (center i)).target)
    (first second : κ → ι) (hdistinct : ∀ k, first k ≠ second k)
    (base point : κ → M)
    (hbase : ∀ k, point k ∈ (coordinateChart (base k)).source)
    (hfirst : ∀ k, point k ∈ (coordinateChart (center (first k))).source)
    (hsecond : ∀ k, point k ∈ (coordinateChart (center (second k))).source)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U,
      (∀ i j, (circularPhaseTangencies (center i) (center j) (ell i) (L i) (r j) (r i)).Finite) ∧
      (∀ k, covectorDet
        (phaseDerivative (centeredAtlasPhase (center (first k)) (ell (first k)) (L (first k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k)))
        (phaseDerivative (centeredAtlasPhase (center (second k)) (ell (second k)) (L (second k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k))) ≠ 0) := by
  let K : ι × ι → Set ℝ := fun a => circularArcCompact (center a.1) (center a.2) (r a.2) (r a.1)
  let V : ι × ι → Set ℝ := fun a => circularArcDomain (center a.1) (center a.2) (r a.2)
  let u : ι × ι → ℝ → CurvePlane := fun a => circularArc (center a.1) (center a.2) (r a.2)
  have hK (a : ι × ι) : IsCompact (K a) := circularArcCompact_compact _ _ (hreg a.2) (hreg a.1)
  have hV (a : ι × ι) : IsOpen (V a) := circularArcDomain_open _ _ (hreg a.2)
  have hu (a : ι × ι) : ContDiffOn ℝ ∞ (u a) (V a) := circularArc_smooth _ _ (hreg a.2)
  have hKV (a : ι × ι) : K a ⊆ V a := circularArcCompact_subset _ _ (hreg a.1)
  have hv (a : ι × ι) (t : ℝ) (ht : t ∈ K a) : deriv (u a) t ≠ 0 :=
    circularArc_regular _ _ (hr a.2) (hreg a.2) (hKV a ht)
  obtain ⟨ell,hell,hfinite,_,hcross⟩ := exists_generic_atlas_phases_on center L Prod.fst
    u V hV hu K hK hKV hv first second hdistinct base point hbase hfirst hsecond U hU hne
  refine ⟨ell,hell,?_,hcross⟩
  intro i j
  exact circularPhaseTangencies_finite (center i) (center j) (ell i) (L i)
    (hr j) (hreg j) (hreg i) (hfinite (i,j))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteCircularPreparation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric finite preparation: independent radii and linear phase
parts are chosen before the starting immersion is flattened at the finite
crossing set. All statements concern the actual coordinate circles. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_circular_preparation
    (index : ι → A.centers) (r0 lo hi L : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (hlohi : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < r0 i)
    (hpos : ∀ i p, 0 < A.weight (index i) p ↔ p ∈ circularCoordinateDisk (index i : M) (r0 i))
    (hreg : ∀ i, circularCoordinateRegion (index i : M) (r0 i) ⊆
      (coordinateChart (index i : M)).target)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (r : ι → ℝ) (ell : ι → CurvePlane), ell ∈ U ∧
      (∀ i, lo i < r i ∧ r i < hi i) ∧
      (circularCrossingSet (fun i => (index i : M)) r).Finite ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        circularBoundary (index i : M) (r i) ∩ circularBoundary (index j : M) (r j) ∩
          circularBoundary (index k : M) (r k) = ∅) ∧
      (∀ i j, i ≠ j → ∀ p ∈ circularBoundary (index i : M) (r i) ∩
          circularBoundary (index j : M) (r j),
        ∃ q : M, p ∈ (coordinateChart q).source ∧
          covectorDet (circularNormalCovector (index i : M) q p)
            (circularNormalCovector (index j : M) q p) ≠ 0) ∧
      (∀ i j, (circularPhaseTangencies (index i : M) (index j : M)
        (ell i) (L i) (r j) (r i)).Finite) ∧
      (∀ i j, i ≠ j → ∀ p ∈ circularCrossingSet (fun k => (index k : M)) r,
        p ∈ (coordinateChart (index i : M)).source →
        p ∈ (coordinateChart (index j : M)).source →
          covectorDet
            (phaseDerivative (centeredAtlasPhase (index i : M) (ell i) (L i) ∘
              (coordinateChart (index i : M)).symm) (coordinateChart (index i : M) p))
            (phaseDerivative (centeredAtlasPhase (index j : M) (ell j) (L j) ∘
              (coordinateChart (index i : M)).symm) (coordinateChart (index i : M) p)) ≠ 0) := by
  classical
  obtain ⟨r,hr,hpair,htriple,htrans⟩ := A.exists_transverse_circular_radii index r0 lo hi
    hlo hlohi hhi hpos
  let P : Set M := circularCrossingSet (fun i => (index i : M)) r
  have hP : P.Finite := circularCrossingSet_finite _ _ hpair
  let : Fintype P := hP.fintype
  let κ := {a : DistinctRadiusPairs ι × P //
    (a.2 : M) ∈ (coordinateChart (index a.1.1.1 : M)).source ∧
    (a.2 : M) ∈ (coordinateChart (index a.1.1.2 : M)).source}
  let : Fintype κ := Fintype.ofFinite κ
  let first : κ → ι := fun a => a.1.1.1.1
  let second : κ → ι := fun a => a.1.1.1.2
  let point : κ → M := fun a => a.1.2
  let base : κ → M := fun a => (index (first a) : M)
  have hrad (i : ι) : 0 < r i := (hlo i).trans (hr i).1
  have hnew (i : ι) : circularCoordinateRegion (index i : M) (r i) ⊆
      (coordinateChart (index i : M)).target := by
    have hs : (r i)^2 ≤ (r0 i)^2 := by
      have h1 := (hr i).2
      have h2 := hhi i
      have h3 := hrad i
      nlinarith
    intro x hx
    exact hreg i (hx.trans hs)
  obtain ⟨ell,hell,htangent,hcross⟩ := exists_generic_circular_phases
    (fun i => (index i : M)) L r hrad hnew first second (fun a => a.1.1.2)
    base point (fun a => a.2.1) (fun a => a.2.1) (fun a => a.2.2) U hU hne
  refine ⟨r,ell,hell,hr,hP,htriple,htrans,htangent,?_⟩
  intro i j hij p hp hi hj
  let a : κ := ⟨(⟨(i,j),hij⟩,⟨p,hp⟩),hi,hj⟩
  exact hcross a

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CycleCorrectedGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference charts give the generic finite geometry for any number of
cycles without shrinking the admissible chart radii after that number is
chosen. The actual corrected families are then attached to those circles. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleGeometryDualAdd
local instance cycleGeometryFiberNormed_r10f131_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace_r10f131_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualSmul_r10f131_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance cycleGeometrySectionNormed_r10f131_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleGeometrySectionSpace_r10f131_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Use the already selected full-disk reference charts, for arbitrarily many
copies, rather than choosing a new admissible radius after the copy count. -/
theorem finite_copy_geometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι → d.B.centers) (component : ι → Fin 3)
    (lo hi : ι → ℝ) (hlo : ∀ a, 0 < lo a) (hlohi : ∀ a, lo a < hi a)
    (hhi : ∀ a, hi a < d.radius (index a))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ q : CircularFamilyGeometry d.B ι,
      (∀ a, lo a < q.radius a ∧ q.radius a < hi a) ∧
      (∀ a, (q.curves a).index = index a) ∧
      (∀ a, q.outerRadius a = d.radius (index a)) ∧
      (∀ a, q.chartRadius a = d.radius (index a)) ∧
      (∀ a, q.convexPart a = d.L (index a)) ∧
      (∀ a, ‖q.linearPart a-(d.P (index a)).ξ (component a)‖ < eta) ∧
      ∀ a, q.linearPart a ∈ Metric.closedBall ((d.P (index a)).ξ (component a))
        (d.epsilon (index a)) := by
  classical
  let eps : ι → ℝ := fun a => min eta (d.epsilon (index a))
  let U : Set (ι → Base) := {ell | ∀ a, ‖ell a-(d.P (index a)).ξ (component a)‖ < eps a}
  have hU : IsOpen U := by
    simp only [U,ofPred_forall]
    apply isOpen_iInter_of_finite
    intro a
    exact isOpen_lt (((continuous_apply a).sub continuous_const).norm) continuous_const
  have hne : U.Nonempty := by
    refine ⟨fun a => (d.P (index a)).ξ (component a),?_⟩
    intro a
    simpa only [sub_self,norm_zero] using lt_min heta (d.epsilon_pos (index a))
  obtain ⟨r,ell,hell,hr,hcross,htriple,htrans,htangent,hind⟩ :=
    d.B.finite_circular_preparation index (fun a => d.radius (index a)) lo hi
      (fun a => d.L (index a)) hlo hlohi hhi
      (fun a => d.weight_positive (index a)) (fun a => d.region (index a)) U hU hne
  have hball (a : ι) : ell a ∈ Metric.closedBall ((d.P (index a)).ξ (component a))
      (d.epsilon (index a)) := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact ((hell a).trans_le (min_le_right _ _)).le
  choose e he hei hephase hecover using fun a => d.charts (index a) (component a) (ell a) (hball a)
  have hrpos (a : ι) : 0 < r a := (hlo a).trans (hr a).1
  have hrr (a : ι) : r a < d.radius (index a) := (hr a).2.trans (hhi a)
  have hrreg (a : ι) : circularCoordinateRegion (index a : M) (r a) ⊆
      (coordinateChart (index a : M)).target := by
    intro x hx
    change circularRadiusSquared (coordinateChart (index a : M) (index a)) x ≤ (r a)^2 at hx
    exact d.region (index a) (hx.trans (by nlinarith [hrpos a,hrr a]))
  have hcover (a : ι) : ∀ x ∈ circularCoordinateRegion (index a : M) (r a),
      baseEquiv.symm x ∈ (e a).source := by
    intro x hx
    apply hecover a x
    change circularRadiusSquared (coordinateChart (index a : M) (index a)) x ≤ (r a)^2 at hx
    change circularRadiusSquared (coordinateChart (index a : M) (index a)) x ≤ (d.radius (index a))^2
    exact hx.trans (by nlinarith [hrpos a,hrr a])
  let curves : ι → PhaseBoundaryCurve d.B := fun a =>
    d.B.circularPhaseBoundaryCurve (index a) (hrpos a) (by nlinarith [hrpos a,hrr a])
      (d.weight_positive (index a)) (hrreg a) (e a) (he a) (hei a) (hcover a)
  have hcarrier (a : ι) : (curves a).carrier = circularBoundary (index a : M) (r a) := rfl
  have hsub : boundaryCrossingSet curves univ ⊆ circularCrossingSet (fun a => (index a : M)) r := by
    rintro p ⟨a,_,b,_,hab,hpa,hpb⟩
    exact mem_iUnion.mpr ⟨⟨(a,b),hab⟩,⟨hpa,hpb⟩⟩
  let q : CircularFamilyGeometry d.B ι := {
    curves := curves, radius := r, outerRadius := fun a => d.radius (index a),
    chartRadius := fun a => d.radius (index a), linearPart := ell, convexPart := fun a => d.L (index a),
    radius_pos := hrpos, radius_outer := fun a => by nlinarith [hrpos a,hrr a],
    radius_chart := hrr, weight_positive := fun a => d.weight_positive (index a),
    region := hrreg, carrier := hcarrier, cover := hcover, first_coordinate := hephase,
    pair_finite := fun a b hab => hcross.subset (fun _ hp => hsub
      (boundaryCrossingSet_pair curves (mem_univ a) (mem_univ b) hab hp.1 hp.2)),
    triple_empty := htriple, tangencies_finite := htangent,
    independent := fun a b hab p hp hpa hpb => hind a b hab p (hsub hp) hpa hpb }
  exact ⟨q,hr,(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),
    (fun a => (hell a).trans_le (min_le_left _ _)),hball⟩

end ReferenceCircularAtlas

namespace CircularFamilyGeometry
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleGeometryDualAdd
local instance cycleGeometryFiberNormed_r10f131_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace_r10f131_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualSmul_r10f131_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

local instance cycleGeometrySectionNormed_r10f131_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleGeometrySectionSpace_r10f131_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] [T2Space M] in
lemma copiedPhases_germ (q : CircularFamilyGeometry B ι)
    (houter : ∀ i p, p ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (a : ι) {p : M}
    (hp : p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a)) :
    q.copiedPhases a =ᶠ[𝓝 p]
      (fun x => ((q.curves a).phase (chart ((q.curves a).index : M) x)) 0) := by
  have hw : B.weight (q.curves a).index p ≠ 0 := by
    apply ne_of_gt ((q.weight_positive a p).mpr ?_)
    exact ⟨hp.1,hp.2.trans (q.radius_outer a)⟩
  let loc : B.centers → Fin 3 → Base → ℝ := fun i _ =>
    centeredConvexPhase (q.linearPart a) (q.convexPart a) (coordinateChart (i : M) i)
  have hg := B.curvedAtlasPhase_eventually loc ((q.curves a).index,0)
    (houter (q.curves a).index) (subset_tsupport _ hw)
  change q.copiedPhases a =ᶠ[𝓝 p]
    (centeredConvexPhase (q.linearPart a) (q.convexPart a)
      (coordinateChart ((q.curves a).index : M) (q.curves a).index) ∘
        coordinateChart ((q.curves a).index : M)) at hg
  apply hg.trans
  apply Filter.Eventually.of_forall
  intro x
  have hh := q.first_coordinate a (chart ((q.curves a).index : M) x)
  change ((q.curves a).phase (chart ((q.curves a).index : M) x)) 0 = _ at hh
  exact hh.symm

omit [CompactSpace M] [T2Space M] in
/-- Attach cycle amplitudes without changing any selected generic geometry. -/
theorem with_cycle_families {N m : ℕ} (q : CircularFamilyGeometry B (Fin (N*m)))
    {u : ∀ p : M, CovariantTwoTensor p}
    (f : Fin N → SmoothPrimitiveFamily (Fin m) u) (hN : 0 < N)
    (hamp : ∀ k a p, 0 ≤ (f k).amplitude a p)
    (hpos : ∀ a p, 0 < (f a.divNat).amplitude a.modNat p ↔
      p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a))
    (hphase : ∀ a, (f a.divNat).phase a.modNat = q.copiedPhases a)
    (houter : ∀ i p, p ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ D : CircularPrimitiveFamily B (Fin (N*m)),
      D.curves = q.curves ∧ D.radius = q.radius ∧ D.outerRadius = q.outerRadius ∧
      D.chartRadius = q.chartRadius ∧ D.linearPart = q.linearPart ∧ D.convexPart = q.convexPart ∧
      (∀ a p, D.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) ∧
      (∀ a, D.phase a = (f a.divNat).phase a.modNat) ∧ D.totalTensor = u := by
  let amp := fun a : Fin (N*m) => (f a.divNat).cycleAmplitude N a.modNat
  let phi := fun a : Fin (N*m) => (f a.divNat).phase a.modNat
  have ha : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amp a) :=
    fun a => (f a.divNat).cycleAmplitude_smooth N a.modNat
  have hp : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a) :=
    fun a => (f a.divNat).smoothPhase a.modNat
  have hn : ∀ a p, 0 ≤ amp a p := fun a p =>
    div_nonneg (hamp _ _ _) (Real.sqrt_nonneg _)
  have hpos' : ∀ a p, 0 < amp a p ↔
      p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a) := by
    intro a p
    exact ((f a.divNat).cycleAmplitude_pos_iff hN a.modNat p).trans (hpos a p)
  have hg : ∀ a p, p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a) →
      phi a =ᶠ[𝓝 p] (fun x => ((q.curves a).phase (chart ((q.curves a).index : M) x)) 0) := by
    intro a p hpa
    change (f a.divNat).phase a.modNat =ᶠ[𝓝 p] _
    rw [hphase a]
    exact q.copiedPhases_germ houter a hpa
  let D := q.withAmplitudes amp phi ha hp hn hpos' hg
  refine ⟨D,rfl,rfl,rfl,rfl,rfl,rfl,(fun _ _ => rfl),(fun _ => rfl),?_⟩
  exact D.totalTensor_cycle f (fun _ _ => rfl) (fun _ => rfl) hN

end CircularFamilyGeometry

namespace ReferenceCircularAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleGeometryDualAdd
local instance cycleGeometryFiberNormed_r10f131_3 : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace_r10f131_3 : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualSmul_r10f131_3 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance cycleGeometrySectionNormed_r10f131_3 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleGeometrySectionSpace_r10f131_3 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- One radius box and map neighborhood precede every cycle count. The
output retains the actual amplitude formula and fixed cutoff bounds, so
the uniform C1 estimate can be applied without choosing further constants. -/
theorem corrected_cycles_oai {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F))
    {phaseBound weightBound mapBound : ℝ}
    (hphaseBound : 0 < phaseBound) (hweightBound : 0 < weightBound)
    (hmapBound : 0 < mapBound)
    {m : ℕ} (e : Fin m ≃ (d.B.centers × Fin 3)) :
    ∃ (mapTol delta : ℝ) (W : ℕ → ℝ),
      0 < mapTol ∧ mapTol ≤ mapBound ∧ 0 < delta ∧
      (∀ i, delta ≤ d.radius i/2) ∧ (∀ j, 0 ≤ W j) ∧
      ∀ N : ℕ, 0 < N →
      ∃ q : CircularFamilyGeometry d.B (Fin (N*m)),
        (∀ a, (q.curves a).index = (e a.modNat).1) ∧
        (∀ a, q.outerRadius a = d.radius (e a.modNat).1) ∧
        (∀ a, q.chartRadius a = d.radius (e a.modNat).1) ∧
        (∀ a, q.convexPart a = d.L (e a.modNat).1) ∧
        (∀ a, ‖q.linearPart a‖ ≤ ‖(d.P (e a.modNat).1).ξ‖+1) ∧
        (∀ a, ‖q.linearPart a-(d.P (e a.modNat).1).ξ (e a.modNat).2‖ < phaseBound) ∧
        (∀ k b j, d.B.WeightedBound 1 j (W j) (d.cycleWeights e q k b)) ∧
        (∀ k b p, |d.cycleWeights e q k b p-d.B.weight b.1 p| < weightBound) ∧
        ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
          A.WeightedBound 1 1 mapTol (G-F) →
        ∃ (f : Fin N → SmoothPrimitiveFamily (Fin m) (g.inner-inducedTensor (r • G)))
          (D : CircularPrimitiveFamily d.B (Fin (N*m))),
          (∀ k a, (f k).amplitude a = d.B.correctedPrimitiveAmplitude d.basis
            (d.cycleWeights e q k) (d.perturbedPhases (d.cycleLinearParts e q k))
            (g.inner-inducedTensor (r • G)) (e a)) ∧
          (∀ k a, (f k).phase a = d.perturbedPhases (d.cycleLinearParts e q k) (e a)) ∧
          D.curves = q.curves ∧ D.radius = q.radius ∧ D.outerRadius = q.outerRadius ∧
          D.chartRadius = q.chartRadius ∧ D.linearPart = q.linearPart ∧ D.convexPart = q.convexPart ∧
          (∀ a p, D.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) ∧
          (∀ a, D.phase a = (f a.divNat).phase a.modNat) ∧
          D.totalTensor = g.inner-inducedTensor (r • G) := by
  classical
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hcorrect⟩ := d.corrected_smooth_family hF r href
  obtain ⟨delta,W,hdelta,hdeltaR,hW,hweights⟩ := d.B.independent_radius_box
    (fun b : d.B.centers × Fin 3 => b.1) (fun b => d.radius b.1)
    (fun b => d.weight_nonneg b.1) (fun b => d.radius_pos b.1) (fun b => d.region b.1)
    (fun b => d.weight_positive b.1) (lt_min hwt hweightBound)
  refine ⟨min mt mapBound,delta,W,lt_min hmt hmapBound,min_le_right _ _,hdelta,
    (fun i => hdeltaR (i,0)),hW,?_⟩
  intro N hN
  let ind := fun a : Fin (N*m) => (e a.modNat).1
  let cmp := fun a : Fin (N*m) => (e a.modNat).2
  let lo := fun a : Fin (N*m) => d.radius (ind a)-delta
  let hi := fun a : Fin (N*m) => d.radius (ind a)-delta/2
  have hlo (a : Fin (N*m)) : 0 < lo a := by
    have hh := hdeltaR (ind a,cmp a)
    have hp := d.radius_pos (ind a)
    dsimp only [lo]
    linarith
  have hmid (a : Fin (N*m)) : lo a < hi a := by dsimp only [lo,hi] <;> linarith
  have hhi (a : Fin (N*m)) : hi a < d.radius (ind a) := by dsimp only [hi] <;> linarith
  obtain ⟨q,hr,hindex,houter,hchart,hL,hell,hball⟩ :=
    d.finite_copy_geometry ind cmp lo hi hlo hmid hhi (lt_min hpt hphaseBound)
  let copy := fun (k : Fin N) (b : d.B.centers × Fin 3) => finProdFinEquiv (k,e.symm b)
  have hcopy (k : Fin N) (b : d.B.centers × Fin 3) :
      (copy k b).divNat = k ∧ e (copy k b).modNat = b := by
    have hh := Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k,e.symm b))
    exact ⟨hh.1,by rw [hh.2,e.apply_symm_apply]⟩
  have hcopy' (a : Fin (N*m)) : copy a.divNat (e a.modNat) = a := by
    simp only [copy,e.symm_apply_apply]
    exact finProdFinEquiv.apply_symm_apply a
  let rr := fun (k : Fin N) (b : d.B.centers × Fin 3) => q.radius (copy k b)
  let ell := d.cycleLinearParts e q
  let psi := d.cycleWeights e q
  have hrr (k : Fin N) (b : d.B.centers × Fin 3) :
      d.radius b.1-delta < rr k b ∧ rr k b < d.radius b.1-delta/2 := by
    have hh := hr (copy k b)
    simpa only [lo,hi,ind,(hcopy k b).2,rr] using hh
  have hpsi (k : Fin N) := hweights (rr k) (hrr k)
  have hrsmall (k : Fin N) (b : d.B.centers × Fin 3) : (rr k b)^2 < (d.radius b.1)^2 := by
    have hh := hrr k b
    have hp := (hpsi k).1 b
    have hR := d.radius_pos b.1
    nlinarith
  have hnorm (a : Fin (N*m)) : ‖q.linearPart a‖ ≤ ‖(d.P (ind a)).ξ‖+1 :=
    (d.parameters (ind a) (cmp a) (q.linearPart a) (hball a)).2
  refine ⟨q,hindex,houter,hchart,hL,hnorm,
    (fun a => (hell a).trans_le (min_le_right _ _)),
    (fun k => (hpsi k).2.2.2.2.2),
    (fun k b p => ((hpsi k).2.2.2.2.1 b p).trans_le (min_le_right _ _)),?_⟩
  intro G hG hGF
  have hnon (k : Fin N) (b : d.B.centers × Fin 3) (p : M) : 0 ≤ psi k b p :=
    (shrinkingCircularWeight_nonneg_le (b.1 : M) (d.B.weight b.1)
      (d.weight_nonneg b.1) (hrsmall k b).le p).1
  have hsupp (k : Fin N) (b : d.B.centers × Fin 3) :
      tsupport (psi k b) ⊆ tsupport (d.B.weight b.1) := by
    apply closure_mono
    intro p hp
    change psi k b p ≠ 0 at hp
    change d.B.weight b.1 p ≠ 0
    intro hz
    exact hp (by simp only [psi,cycleWeights,shrinkingCircularWeight,hz,zero_mul])
  have hell' (k : Fin N) (i : d.B.centers) (j : Fin 3) :
      ‖ell k i j-(d.P i).ξ j‖ < pt := by
    have hh := (hell (copy k (i,j))).trans_le (min_le_left _ _)
    simpa only [ind,cmp,(hcopy k (i,j)).2,ell,cycleLinearParts] using hh
  choose fc hphase hamp hnonamp hposamp hsamp using fun k : Fin N =>
    hcorrect (ell k) (psi k) (hell' k) (hpsi k).2.1 (hnon k) (hsupp k)
      (fun b p => ((hpsi k).2.2.2.2.1 b p).trans_le (min_le_left _ _)) G hG
      (fun i => (hGF i).mono_const (min_le_left _ _))
  let f := fun k => (fc k).reindex e
  have hphase' (a : Fin (N*m)) : (f a.divNat).phase a.modNat = q.copiedPhases a := by
    change (fc a.divNat).phase (e a.modNat) = _
    rw [hphase a.divNat]
    change d.B.circularPhase (e a.modNat).1
      (ell a.divNat (e a.modNat).1 (e a.modNat).2) (d.L (e a.modNat).1) = _
    rw [show ell a.divNat (e a.modNat).1 (e a.modNat).2 = q.linearPart a from by
      change q.linearPart (copy a.divNat (e a.modNat)) = q.linearPart a
      rw [hcopy' a]]
    simp only [CircularFamilyGeometry.copiedPhases,hindex a,hL a,ind]
  have hpositive (a : Fin (N*m)) (p : M) :
      0 < (f a.divNat).amplitude a.modNat p ↔
        p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a) := by
    change 0 < (fc a.divNat).amplitude (e a.modNat) p ↔ _
    rw [hposamp a.divNat (e a.modNat) p]
    have hh := (hpsi a.divNat).2.2.1 (e a.modNat) p
    change 0 < psi a.divNat (e a.modNat) p ↔ _ at hh
    simpa only [rr,hcopy' a,hindex a,ind] using hh
  obtain ⟨D,hD⟩ := q.with_cycle_families f hN
    (fun k a p => hnonamp k (e a) p) hpositive hphase' d.outer
  refine ⟨f,D,?_,?_,hD⟩
  · intro k a
    change (fc k).amplitude (e a) = _
    exact congrFun (hamp k) (e a)
  · intro k a
    change (fc k).phase (e a) = _
    exact congrFun (hphase k) (e a)

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles_oai.{u_1}
