-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:17.195853+00:00
-- url     : https://prove2.me/submissions/0cb0eb33-cd2b-4919-9980-6fd51cd12498

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_adapted_primitive_geometry
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SupportedPrimitivePatch_boundary_step

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricCoordinates
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

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter Bundle Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]

lemma covectorSquare_evaluate (ξ v w : SmallModes.Base) :
    PhaseMean.evaluate (covectorSquare ξ) v w = phaseLinear ξ v * phaseLinear ξ w := by
  simp [PhaseMean.evaluate,covectorSquare,phaseLinear_apply]
  ring

end ClosedSurfaceR4

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

lemma covectorDet_pullback (A : CurvePlane →L[ℝ] CurvePlane) (v w : CurvePlane) :
    covectorDet (pullCovector A v) (pullCovector A w) = coordDet A * covectorDet v w := by
  dsimp [covectorDet,pullCovector,coordDet]
  ring

lemma phaseLinear_ne_zero_on_kernel {v w t : CurvePlane}
    (hdet : covectorDet v w ≠ 0) (ht : t ≠ 0) (hv : phaseLinear v t = 0) :
    phaseLinear w t ≠ 0 := by
  intro hw
  by_cases ht1 : t.1 = 0
  · have ht2 : t.2 ≠ 0 := fun ht2 => ht (Prod.ext ht1 ht2)
    have he : covectorDet v w * t.2 = v.1 * phaseLinear w t-w.1 * phaseLinear v t := by
      dsimp [covectorDet,phaseLinear_apply]
      ring
    rw [hv,hw,mul_zero,mul_zero,sub_self] at he
    exact hdet ((mul_eq_zero.mp he).resolve_right ht2)
  · have he : covectorDet v w * t.1 = w.2 * phaseLinear v t-v.2 * phaseLinear w t := by
      dsimp [covectorDet,phaseLinear_apply]
      ring
    rw [hv,hw,mul_zero,mul_zero,sub_self] at he
    exact hdet ((mul_eq_zero.mp he).resolve_right ht1)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredAtlasDifferentials
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateTransition_det_ne (q p : M) {x : CurvePlane}
    (hx : x ∈ (coordinateTransition q p).source) :
    coordDet (fderiv ℝ (coordinateTransition q p) x) ≠ 0 := by
  let e := coordinateTransition q p
  exact coordDet_fderiv_ne_zero_of_local_inverse e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun y hy => e.left_inv hy) hx

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CompactSmoothCutoffs
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested compact cutoffs in finite-dimensional parameter spaces. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma supported_local_mul {χ f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hn : x ∉ tsupport χ := fun h => hx (hs h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    exact (congrArg (fun t : ℝ => t * f y) hy).trans (zero_mul _)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfacePhaseCharts
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual surface chart associated with a nonlinear phase. It is
independent of the correction atlas and supplies the chart transitions for later curves. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseChart_apply (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (p : M) :
    surfacePhaseChart q e p = baseEquiv (e (FiniteOrderSmoothing.chart q p)) := rfl

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseChart_symm_apply (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (x : SmallModes.Base) :
    (surfacePhaseChart q e).symm x =
      (FiniteOrderSmoothing.chart q).symm (e.symm (baseEquiv.symm x)) := rfl

lemma surfacePhaseChart_smooth (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (surfacePhaseChart q e)
      (surfacePhaseChart q e).source := by
  exact (baseEquiv.contDiff.comp he).contMDiff.comp_contMDiffOn
    ((FiniteOrderSmoothing.chart_smooth q).mono (fun _ hx => hx.1))

lemma surfacePhaseChart_symm_smooth (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) :
    ContMDiffOn 𝓘(ℝ,SmallModes.Base) planeModel ∞ (surfacePhaseChart q e).symm
      (surfacePhaseChart q e).target := by
  exact (FiniteOrderSmoothing.chart_symm_smooth q).comp
    (hi.comp baseEquiv.symm.contDiff).contMDiff.contMDiffOn (fun _ hx => hx.2)

lemma surfacePhaseTransition_smooth (p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) (q : M)
    (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (surfacePhaseTransition p e q f) (surfacePhaseTransition p e q f).source := by
  apply ContMDiffOn.contDiffOn
  exact (surfacePhaseChart_smooth q f hf).comp
    ((surfacePhaseChart_symm_smooth p e hi).mono (fun _ hx => hx.1)) (fun _ hx => hx.2)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFlatBump
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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

lemma circularRadiusSquared_derivative (c p v : Base) :
    coordDeriv v (circularRadiusSquared c) p =
      2*((p.1-c.1)*v.1 + (p.2-c.2)*v.2) := by
  have h₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := p) |>.sub_const c.1
  have h₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p) |>.sub_const c.2
  have hd := (h₁.pow 2).add (h₂.pow 2)
  have he : circularRadiusSquared c =
      ((fun x : Base => ((ContinuousLinearMap.fst ℝ ℝ ℝ) x-c.1)^2) +
        fun x : Base => ((ContinuousLinearMap.snd ℝ ℝ ℝ) x-c.2)^2) := rfl
  change (fderiv ℝ (circularRadiusSquared c) p) v = _
  rw [he,hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', two_smul, smul_eq_mul]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CircularSmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularDiskTopology
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coordinate disks are regular open, with exactly the stated
coordinate circles as their frontiers. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

private lemma complex_radius_sq (c x : Base) :
    ‖Complex.equivRealProdCLM.symm x - Complex.equivRealProdCLM.symm c‖^2 =
      circularRadiusSquared c x := by
  rw [← map_sub,Complex.sq_norm]
  simp [Complex.equivRealProdCLM_symm_apply,Complex.normSq_apply,circularRadiusSquared,pow_two]

private lemma circular_region_ball (c : Base) {r : ℝ} (hr : 0 < r) :
    {x | circularRadiusSquared c x < r^2} =
      Complex.equivRealProdCLM.symm ⁻¹' ball (Complex.equivRealProdCLM.symm c) r := by
  ext x
  rw [mem_preimage,mem_ball,dist_eq_norm]
  change circularRadiusSquared c x < r^2 ↔ _
  rw [← complex_radius_sq]
  exact sq_lt_sq₀ (norm_nonneg _) hr.le

private lemma circular_region_closedBall (c : Base) {r : ℝ} (hr : 0 < r) :
    {x | circularRadiusSquared c x ≤ r^2} =
      Complex.equivRealProdCLM.symm ⁻¹' closedBall (Complex.equivRealProdCLM.symm c) r := by
  ext x
  rw [mem_preimage,mem_closedBall,dist_eq_norm]
  change circularRadiusSquared c x ≤ r^2 ↔ _
  rw [← complex_radius_sq]
  exact sq_le_sq₀ (norm_nonneg _) hr.le

lemma closure_circular_region (c : Base) {r : ℝ} (hr : 0 < r) :
    closure {x | circularRadiusSquared c x < r^2} = {x | circularRadiusSquared c x ≤ r^2} := by
  rw [circular_region_ball c hr]
  change closure (Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' ball
    (Complex.equivRealProdCLM.symm c) r) = _
  rw [← Complex.equivRealProdCLM.symm.toHomeomorph.preimage_closure,closure_ball _ hr.ne']
  exact (circular_region_closedBall c hr).symm

lemma interior_circular_region (c : Base) {r : ℝ} (hr : 0 < r) :
    interior {x | circularRadiusSquared c x ≤ r^2} = {x | circularRadiusSquared c x < r^2} := by
  rw [circular_region_closedBall c hr]
  change interior (Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' closedBall
    (Complex.equivRealProdCLM.symm c) r) = _
  rw [← Complex.equivRealProdCLM.symm.toHomeomorph.preimage_interior,interior_closedBall _ hr.ne']
  exact (circular_region_ball c hr).symm

end ClosedSurfaceR4.PhaseGeometry
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_iff (q : M) {r : ℝ}
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) (p : M) :
    p ∈ circularDiskClosure q r ↔ p ∈ (coordinateChart q).source ∧
      circularRadiusSquared (coordinateChart q q) (coordinateChart q p) ≤ r^2 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(coordinateChart q).map_target (hreg hx),?_⟩
    rwa [(coordinateChart q).right_inv (hreg hx)]
  · rintro ⟨hp,hx⟩
    exact ⟨coordinateChart q p,hx,(coordinateChart q).left_inv hp⟩

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_closure (q : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) :
    closure (circularCoordinateDisk q r) = circularDiskClosure q r := by
  let S := {x : SmallModes.Base | circularRadiusSquared (coordinateChart q q) x < r^2}
  have hI : (coordinateChart q).IsImage (circularCoordinateDisk q r) S := by
    intro p hp
    exact ⟨fun hx => ⟨hp,hx⟩,fun hx => hx.2⟩
  have hc : closure (circularCoordinateDisk q r) ⊆ circularDiskClosure q r := by
    apply closure_minimal _ (circularDiskClosure_compact q r hreg).isClosed
    intro p hp
    exact (circularDiskClosure_iff q hreg p).mpr ⟨hp.1,hp.2.le⟩
  apply Subset.antisymm hc
  intro p hp
  obtain ⟨hs,hx⟩ := (circularDiskClosure_iff q hreg p).mp hp
  apply (hI.closure hs).mp
  simpa only [S,closure_circular_region _ hr,mem_ofPred] using hx

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_interior (q : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) :
    interior (circularDiskClosure q r) = circularCoordinateDisk q r := by
  let S := {x : SmallModes.Base | circularRadiusSquared (coordinateChart q q) x ≤ r^2}
  have hI : (coordinateChart q).IsImage (circularDiskClosure q r) S := by
    intro p hp
    exact ⟨fun hx => (circularDiskClosure_iff q hreg p).mpr ⟨hp,hx⟩,
      fun hx => ((circularDiskClosure_iff q hreg p).mp hx).2⟩
  ext p
  constructor
  · intro hp
    have hs := circularDiskClosure_source q r hreg (interior_subset hp)
    have hx := (hI.interior hs).mpr hp
    exact ⟨hs,by simpa only [S,interior_circular_region _ hr,mem_ofPred,mem_preimage] using hx⟩
  · intro hp
    apply (circularCoordinateDisk_open q r).subset_interior_iff.mpr ?_ hp
    exact fun p hp => (circularDiskClosure_iff q hreg p).mpr ⟨hp.1,hp.2.le⟩

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_frontier (q : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) :
    frontier (circularCoordinateDisk q r) = circularBoundary q r := by
  rw [frontier,circularCoordinateDisk_closure q hr hreg,
    (circularCoordinateDisk_open q r).interior_eq]
  ext p
  simp only [Set.mem_sdiff,circularDiskClosure_iff q hreg p,circularCoordinateDisk,circularBoundary,
    mem_inter_iff,mem_preimage,mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hp,hle⟩,hn⟩
    exact ⟨hp,le_antisymm hle (not_lt.mp (fun hlt => hn ⟨hp,hlt⟩))⟩
  · rintro ⟨hp,he⟩
    exact ⟨⟨hp,he.le⟩,fun hlt => (lt_irrefl _ (he ▸ hlt.2))⟩

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_regular (q : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) :
    interior (closure (circularCoordinateDisk q r)) = circularCoordinateDisk q r := by
  rw [circularCoordinateDisk_closure q hr hreg,circularDiskClosure_interior q hr hreg]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhaseDiskTopology
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact primitive disks and their boundaries in the actual phase chart. -/
noncomputable section
open Set Filter Manifold
open scoped Topology
namespace ClosedSurfaceR4
open SmallModes
variable {M : Type*} [TopologicalSpace M]

lemma compact_phase_disk_geometry (E : OpenPartialHomeomorph M Base)
    {D : Set M} (hD : IsOpen D) (hK : IsCompact (closure D))
    (hS : closure D ⊆ E.source) :
    IsOpen (E '' D) ∧ closure (E '' D) = E '' closure D ∧
      frontier (E '' D) = E '' frontier D ∧ IsCompact (closure (E '' D)) := by
  have hSD : D ⊆ E.source := subset_trans subset_closure hS
  have hI : E.IsImage D (E '' D) := by
    intro p hp
    constructor
    · rintro ⟨q,hq,he⟩
      have hqp := E.injOn (hSD hq) hp he
      exact hqp ▸ hq
    · exact fun hpD => ⟨p,hpD,rfl⟩
  have hIE : E.target ∩ E '' D = E '' D := inter_eq_right.mpr (by
    rintro _ ⟨p,hp,rfl⟩
    exact E.map_source (hSD hp))
  have hO : IsOpen (E '' D) := by
    rw [← hIE]
    exact hI.isOpen_iff.mp (E.open_source.inter hD)
  have hC : IsCompact (E '' closure D) := hK.image_of_continuousOn (E.continuousOn.mono hS)
  have hc : closure (E '' D) = E '' closure D := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure) hC.isClosed
    · rintro _ ⟨p,hp,rfl⟩
      exact (hI.closure (hS hp)).mpr hp
  have hf : frontier (E '' D) = E '' frontier D := by
    rw [frontier,hO.interior_eq,hc,frontier,hD.interior_eq]
    ext y
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hn⟩
      exact ⟨p,⟨hp,fun hpD => hn ⟨p,hpD,rfl⟩⟩,rfl⟩
    · rintro ⟨p,⟨hp,hn⟩,rfl⟩
      refine ⟨⟨p,hp,rfl⟩,?_⟩
      rintro ⟨q,hq,he⟩
      have hqp := E.injOn (hSD hq) (hS hp) he
      exact hn (hqp ▸ hq)
  exact ⟨hO,hc,hf,hc ▸ hC⟩

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTensorPullback
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pullback of finite tensor expressions under fixed coordinate changes.
The Jacobian factors, coefficient substitution, and higher jet atoms are
all constructed, so the evaluation identity assumes no tensor covariance. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Matrix Topology

namespace ClosedSurfaceR4.JetPolynomial

lemma tensorCoordinateJacobian_sum (T : Base → Base) (x : Base)
    (A : PhaseMean.Tensor) (k : Fin 3) :
    (∑ l : Fin 3, tensorCoordinateJacobian T k l x * A l) =
      tensorCoordinatePullbackValue T x A k := by
  rw [Fin.sum_univ_three]
  let u := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.firstDirection k))
  let v := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.secondDirection k))
  change u 0 * v 0 * A 0 + (u 0 * v 1 + u 1 * v 0) * A 1 + u 1 * v 1 * A 2 =
    A 0 * u 0 * v 0 + A 1 * (u 0 * v 1 + u 1 * v 0) + A 2 * u 1 * v 1
  ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveSecondFields
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth global representatives of second-form fields along a compact curve.
A cutoff in its own phase chart extends the field without choosing a normal frame. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SmallModes NormalFrame SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseCurveSecondField_eq (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (β : SmallModes.Base → ℝ) (F : M → Space) (v w : SmallModes.Base → SmallModes.Base)
    {p : M} (hp : p ∈ (chart (i : M)).source) (ho : A.outer i p = 1)
    (hβ : β (baseEquiv (e (chart (i : M) p))) = 1) :
    spaceCoordinates (A.phaseCurveSecondField i e β F v w p) =
      realSecondForm (A.phaseRealChartMap i e.symm F)
        (v (baseEquiv (e (chart (i : M) p)))) (w (baseEquiv (e (chart (i : M) p))))
        (baseEquiv (e (chart (i : M) p))) := by
  simp only [phaseCurveSecondField,restore,indicator_of_mem hp,ho,hβ,one_smul,
    spaceCoordinates.apply_symm_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseBoundaryCurve
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed compact boundary curves and their actual second-form fields.
The cutoff is chosen from the curve geometry, independently of any immersion. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

lemma cutoff_properties : ContDiff ℝ ∞ c.cutoff ∧ HasCompactSupport c.cutoff ∧
    (∀ x ∈ c.coordinate '' c.carrier, c.cutoff x = 1) ∧
    ∀ x ∈ tsupport c.cutoff, baseEquiv.symm x ∈ c.phase.target ∧
      B.chartWeight c.index (c.phase.symm (baseEquiv.symm x)) ≠ 0 :=
  Classical.choose_spec c.cutoff_exists

lemma second_eq (F : M → Space) {p : M} (hp : p ∈ c.carrier) :
    c.second F p = realSecondForm (B.phaseRealChartMap c.index c.phase.symm F)
      dy dy (c.coordinate p) := by
  apply B.phaseCurveSecondField_eq c.index c.phase c.cutoff F (fun _ => dy) (fun _ => dy)
    (c.source hp).1
  · exact B.outer_one c.index p (subset_tsupport _ (c.active p hp))
  · exact c.cutoff_properties.2.2.1 _ ⟨p,hp,rfl⟩

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveTensor
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transported primitive is the square of the actual first phase
covector, with its supported amplitude. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.JetPolynomial

lemma tensorCoordinatePullback_first_square (T : Base → Base) (x : Base) (a : ℝ) :
    tensorCoordinatePullbackValue T x ![a^2,0,0] =
      a^2 • PhaseGeometry.covectorSquare (firstPhaseCovector T x) := by
  have hx : planeCoordinateIsometry.symm SmallModes.dx = coordinateVector 0 := by
    ext i
    fin_cases i <;> rfl
  have hy : planeCoordinateIsometry.symm SmallModes.dy = coordinateVector 1 := by
    ext i
    fin_cases i <;> rfl
  ext k
  rw [← tensorCoordinateJacobian_sum,Fin.sum_univ_three]
  fin_cases k <;> simp [tensorCoordinateJacobian,firstPhaseCovector,
    PhaseGeometry.covectorSquare,PhaseMean.firstDirection,PhaseMean.secondDirection,
    hx,hy] <;> ring

lemma localizedTensorPullback_first_square (T : Base → Base) (χ a : Base → ℝ) (x : Base) :
    localizedTensorPullback T χ (fun y => ![a y^2,0,0]) x =
      (χ x * (a (T x))^2) • PhaseGeometry.covectorSquare (firstPhaseCovector T x) := by
  rw [localizedTensorPullback,tensorCoordinatePullback_first_square,smul_smul]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCoordinateCovector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first phase coordinate has the exact covector used by the local
rank-one tensor pullback. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates

namespace JetPolynomial
lemma firstPhaseCovector_apply (T : Base → Base) (x v : Base) :
    phaseLinear (firstPhaseCovector T x) (baseEquiv v) = (fderiv ℝ T x v) 0 := by
  have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 := by
    ext k
    fin_cases k <;> simp [coordinateVector]
  conv_rhs => rw [hv]
  simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change (fderiv ℝ T x (coordinateVector 0)) 0 * v 0 +
    (fderiv ℝ T x (coordinateVector 1)) 0 * v 1 = _
  ring
end JetPolynomial

namespace FiniteOrderSmoothing.SmoothingAtlas
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable (A : SmoothingAtlas M)

lemma jetChart_tangentCoordinates (i : A.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p =
      (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap.comp
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p) := by
  have hp' : p ∈ (chartAt Plane (i : M)).source := by simpa only [chart_source] using hp
  have hc := (contMDiffOn_chart (I := planeModel) (n := ∞) (x := (i : M)) p hp').contMDiffAt
    ((chartAt Plane (i : M)).open_source.mem_nhds hp')
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hp']
  change mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base)
    ((EuclideanSpace.equiv (Fin 2) ℝ) ∘ chartAt Plane (i : M)) p = _
  rw [mfderiv_comp p
    (((EuclideanSpace.equiv (Fin 2) ℝ).contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt
    (hc.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),mfderiv_eq_fderiv,
    (EuclideanSpace.equiv (Fin 2) ℝ).fderiv]
  rfl

lemma phaseFirst_mfderiv (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) {phi : M → ℝ} {p : M}
    (hp : p ∈ (chart (i : M)).source)
    (hphi : phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0))
    (v : TangentSpace planeModel p) :
    mfderiv planeModel 𝓘(ℝ) phi p v =
      phaseLinear (JetPolynomial.firstPhaseCovector e (chart (i : M) p))
        (planeCoordinates
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)) := by
  let f : JetPolynomial.Base → ℝ := fun y => e y 0
  have hf : ContDiff ℝ ∞ f := (contDiff_pi.mp he 0)
  have hc := (chart_smooth (i : M) p hp).contMDiffAt ((chart (i : M)).open_source.mem_nhds hp)
  rw [hphi.mfderiv_eq]
  change mfderiv planeModel 𝓘(ℝ) (f ∘ chart (i : M)) p v = _
  rw [mfderiv_comp p (hf.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv,A.jetChart_tangentCoordinates i hp]
  change fderiv ℝ f (chart (i : M) p)
    ((EuclideanSpace.equiv (Fin 2) ℝ)
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)) = _
  rw [fderiv_apply (he.differentiable (by simp) _) 0]
  exact (JetPolynomial.firstPhaseCovector_apply e _ _).symm

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseDiskSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the analytic support with the closed geometric primitive disk. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseSurfaceSupport_image (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {C : Set M} (hC : IsClosed C) (hchart : C ⊆ (chart (i : M)).source)
    (hphase : (chart (i : M)) '' C ⊆ e.source) :
    A.phaseSurfaceSupport i e (e '' ((chart (i : M)) '' C)) = C := by
  have he : e.symm '' (e '' ((chart (i : M)) '' C)) = (chart (i : M)) '' C := by
    ext y
    constructor
    · rintro ⟨z,⟨q,hq,rfl⟩,rfl⟩
      simpa only [e.left_inv (hphase hq)] using hq
    · intro hy
      exact ⟨e y,⟨y,hy,rfl⟩,e.left_inv (hphase hy)⟩
  have hc : (chart (i : M)).symm '' ((chart (i : M)) '' C) = C := by
    ext p
    constructor
    · rintro ⟨q,⟨x,hx,rfl⟩,rfl⟩
      simpa only [(chart (i : M)).left_inv (hchart hx)] using hx
    · intro hp
      exact ⟨chart (i : M) p,⟨p,hp,rfl⟩,(chart (i : M)).left_inv (hchart hp)⟩
  rw [phaseSurfaceSupport,he,hc,hC.closure_eq]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseFrontierAvoidance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the preserved normal condition on the actual boundary curve
to the frontier of the disk in phase coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

lemma frontier_avoidance {D : Set M} (hD : IsOpen D)
    (hDs : closure D ⊆ (surfacePhaseChart (c.index : M) c.phase).source)
    (hfront : c.carrier = frontier D)
    {F : M → Space} (n : PreferredNormal F)
    (hold : ∀ p ∈ c.carrier, c.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c.second F p)) :
    ∀ x ∈ frontier ((surfacePhaseChart (c.index : M) c.phase) '' D),
      realSecondForm (B.phaseRealChartMap c.index c.phase.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (B.phaseRealChartMap c.index c.phase.symm F) dy dy x) ≠
        -n.inPhase (c.index : M) c.phase x := by
  let E := surfacePhaseChart (c.index : M) c.phase
  have hK : IsCompact (closure D) := isClosed_closure.isCompact
  have h := compact_phase_disk_geometry E hD hK hDs
  intro x hx
  rw [h.2.2.1] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  have hpc : p ∈ c.carrier := hfront.symm ▸ hp
  have hsec : c.second F p = realSecondForm (B.phaseRealChartMap c.index c.phase.symm F)
      dy dy (E p) := c.second_eq F hpc
  have hn : n.inPhase (c.index : M) c.phase (E p) = spaceCoordinates (n.vector p) := by
    change spaceCoordinates (n.vector (E.symm (E p))) = _
    rw [E.left_inv (hDs (frontier_subset_closure hp))]
  rw [← hsec,hn]
  refine ⟨(hold p hpc).1,?_⟩
  intro he
  apply (hold p hpc).2
  rw [he,neg_neg]

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricRegion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An open phase region inside the fixed atlas patch and the uniform
coordinate radius used by the metric convexity estimate. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem phase_metric_region (j : B.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set M} (hKs : K ⊆ (surfacePhaseChart (j : M) e).source)
    (hactive : ∀ p ∈ K, B.weight j p ≠ 0) {r : ℝ}
    (hsmall : ∀ p ∈ K, ‖coordinateChart (j : M) p-coordinateChart (j : M) (j : M)‖ < r) :
    ∃ Ω : Set Base, IsOpen Ω ∧ (surfacePhaseChart (j : M) e) '' K ⊆ Ω ∧
      Ω ⊆ (surfacePhaseChart (j : M) e).target ∧
      ∀ x ∈ Ω, B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0 ∧
        ‖coordinateChart (j : M) ((surfacePhaseChart (j : M) e).symm x)-
          coordinateChart (j : M) (j : M)‖ < r := by
  let E := surfacePhaseChart (j : M) e
  let P := {p : M | B.weight j p ≠ 0} ∩
    ((coordinateChart (j : M)).source ∩ (coordinateChart (j : M)) ⁻¹'
      Metric.ball (coordinateChart (j : M) (j : M)) r)
  have hP : IsOpen P := (isOpen_ne.preimage (B.weight_smooth j).continuous).inter
    ((coordinateChart (j : M)).isOpen_inter_preimage Metric.isOpen_ball)
  let W := E.source ∩ P
  have hW : IsOpen W := E.open_source.inter hP
  let Ω := E '' W
  refine ⟨Ω,E.isOpen_image_of_subset_source hW inter_subset_left,?_,?_,?_⟩
  · rintro x ⟨p,hp,rfl⟩
    refine ⟨p,⟨hKs hp,hactive p hp,?_,?_⟩,rfl⟩
    · have hs : p ∈ (chart (j : M)).source := (hKs hp).1
      simpa only [coordinateChart_source,chart_source] using hs
    · simpa only [Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hsmall p hp
  · rintro x ⟨p,hp,rfl⟩
    exact E.map_source hp.1
  · rintro x ⟨p,hp,rfl⟩
    rw [E.left_inv hp.1]
    exact ⟨hp.2.1,by simpa only [Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hp.2.2.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseTransitionCocycle
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chain identities for the actual nonlinear phase charts. They transport
both directions of an ordered crossing through a third chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_apply (q r : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) {p : M}
    (hp : p ∈ (surfacePhaseChart q e).source) :
    surfacePhaseTransition q e r f (surfacePhaseChart q e p) = surfacePhaseChart r f p := by
  change (surfacePhaseChart r f) ((surfacePhaseChart q e).symm (surfacePhaseChart q e p)) = _
  rw [(surfacePhaseChart q e).left_inv hp]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_source (q r : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) {p : M}
    (hp : p ∈ (surfacePhaseChart q e).source) (hr : p ∈ (surfacePhaseChart r f).source) :
    surfacePhaseChart q e p ∈ (surfacePhaseTransition q e r f).source := by
  refine ⟨(surfacePhaseChart q e).map_source hp,?_⟩
  change (surfacePhaseChart q e).symm (surfacePhaseChart q e p) ∈ (surfacePhaseChart r f).source
  rwa [(surfacePhaseChart q e).left_inv hp]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_cocycle_germ (q₁ q₂ q₃ : M)
    (e₁ e₂ e₃ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {p : M} (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (h₃ : p ∈ (surfacePhaseChart q₃ e₃).source) :
    surfacePhaseTransition q₂ e₂ q₃ e₃ ∘ surfacePhaseTransition q₁ e₁ q₂ e₂ =ᶠ[𝓝 (surfacePhaseChart q₁ e₁ p)] surfacePhaseTransition q₁ e₁ q₃ e₃ := by
  have h₁₂ := surfacePhaseTransition_source q₁ q₂ e₁ e₂ h₁ h₂
  have h₁₃ := surfacePhaseTransition_source q₁ q₃ e₁ e₃ h₁ h₃
  filter_upwards [(surfacePhaseTransition q₁ e₁ q₂ e₂).open_source.mem_nhds h₁₂,
    (surfacePhaseTransition q₁ e₁ q₃ e₃).open_source.mem_nhds h₁₃] with x hx _
  have hxs : (surfacePhaseChart q₁ e₁).symm x ∈ (surfacePhaseChart q₂ e₂).source := hx.2
  change (surfacePhaseChart q₃ e₃) ((surfacePhaseChart q₂ e₂).symm
    ((surfacePhaseChart q₂ e₂) ((surfacePhaseChart q₁ e₁).symm x))) = _
  rw [(surfacePhaseChart q₂ e₂).left_inv hxs]
  rfl

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_self_germ (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart q e).target) :
    surfacePhaseTransition q e q e =ᶠ[𝓝 x] id := by
  filter_upwards [(surfacePhaseChart q e).open_target.mem_nhds hx] with y hy
  exact (surfacePhaseChart q e).right_inv hy

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_self_fderiv (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart q e).target) :
    fderiv ℝ (surfacePhaseTransition q e q e) x = ContinuousLinearMap.id ℝ SmallModes.Base := by
  rw [(surfacePhaseTransition_self_germ q e hx).fderiv_eq,fderiv_id]

lemma surfacePhaseTransition_fderiv_cocycle (q₁ q₂ q₃ : M)
    (e₁ e₂ e₃ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi₁ : ContDiff ℝ ∞ e₁.symm) (he₂ : ContDiff ℝ ∞ e₂)
    (hi₂ : ContDiff ℝ ∞ e₂.symm) (he₃ : ContDiff ℝ ∞ e₃)
    {p : M} (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (h₃ : p ∈ (surfacePhaseChart q₃ e₃).source) :
    fderiv ℝ (surfacePhaseTransition q₁ e₁ q₃ e₃) (surfacePhaseChart q₁ e₁ p) =
      (fderiv ℝ (surfacePhaseTransition q₂ e₂ q₃ e₃) (surfacePhaseChart q₂ e₂ p)).comp
        (fderiv ℝ (surfacePhaseTransition q₁ e₁ q₂ e₂) (surfacePhaseChart q₁ e₁ p)) := by
  have h₁₂ := surfacePhaseTransition_source q₁ q₂ e₁ e₂ h₁ h₂
  have h₂₃ := surfacePhaseTransition_source q₂ q₃ e₂ e₃ h₂ h₃
  have hd₁₂ := (((surfacePhaseTransition_smooth q₁ e₁ hi₁ q₂ e₂ he₂)
    (surfacePhaseChart q₁ e₁ p) h₁₂).contDiffAt
      ((surfacePhaseTransition q₁ e₁ q₂ e₂).open_source.mem_nhds h₁₂)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd₂₃ := (((surfacePhaseTransition_smooth q₂ e₂ hi₂ q₃ e₃ he₃)
    (surfacePhaseChart q₂ e₂ p) h₂₃).contDiffAt
      ((surfacePhaseTransition q₂ e₂ q₃ e₃).open_source.mem_nhds h₂₃)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg := surfacePhaseTransition_cocycle_germ q₁ q₂ q₃ e₁ e₂ e₃ h₁ h₂ h₃
  rw [← hg.fderiv_eq]
  have ht := surfacePhaseTransition_apply q₁ q₂ e₁ e₂ h₁
  rw [fderiv_comp _ (by rwa [ht]) hd₁₂,ht]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseOrdinaryCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The identity phase recovers ordinary surface coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates RealModes SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma surfacePhaseChart_refl_apply (q p : M) :
    surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base) p = coordinateChart q p := rfl

lemma surfacePhaseChart_refl_symm_apply (q : M) (x : SmallModes.Base) :
    (surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base)).symm x =
      (coordinateChart q).symm x := by
  simp [surfacePhaseChart_symm_apply,FiniteOrderSmoothing.chart,coordinateChart_symm_apply,
    coordinateInverse,planeModel,baseEquiv,planeCoordinates]

lemma surfacePhaseChart_refl_source (q : M) :
    (surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base)).source =
      (coordinateChart q).source := by
  simp [surfacePhaseChart,FiniteOrderSmoothing.chart,coordinateChart]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseTargetCongruence
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting a target phase chart keeps every transition function. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma surfacePhaseTransition_target_congr (p q r : M) (hqr : q = r)
    (e f g : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hfg : ∀ x, f x = g x) :
    (surfacePhaseTransition p e q f : SmallModes.Base → SmallModes.Base) =
      surfacePhaseTransition p e r g := by
  subst r
  funext x
  change baseEquiv (f (FiniteOrderSmoothing.chart q ((surfacePhaseChart p e).symm x))) =
    baseEquiv (g (FiniteOrderSmoothing.chart q ((surfacePhaseChart p e).symm x)))
  rw [hfg]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseTransitionRegularity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A phase-coordinate transition preserves nonzero tangent directions. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates RealModes SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma surfacePhaseTransition_fderiv_injective (p q : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {a : M} (hp : a ∈ (surfacePhaseChart p e).source)
    (hq : a ∈ (surfacePhaseChart q f).source) :
    Function.Injective (fderiv ℝ (surfacePhaseTransition p e q f) (surfacePhaseChart p e a)) := by
  have hh := surfacePhaseTransition_fderiv_cocycle p q p e f e hi hf hfi he hp hq hp
  rw [surfacePhaseTransition_self_fderiv p e ((surfacePhaseChart p e).map_source hp)] at hh
  intro v w hvw
  have hv := congrArg (fun L : Base →L[ℝ] Base => L v) hh
  have hw := congrArg (fun L : Base →L[ℝ] Base => L w) hh
  simp only [ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply] at hv hw
  exact hv.trans ((congrArg (fderiv ℝ (surfacePhaseTransition q f p e)
    (surfacePhaseChart q f a)) hvw).trans hw.symm)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseTransverseDefiner
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A boundary transverse to a phase has a nonzero defining derivative in
that phase's second coordinate. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma phase_chart_transverse_definer_at {φ ρ : Base → ℝ} {f : Base → Base}
    {p : Base} (hφ : DifferentiableAt ℝ φ (f p)) (hρ : DifferentiableAt ℝ ρ (f p))
    (hf : DifferentiableAt ℝ f p) (hphase : φ ∘ f =ᶠ[𝓝 p] Prod.fst)
    (hD : coordDet (fderiv ℝ f p) ≠ 0)
    (hcross : covectorDet (phaseDerivative φ (f p)) (phaseDerivative ρ (f p)) ≠ 0) :
    fderiv ℝ (ρ ∘ f) p dy ≠ 0 := by
  have hcomp (ψ : Base → ℝ) (hψ : DifferentiableAt ℝ ψ (f p)) :
      phaseDerivative (ψ ∘ f) p = pullCovector (fderiv ℝ f p) (phaseDerivative ψ (f p)) := by
    unfold phaseDerivative
    rw [fderiv_comp p hψ hf]
    change ((fderiv ℝ ψ (f p)) ((fderiv ℝ f p) dx),
      (fderiv ℝ ψ (f p)) ((fderiv ℝ f p) dy)) = _
    conv_lhs => rw [← phaseLinear_phaseDerivative ψ (f p)]
    rfl
  have hfirst : pullCovector (fderiv ℝ f p) (phaseDerivative φ (f p)) = dx := by
    rw [← hcomp φ hφ]
    unfold phaseDerivative
    rw [hphase.fderiv_eq,fderiv_fst]
    rfl
  have hdet := covectorDet_pullback (fderiv ℝ f p)
    (phaseDerivative φ (f p)) (phaseDerivative ρ (f p))
  rw [hfirst,← hcomp ρ hρ] at hdet
  have hne := mul_ne_zero hD hcross
  rw [← hdet] at hne
  simpa only [covectorDet,dx,phaseDerivative,one_mul,zero_mul,sub_zero] using hne

lemma circular_radius_phase_determinant (φ : Base → ℝ) (c p : Base) :
    covectorDet (phaseDerivative φ p) (phaseDerivative (circularRadiusSquared c) p) =
      -2 * phaseLinear (phaseDerivative φ p)
        (FiniteOrderSmoothing.circularAngularTangent c p) := by
  have hx := circularRadiusSquared_derivative c p dx
  have hy := circularRadiusSquared_derivative c p dy
  unfold covectorDet phaseDerivative
  change coordDeriv dx φ p * coordDeriv dy (circularRadiusSquared c) p -
    coordDeriv dy φ p * coordDeriv dx (circularRadiusSquared c) p = _
  rw [hx,hy]
  simp only [phaseLinear_apply,FiniteOrderSmoothing.circularAngularTangent,dx,dy]
  dsimp [coordDeriv]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RealPhaseChart
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual phase chart in the real pair coordinates used by curvature. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial

lemma realPhaseChart_smooth (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) :
    ContDiff ℝ ∞ (realPhaseChart e) :=
  planeCoordinateIsometry.contDiff.comp (he.comp planeCoordinateIsometry.symm.contDiff)

lemma realPhaseChart_symm_smooth (e : OpenPartialHomeomorph Base Base) (hi : ContDiff ℝ ∞ e.symm) :
    ContDiff ℝ ∞ (realPhaseChart e).symm :=
  planeCoordinateIsometry.contDiff.comp (hi.comp planeCoordinateIsometry.symm.contDiff)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfacePhaseAmplitude
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuinely smooth amplitude in phase coordinates, extended by zero
with precisely the original support and no change to its surface values. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_phase_amplitude (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hDc : IsCompact (closure D))
    (hDs : closure D ⊆ (surfacePhaseChart q e).source)
    {f : M → ℝ} (hf : ContMDiff planeModel 𝓘(ℝ) ∞ f)
    (hf0 : ∀ p, 0 ≤ f p) (hfpos : ∀ p, 0 < f p ↔ p ∈ D) :
    ∃ a : SmallModes.Base → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 ≤ a x) ∧
      (∀ p ∈ (surfacePhaseChart q e).source, a (surfacePhaseChart q e p) = f p) ∧
      (∀ x, 0 < a x ↔ x ∈ (surfacePhaseChart q e) '' D) ∧
      ∀ x ∉ (surfacePhaseChart q e) '' closure D, a x = 0 := by
  let E := surfacePhaseChart q e
  let K := E '' closure D
  have hK : IsCompact K := hDc.image_of_continuousOn (E.continuousOn.mono hDs)
  have hKt : K ⊆ E.target := by
    rintro _ ⟨p,hp,rfl⟩
    exact E.map_source (hDs hp)
  obtain ⟨β,hβ,hβc,hβrange,hβs,hβone⟩ :=
    CollarVelocity.compact_cutoff hK E.open_target hKt
  have hraw : ContDiffOn ℝ ∞ (f ∘ E.symm) E.target := by
    exact (hf.comp_contMDiffOn (surfacePhaseChart_symm_smooth q e hi)).contDiffOn
  let a := fun x => β x * f (E.symm x)
  have ha : ContDiff ℝ ∞ a :=
    CollarVelocity.supported_local_mul E.open_target hβ hraw hβs
  have hzero {p : M} (hp : p ∉ D) : f p = 0 :=
    le_antisymm (le_of_not_gt (fun hh => hp ((hfpos p).mp hh))) (hf0 p)
  have heq (p : M) (hp : p ∈ E.source) : a (E p) = f p := by
    change β (E p)*f (E.symm (E p)) = f p
    rw [E.left_inv hp]
    by_cases hpD : p ∈ closure D
    · rw [hβone _ (mem_image_of_mem E hpD),one_mul]
    · rw [hzero (fun hh => hpD (subset_closure hh)),mul_zero]
  refine ⟨a,ha,fun x => mul_nonneg (hβrange x).1 (hf0 _),heq,?_,?_⟩
  · intro x
    constructor
    · intro hx
      have hbx : β x ≠ 0 := by intro hz; change 0 < β x*f (E.symm x) at hx; rw [hz,zero_mul] at hx; exact lt_irrefl _ hx
      have hxt : x ∈ E.target := hβs (subset_tsupport β hbx)
      have hfx : 0 < f (E.symm x) := by
        rw [← E.right_inv hxt,heq _ (E.map_target hxt)] at hx
        exact hx
      exact ⟨E.symm x,(hfpos _).mp hfx,E.right_inv hxt⟩
    · rintro ⟨p,hp,rfl⟩
      rw [heq _ (hDs (subset_closure hp))]
      exact (hfpos p).mpr hp
  · intro x hx
    by_cases hb0 : β x = 0
    · exact by change β x*f (E.symm x) = 0; rw [hb0,zero_mul]
    have hxt : x ∈ E.target := hβs (subset_tsupport β hb0)
    have hpD : E.symm x ∉ D := by
      intro hp
      exact hx ⟨E.symm x,subset_closure hp,E.right_inv hxt⟩
    exact by change β x*f (E.symm x) = 0; rw [hzero hpD,mul_zero]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceRealPhaseChart
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifications of the actual surface phase chart in real coordinates. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma surfacePhaseChart_real_apply (q p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    surfacePhaseChart q e p = ((coordinateChart q).trans (JetPolynomial.realPhaseChart e)) p := by
  change baseEquiv (e (FiniteOrderSmoothing.chart q p)) =
    baseEquiv
      (e (baseEquiv.symm (coordinateChart q p)))
  have hq : coordinateChart q p = baseEquiv (FiniteOrderSmoothing.chart q p) := rfl
  rw [hq,baseEquiv.symm_apply_apply]

lemma surfacePhaseChart_real_source (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    (surfacePhaseChart q e).source =
      ((coordinateChart q).trans (JetPolynomial.realPhaseChart e)).source := by
  ext p
  change (p ∈ (FiniteOrderSmoothing.chart q).source ∧
    FiniteOrderSmoothing.chart q p ∈ e.source) ↔
    (p ∈ (coordinateChart q).source ∧
      baseEquiv.symm (coordinateChart q p) ∈ e.source)
  have hq : coordinateChart q p = baseEquiv (FiniteOrderSmoothing.chart q p) := rfl
  rw [hq,baseEquiv.symm_apply_apply,FiniteOrderSmoothing.chart_source,coordinateChart_source]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteBoundaryGeometry
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite boundary invariant retained by successive primitive corrections. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*}

namespace FiniteBoundaryGeometry

lemma restrict {curves : ι → PhaseBoundaryCurve B} {E : Set M}
    {F : M → Space} {n : PreferredNormal F} (h : FiniteBoundaryGeometry curves E F n)
    {κ : Type*} (f : κ → ι) (hf : Function.Injective f) {E' : Set M} (hE : E' ⊆ E) :
    FiniteBoundaryGeometry (curves ∘ f) E' F n where
  nonzero j p hp := h.nonzero (f j) p hp
  avoids j p hp := h.avoids (f j) p hp
  positive j k hjk p hp hj hk := h.positive (f j) (f k) (fun he => hjk (hf he)) p (hE hp) hj hk
  crossing j k hjk p hp hj hk := h.crossing (f j) (f k) (fun he => hjk (hf he)) p (hE hp) hj hk

end FiniteBoundaryGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteBoundaryLocalDefiners
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite closed boundary families can be isolated locally after any
continuous parametrization; no global extension of their coordinate maps
is needed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma finite_boundary_local_definers {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i)) (f : Base → X)
    {K P : Set Base} (hf : ∀ p ∈ K, ContinuousAt f p)
    (hcover : ∀ p ∈ K, ∃ i, f p ∈ C i)
    (hcross : ∀ i j, i ≠ j → ∀ p ∈ K, f p ∈ C i → f p ∈ C j → p ∈ P)
    (hlocal : ∀ i p, p ∈ K \ P → f p ∈ C i →
      ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧ ∃ g : Base → ℝ,
        ContDiffOn ℝ ∞ g N ∧ (∀ x ∈ N, f x ∈ C i → g x = 0) ∧
          fderiv ℝ g p dy ≠ 0) :
    ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ g : Base → ℝ, ContDiffOn ℝ ∞ g N ∧ (∀ x ∈ K ∩ N, g x = 0) ∧
        fderiv ℝ g p dy ≠ 0 := by
  classical
  intro p hp
  obtain ⟨i,hi⟩ := hcover p hp.1
  obtain ⟨N,hN,hpN,g,hg,hzero,hderiv⟩ := hlocal i p hp hi
  have hav : ∀ᶠ x in 𝓝 p, ∀ j, j ≠ i → f x ∉ C j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => (h hji).elim)
    · have hj : f p ∉ C j := fun hj => hp.2 (hcross i j (Ne.symm hji) p hp.1 hi hj)
      filter_upwards [(hf p hp.1).eventually ((hC j).isOpen_compl.mem_nhds hj)] with x hx _
      exact hx
  obtain ⟨W,hWsub,hW,hpW⟩ := mem_nhds_iff.mp hav
  refine ⟨N ∩ W,hN.inter hW,⟨hpN,hpW⟩,g,hg.mono inter_subset_left,?_,hderiv⟩
  intro x hx
  obtain ⟨j,hj⟩ := hcover x hx.1
  have hji : j = i := by
    by_contra h
    exact hWsub hx.2.2 j h hj
  exact hzero x hx.2.1 (by simpa only [hji] using hj)

end ClosedSurfaceR4.PhaseGeometry

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

omit [CompactSpace M] in
lemma boundaryCrossingSet_finite (curves : ι → PhaseBoundaryCurve B) (s : Set ι)
    (hpair : ∀ i j, i ≠ j → ((curves i).carrier ∩ (curves j).carrier).Finite) :
    (boundaryCrossingSet curves s).Finite := by
  classical
  have hU : (⋃ a : {a : ι × ι // a.1 ≠ a.2},
      (curves a.1.1).carrier ∩ (curves a.1.2).carrier).Finite :=
    Set.finite_iUnion (fun a => hpair a.1.1 a.1.2 a.2)
  apply hU.subset
  rintro p ⟨i,_,j,_,hij,hi,hj⟩
  exact mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hi,hj⟩

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteBoundaryRemoval
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the primitive's own boundary from the finite invariant. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*}

omit [CompactSpace M] in
lemma removed_boundary_crossings_subset (curves : ι → PhaseBoundaryCurve B) (a : ι) :
    boundaryCrossingSet (fun j : {j : ι // j ≠ a} => curves j) univ ⊆
      boundaryCrossingSet curves univ := by
  rintro p ⟨j,_,k,_,hjk,hj,hk⟩
  exact ⟨j,mem_univ _,k,mem_univ _,fun h => hjk (Subtype.ext h),hj,hk⟩

omit [CompactSpace M] in
lemma removed_boundary_crossings_disjoint (curves : ι → PhaseBoundaryCurve B) (a : ι)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅) :
    Disjoint (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => curves j) univ)
      (curves a).carrier := by
  apply Set.disjoint_left.mpr
  rintro p ⟨j,_,k,_,hjk,hj,hk⟩ ha
  have hx : p ∈ (curves j).carrier ∩ (curves k).carrier ∩ (curves a).carrier := ⟨⟨hj,hk⟩,ha⟩
  rw [htriple j k a (fun h => hjk (Subtype.ext h)) j.2 k.2] at hx
  exact hx.elim

namespace FiniteBoundaryGeometry

lemma remove {curves : ι → PhaseBoundaryCurve B} {F : M → Space} {n : PreferredNormal F}
    (h : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n) (a : ι) :
    FiniteBoundaryGeometry (fun j : {j : ι // j ≠ a} => curves j)
      (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => curves j) univ) F n :=
  h.restrict Subtype.val Subtype.val_injective (removed_boundary_crossings_subset curves a)

lemma remove_frontier {curves : ι → PhaseBoundaryCurve B} {F : M → Space} {n : PreferredNormal F}
    (h : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n) (a : ι) :
    ∀ (j : {j : ι // j ≠ a}) p, p ∈ (curves j).carrier ∩ (curves a).carrier →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < (curves a).crossing (curves j) F p := by
  intro j p hp
  have hE := boundaryCrossingSet_pair curves (mem_univ j.val) (mem_univ a) j.2 hp.1 hp.2
  exact ⟨h.positive j a j.2 p hE hp.1 hp.2,h.crossing a j j.2.symm p hE hp.2 hp.1⟩

end FiniteBoundaryGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPhaseBoundaryCurve
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate circles as the fixed phase curves of the induction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

omit [CompactSpace M] in
lemma circular_closed_disk_phase_source [T2Space M]
    (i : B.centers) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion (i : M) r ⊆ (coordinateChart (i : M)).target)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hcover : ∀ x ∈ circularCoordinateRegion (i : M) r, baseEquiv.symm x ∈ e.source) :
    closure (circularCoordinateDisk (i : M) r) ⊆ (surfacePhaseChart (i : M) e).source := by
  rw [circularCoordinateDisk_closure (i : M) hr hreg]
  intro p hp
  obtain ⟨hs,hx⟩ := (circularDiskClosure_iff (i : M) hreg p).mp hp
  refine ⟨?_,?_⟩
  · change p ∈ (chart (i : M)).source
    rw [chart_source]
    simpa only [coordinateChart_source] using hs
  · have h := hcover (coordinateChart (i : M) p) hx
    change baseEquiv.symm (baseEquiv (chart (i : M) p)) ∈ e.source at h
    change chart (i : M) p ∈ e.source
    simpa only [baseEquiv.symm_apply_apply] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CompactPrimitiveSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact compact support data for a primitive on an adapted analytic atlas. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_primitive_support (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) {D : Set M} (hD : IsCompact D)
    (hDs : D ⊆ (surfacePhaseChart (i : M) e).source)
    (hactive : ∀ p ∈ D, A.weight i p ≠ 0) :
    ∃ K : Set JetPolynomial.Base, IsCompact K ∧ K ⊆ e.target ∧
      A.phaseSurfaceSupport i e K = D ∧
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) ∧
      (∀ p ∈ D, e (chart (i : M) p) ∈ K) ∧
      (∀ y ∈ K, A.chartWeight i (e.symm y) ≠ 0) ∧
      ∃ χ : JetPolynomial.Base → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ e.source ∧ ∀ x ∈ e.symm '' K, χ x = 1 := by
  let C := (chart (i : M)) '' D
  have hC : IsCompact C := hD.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (fun _ hp => (hDs hp).1))
  have hCe : C ⊆ e.source := by
    rintro _ ⟨p,hp,rfl⟩
    exact (hDs hp).2
  let K := e '' C
  have hK : IsCompact K := hC.image he.continuous
  have hinv : e.symm '' K = C := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa only [e.left_inv (hCe hz)] using hz
    · exact fun hx => ⟨e x,⟨x,hx,rfl⟩,e.left_inv (hCe hx)⟩
  refine ⟨K,hK,?_,?_,?_,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (hCe hx)
  · exact A.phaseSurfaceSupport_image i e hD.isClosed
      (fun _ hp => (hDs hp).1) hCe
  · rw [hinv]
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨p,subset_tsupport _ (hactive p hp),rfl⟩
  · exact fun p hp => ⟨chart (i : M) p,⟨p,hp,rfl⟩,rfl⟩
  · rintro y ⟨x,⟨p,hp,rfl⟩,rfl⟩
    have hpe : chart (i : M) p ∈ e.source := (hDs hp).2
    rw [e.left_inv hpe,chartWeight,
      indicator_of_mem ((chart (i : M)).map_source (hDs hp).1),
      (chart (i : M)).left_inv (hDs hp).1]
    exact hactive p hp
  · obtain ⟨χ,hχ,hχc,_,hχs,hχone⟩ := CollarVelocity.compact_cutoff hC e.open_source hCe
    exact ⟨χ,hχ,hχc,hχs,fun x hx => hχone x (hinv ▸ hx)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveGlobalTensor
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of a supported analytic primitive with the square of its
actual global surface phase differential. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.globalPrimitiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.globalPrimitiveFiberSpace
local instance globalPrimitiveDualSmul_r75e2a7_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.globalPrimitiveFiberNormed
local instance globalPrimitiveSectionNormed_r75e2a7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalPrimitiveSectionSpace_r75e2a7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma localized_primitive_tensor_at (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (χ : JetPolynomial.Base → ℝ) (a : SmallModes.Base → ℝ)
    {phi : M → ℝ} {p : M} (hp : p ∈ (chart (i : M)).source)
    (hphi : phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0)) :
    A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)) p =
      (A.outer i p * χ (chart (i : M) p) * (a (surfacePhaseChart (i : M) e p))^2) •
        phaseDifferentialSquare phi p := by
  ext v w
  rw [A.tensorRestore_apply i _ hp,localizedTensorPullback_first_square,map_smul]
  simp only [smul_apply,smul_eq_mul,fiberFromThree_apply,covectorSquare_evaluate]
  rw [← A.phaseFirst_mfderiv i e he hp hphi v,← A.phaseFirst_mfderiv i e he hp hphi w]
  let dv : ℝ := mfderiv planeModel 𝓘(ℝ) phi p v
  let dw : ℝ := mfderiv planeModel 𝓘(ℝ) phi p w
  change A.outer i p * (χ (chart (i : M) p) * (a (baseEquiv (e (chart (i : M) p))))^2 *
    (dv * dw)) =
    (A.outer i p * χ (chart (i : M) p) * (a (baseEquiv (e (chart (i : M) p))))^2) *
      (dv * dw)
  ring

theorem phase_primitive_global_tensor (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) {χ : JetPolynomial.Base → ℝ}
    (hχs : tsupport χ ⊆ e.source) {a : SmallModes.Base → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) {D : Set M}
    (hDs : D ⊆ (surfacePhaseChart (i : M) e).source)
    (hapos : ∀ x, 0 < a x ↔ x ∈ (surfacePhaseChart (i : M) e) '' D)
    {f phi : M → ℝ}
    (haf : ∀ p ∈ D, a (surfacePhaseChart (i : M) e p) = f p)
    (hfzero : ∀ p ∉ D, f p = 0)
    (houter : ∀ p ∈ D, A.outer i p = 1)
    (hone : ∀ p ∈ D, χ (chart (i : M) p) = 1)
    (hphi : ∀ p ∈ D, phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0)) :
    A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)) =
      fun p => (f p)^2 • phaseDifferentialSquare phi p := by
  funext p
  by_cases hpD : p ∈ D
  · rw [A.localized_primitive_tensor_at i e he χ a (hDs hpD).1 (hphi p hpD),
      houter p hpD,hone p hpD,haf p hpD,one_mul,one_mul]
  rw [hfzero p hpD,zero_pow (by decide : 2 ≠ 0),zero_smul]
  by_cases hp : p ∈ (chart (i : M)).source
  · have hzero : localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0])
        (chart (i : M) p) = 0 := by
      by_cases hχ : χ (chart (i : M) p) = 0
      · simp only [localizedTensorPullback,hχ,zero_smul]
      have hep : p ∈ (surfacePhaseChart (i : M) e).source :=
        ⟨hp,hχs (subset_tsupport χ hχ)⟩
      have ha : a (surfacePhaseChart (i : M) e p) = 0 := by
        apply le_antisymm _ (ha0 _)
        apply le_of_not_gt
        intro hpos
        obtain ⟨q,hq,heq⟩ := (hapos _).mp hpos
        have hqp : q = p := (surfacePhaseChart (i : M) e).injOn (hDs hq) hep heq
        exact hpD (hqp ▸ hq)
      rw [localizedTensorPullback_first_square]
      change (χ (chart (i : M) p) * (a (surfacePhaseChart (i : M) e p))^2) • _ = 0
      rw [ha,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_smul]
    ext v w
    rw [A.tensorRestore_apply i _ hp,hzero,map_zero]
    simp
  · have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (A.outer_support i h))
    simp only [bundleRestore,ho,zero_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ConstructedPrimitiveSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the smooth amplitude and the exact localized tensor of an
actual surface primitive, retaining its precise geometric support. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.constructedSupportDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.constructedSupportFiberSpace
local instance constructedSupportDualSmul_r75e2a7_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.constructedSupportFiberNormed
local instance constructedSupportSectionNormed_r75e2a7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance constructedSupportSectionSpace_r75e2a7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem constructed_primitive_support (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hDs : closure D ⊆ (surfacePhaseChart (i : M) e).source)
    (hactive : ∀ p ∈ closure D, A.weight i p ≠ 0)
    {f phi : M → ℝ} (hf : ContMDiff planeModel 𝓘(ℝ) ∞ f)
    (hf0 : ∀ p, 0 ≤ f p) (hfpos : ∀ p, 0 < f p ↔ p ∈ D)
    (hphi : ∀ p ∈ D, phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0)) :
    ∃ K : Set JetPolynomial.Base, IsCompact K ∧ K ⊆ e.target ∧
      A.phaseSurfaceSupport i e K = closure D ∧
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) ∧
      (∀ p ∈ closure D, e (chart (i : M) p) ∈ K) ∧
      (∀ y ∈ K, A.chartWeight i (e.symm y) ≠ 0) ∧
      ∃ χ : JetPolynomial.Base → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ e.source ∧ (∀ x ∈ e.symm '' K, χ x = 1) ∧
      ∃ a : SmallModes.Base → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 ≤ a x) ∧
        (∀ p ∈ (surfacePhaseChart (i : M) e).source, a (surfacePhaseChart (i : M) e p) = f p) ∧
        (∀ x, 0 < a x ↔ x ∈ (surfacePhaseChart (i : M) e) '' D) ∧
        (∀ x ∉ K, a (baseEquiv x) = 0) ∧
        A.bundleRestore A.tensorTriv i
          (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)) =
          fun p => (f p)^2 • phaseDifferentialSquare phi p := by
  have hDc : IsCompact (closure D) := isClosed_closure.isCompact
  obtain ⟨K,hK,hKt,hSupport,hKA,hDK,hactiveK,χ,hχ,hχc,hχs,hχone⟩ :=
    A.compact_primitive_support i e he hDc hDs hactive
  obtain ⟨a,ha,ha0,haf,hapos,_haoff⟩ := surface_phase_amplitude (i : M) e hi hDc hDs hf hf0 hfpos
  have hfzero (p : M) (hp : p ∉ D) : f p = 0 :=
    le_antisymm (le_of_not_gt (fun hh => hp ((hfpos p).mp hh))) (hf0 p)
  have hχD (p : M) (hp : p ∈ D) : χ (chart (i : M) p) = 1 := by
    have hpe : chart (i : M) p ∈ e.source := (hDs (subset_closure hp)).2
    apply hχone
    exact ⟨e (chart (i : M) p),hDK p (subset_closure hp),e.left_inv hpe⟩
  have hzero (x : JetPolynomial.Base) (hx : x ∉ K) : a (baseEquiv x) = 0 := by
    apply le_antisymm _ (ha0 _)
    apply le_of_not_gt
    intro hpos
    obtain ⟨p,hp,heq⟩ := (hapos _).mp hpos
    apply hx
    have heqx := congrArg baseEquiv.symm heq
    change baseEquiv.symm (baseEquiv (e (chart (i : M) p))) = baseEquiv.symm (baseEquiv x) at heqx
    have hh : e (chart (i : M) p) = x := by
      simpa only [baseEquiv.symm_apply_apply] using heqx
    exact hh ▸ hDK p (subset_closure hp)
  refine ⟨K,hK,hKt,hSupport,hKA,hDK,hactiveK,χ,hχ,hχc,hχs,hχone,a,ha,ha0,haf,hapos,hzero,?_⟩
  exact A.phase_primitive_global_tensor i e he hχs ha0
    (fun _ hp => hDs (subset_closure hp)) hapos (fun p hp => haf p (hDs (subset_closure hp)))
    hfzero (fun p hp => A.outer_one i p (subset_tsupport _ (hactive p (subset_closure hp)))) hχD hphi

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveDomainWindow
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact coordinate window and exact support location used by the
analytic primitive theorem. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates

lemma phaseWindow_closure {V : Set SmallModes.Base} (hV : IsOpen V) :
    closure (phaseWindow hV : Set JetPolynomial.Base) = baseEquiv ⁻¹' closure V :=
  (baseEquiv.toHomeomorph.preimage_closure V).symm

lemma phaseWindow_compact {V : Set SmallModes.Base} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) : IsCompact (closure (phaseWindow hV : Set JetPolynomial.Base)) := by
  rw [phaseWindow_closure]
  exact baseEquiv.toHomeomorph.isCompact_preimage.mpr hVc

lemma phaseWindow_real_closure {V : Set SmallModes.Base} (hV : IsOpen V) :
    baseEquiv '' closure (phaseWindow hV : Set JetPolynomial.Base) = closure V := by
  rw [phaseWindow_closure]
  exact Set.image_preimage_eq _ baseEquiv.surjective

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseSupport_image_contains (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set JetPolynomial.Base} (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {y : JetPolynomial.Base} (hy : y ∈ K) :
    ∃ p ∈ A.phaseSurfaceSupport i e K, surfacePhaseChart (i : M) e p = baseEquiv y := by
  obtain ⟨p,hp,hpy⟩ := hKA (mem_image_of_mem e.symm hy)
  have hps := A.weight_support i hp
  refine ⟨p,?_,?_⟩
  · apply subset_closure
    exact ⟨e.symm y,mem_image_of_mem e.symm hy,by rw [← hpy,(chart (i : M)).left_inv hps]⟩
  · change baseEquiv (e (chart (i : M) p)) = baseEquiv y
    rw [hpy,e.right_inv (hKt hy)]

lemma phaseSupport_window (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set JetPolynomial.Base} (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {V : Set SmallModes.Base} (hV : IsOpen V)
    (hCV : (surfacePhaseChart (i : M) e) '' A.phaseSurfaceSupport i e K ⊆ V) :
    K ⊆ (phaseWindow hV : Set JetPolynomial.Base) := by
  intro y hy
  obtain ⟨p,hp,heq⟩ := A.phaseSupport_image_contains i e hKt hKA hy
  change baseEquiv y ∈ V
  rw [← heq]
  exact hCV (mem_image_of_mem _ hp)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SupportedPrimitivePatch
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed support and geometric domain of one actual primitive.
Every field is data or a local identity needed by the analytic realization. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchFiberSpace
local instance patchDualSmul_r75e2a7_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchFiberNormed
local instance patchSectionNormed_r75e2a7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance patchSectionSpace_r75e2a7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem supported_primitive_patch (i : A.centers) {F : M → Space}
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (hcover : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {D : Set M} (hDs : closure D ⊆ (surfacePhaseChart (i : M) e).source)
    (hactive : ∀ p ∈ closure D, A.weight i p ≠ 0)
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p) (hamppos : ∀ p, 0 < amp p ↔ p ∈ D)
    (hphi : ∀ p ∈ D, phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0))
    {V U : Set SmallModes.Base} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hDV : (surfacePhaseChart (i : M) e) '' closure D ⊆ V)
    (heV : MapsTo e e.source (baseEquiv ⁻¹' V))
    (hU : IsOpen U) (hVU : closure V ⊆ U)
    {n : SmallModes.Base → NormalFrame.Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x))
    (hN : ∀ x ∈ U, coordDeriv dx (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n x = 0 ∧
      coordDeriv dy (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n x = 0 ∧ n x ⬝ᵥ n x = 1)
    (hH : ∀ x ∈ U, 0 < coordinateMetricHessian
      (inducedCoordinateMetric (A.phaseRealChartMap i e.symm F)) Prod.fst x dy dy)
    (hb : ∀ x ∈ closure V \ (surfacePhaseChart (i : M) e) '' D,
      realSecondForm (A.phaseRealChartMap i e.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy x) ≠ -n x) :
    Nonempty (SupportedPrimitivePatch A i e F amp phi D) := by
  obtain ⟨K,hK,hKt,hs,hKA,hDK,hKa,χ,hχ,hχc,hχs,hχone,a,ha,ha0,haf,hapos,haoff,htensor⟩ :=
    A.constructed_primitive_support i e he hi hDs hactive hamp hamp0 hamppos hphi
  have hKS : K ⊆ (phaseWindow hV : Set JetPolynomial.Base) := by
    apply A.phaseSupport_window i e hKt hKA hV
    rwa [hs]
  refine ⟨{
    phase_smooth := he, inverse_smooth := hi,
    outer := houter, cover := hcover, cutoff := χ, cutoff_smooth := hχ,
    cutoff_compact := hχc, cutoff_source := hχs, amplitude := a, amplitude_smooth := ha,
    amplitude_nonneg := ha0, amplitude_surface := haf, amplitude_positive := hapos,
    compactSet := K, compact := hK, target := hKt, support := hs, inverse_support := hKA,
    cutoff_one := hχone, amplitude_off := haoff, compact_active := hKa,
    closed_coordinates := hDK, source_closed := hDs, active_closed := hactive,
    window := phaseWindow hV, window_compact := phaseWindow_compact hV hVc,
    phase_window := heV, support_window := hKS, region := closure V, region_compact := hVc,
    window_region := ?_, openRegion := U, open_region := hU, region_open := hVU,
    normal := n, normal_smooth := hn, immersion := hI, normal_properties := hN,
    convexity := hH, boundary := ?_, tensor := htensor }⟩
  · rw [phaseWindow_real_closure]
  · intro x hx ha0x
    apply hb x ⟨hx,?_⟩
    intro hin
    have hp := (hapos x).mpr hin
    rw [ha0x] at hp
    exact lt_irrefl _ hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ConstructSupportedPrimitivePatch
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported primitive patch is constructed from the actual immersion,
its preferred normal, metric convexity and the original boundary condition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem construct_supported_primitive_patch (j : B.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D) (hqD : (j : M) ∈ D)
    (hDs : closure D ⊆ (surfacePhaseChart (j : M) e).source)
    {Ω : Set Base} (hΩ : IsOpen Ω)
    (hDΩ : (surfacePhaseChart (j : M) e) '' closure D ⊆ Ω)
    (hΩe : Ω ⊆ (surfacePhaseChart (j : M) e).target)
    (hactive : ∀ x ∈ Ω, B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0)
    {localPhase : Base → ℝ} (hlocalPhase : ContDiff ℝ ∞ localPhase)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart e x).1 = localPhase x)
    (hconvex : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (j : M)) localPhase
        (coordinateChart (j : M) ((surfacePhaseChart (j : M) e).symm x)) v v)
    (hboundary : ∀ x ∈ frontier ((surfacePhaseChart (j : M) e) '' D),
      realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x) ≠ -n.inPhase (j : M) e x)
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p) (hamppos : ∀ p, 0 < amp p ↔ p ∈ D)
    (hphi : ∀ p ∈ D, phi =ᶠ[𝓝 p] (fun q => (e (chart (j : M) q)) 0)) :
    ∃ (A : SmoothingAtlas M) (i : A.centers)
      (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base),
      (i : M) = (j : M) ∧ (∀ x, f x = e x) ∧ (∀ x, f.symm x = e.symm x) ∧
      Nonempty (SupportedPrimitivePatch A i f F amp phi D) := by
  obtain ⟨V,A,i,f,U,hV,hVc,hDV,hVΩ,hij,hfe,hfi,hfs,hfis,hw,houter,hcover,hsource,hDf,
      hU,hVU,_hUΩ,hn,hI,hN,hH,hb⟩ := B.adapted_primitive_geometry j hF n e he hi
    hD hqD hDs hΩ hDΩ hΩe hactive hlocalPhase hphase hconvex hboundary
  have hE : (surfacePhaseChart (i : M) f : M → Base) = surfacePhaseChart (j : M) e := by
    funext p
    simp only [surfacePhaseChart_apply,hij,hfe]
  have hph : (fun q => (f (chart (i : M) q)) 0) = (fun q => (e (chart (j : M) q)) 0) := by
    funext p
    rw [hij,hfe]
  refine ⟨A,i,f,hij,hfe,hfi,?_⟩
  apply A.supported_primitive_patch i f hfs hfis houter hcover hDf
    (fun p hp => (hw p hp).ne') hamp hamp0 hamppos
    (by simpa only [hph] using hphi) hV hVc
    (by simpa only [hE] using hDV) hsource hU hVU hn hI hN hH
  simpa only [hE] using hb

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularSupportedPrimitivePatch
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic support and all local geometric data for an actual circular
primitive are constructed from the preserved boundary normal and metric bound. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

theorem supported_circular_patch
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F) {r r₀ R : ℝ} (hr : 0 < r)
    (hrr₀ : r^2 < r₀^2) (hrR : r < R)
    (hpos : ∀ p, 0 < B.weight c.index p ↔ p ∈ circularCoordinateDisk (c.index : M) r₀)
    (hreg : circularCoordinateRegion (c.index : M) r ⊆ (coordinateChart (c.index : M)).target)
    (hfront : c.carrier = circularBoundary (c.index : M) r)
    (hcover : ∀ x ∈ circularCoordinateRegion (c.index : M) r, baseEquiv.symm x ∈ c.phase.source)
    {localPhase : Base → ℝ} (hlocalPhase : ContDiff ℝ ∞ localPhase)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart c.phase x).1 = localPhase x)
    (hconvex : ∀ p ∈ tsupport (B.weight c.index),
      ‖coordinateChart (c.index : M) p-coordinateChart (c.index : M) (c.index : M)‖ ≤ R →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g (c.index : M))
        localPhase (coordinateChart (c.index : M) p) v v)
    (hboundary : ∀ p ∈ c.carrier, c.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c.second F p))
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p)
    (hamppos : ∀ p, 0 < amp p ↔ p ∈ circularCoordinateDisk (c.index : M) r)
    (hphi : ∀ p ∈ circularCoordinateDisk (c.index : M) r,
      phi =ᶠ[𝓝 p] (fun q => (c.phase (chart (c.index : M) q)) 0)) :
    ∃ (A : SmoothingAtlas M) (i : A.centers)
      (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base),
      (i : M) = (c.index : M) ∧ (∀ x, e x = c.phase x) ∧ (∀ x, e.symm x = c.phase.symm x) ∧
      Nonempty (SupportedPrimitivePatch A i e F amp phi (circularCoordinateDisk (c.index : M) r)) := by
  let D := circularCoordinateDisk (c.index : M) r
  have hD : IsOpen D := circularCoordinateDisk_open (c.index : M) r
  have hDs : closure D ⊆ (surfacePhaseChart (c.index : M) c.phase).source :=
    B.circular_closed_disk_phase_source c.index hr hreg c.phase hcover
  have hDj : (c.index : M) ∈ D := by
    refine ⟨?_,?_⟩
    · rw [coordinateChart_source]
      exact mem_chart_source Plane (c.index : M)
    · change circularRadiusSquared (coordinateChart (c.index : M) (c.index : M))
        (coordinateChart (c.index : M) (c.index : M)) < r^2
      simp only [circularRadiusSquared,sub_self,zero_pow (by decide : 2 ≠ 0),add_zero]
      exact sq_pos_of_pos hr
  have hclosed (p : M) (hp : p ∈ closure D) :
      p ∈ (coordinateChart (c.index : M)).source ∧
        circularRadiusSquared (coordinateChart (c.index : M) (c.index : M))
          (coordinateChart (c.index : M) p) ≤ r^2 := by
    have hc : closure D = circularDiskClosure (c.index : M) r :=
      circularCoordinateDisk_closure (c.index : M) hr hreg
    exact (circularDiskClosure_iff (c.index : M) hreg p).mp (hc ▸ hp)
  have hw (p : M) (hp : p ∈ closure D) : B.weight c.index p ≠ 0 := by
    apply ne_of_gt ((hpos p).mpr ?_)
    exact ⟨(hclosed p hp).1,((hclosed p hp).2).trans_lt hrr₀⟩
  have hsmall (p : M) (hp : p ∈ closure D) :
      ‖coordinateChart (c.index : M) p-coordinateChart (c.index : M) (c.index : M)‖ < R := by
    have hh := circularRadiusSquared_le_norm (hclosed p hp).2
    rw [abs_of_pos hr] at hh
    exact hh.trans_lt hrR
  obtain ⟨Ω,hΩ,hDΩ,hΩe,hΩprop⟩ := B.phase_metric_region c.index c.phase hDs hw hsmall
  have hcv : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (c.index : M)) localPhase
        (coordinateChart (c.index : M) ((surfacePhaseChart (c.index : M) c.phase).symm x)) v v := by
    intro x hx v hv
    exact hconvex _ (subset_tsupport _ (hΩprop x hx).1) (hΩprop x hx).2.le v hv
  have hb := c.frontier_avoidance hD hDs
    (hfront.trans (circularCoordinateDisk_frontier (c.index : M) hr hreg).symm) n hboundary
  exact B.construct_supported_primitive_patch c.index hF n c.phase c.smooth c.inverse_smooth
    hD hDj hDs hΩ hDΩ hΩe (fun x hx => (hΩprop x hx).1)
    hlocalPhase hphase hcv hb hamp hamp0 hamppos hphi

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseCrossingTransversality
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent phase covectors give the nonzero first components of the
actual transported directions at every finite crossing. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SmallModes RealModes SurfaceJetCoordinates PhaseGeometry

namespace PhaseGeometry

lemma firstCoordinateCovector_apply (L : Base →L[ℝ] Base) (v : Base) :
    phaseLinear (firstCoordinateCovector L) v = (L v).1 := by
  have hv : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]
  conv_rhs => rw [hv]
  simp only [map_add,map_smul,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
  change (L dx).1*v.1 + (L dy).1*v.2 = _
  ring

lemma phaseDerivative_fst {T : Base → Base} {x : Base} (hT : DifferentiableAt ℝ T x) :
    phaseDerivative (Prod.fst ∘ T) x = firstCoordinateCovector (fderiv ℝ T x) := by
  have hd := ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp x hT.hasFDerivAt).fderiv
  change fderiv ℝ (Prod.fst ∘ T) x = _ at hd
  rw [phaseDerivative,hd]
  rfl

end PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem phase_crossing_first_nonzero (q₀ q₁ q₂ : M)
    (e₀ e₁ e₂ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he₀ : ContDiff ℝ ∞ e₀) (hi₀ : ContDiff ℝ ∞ e₀.symm)
    (he₁ : ContDiff ℝ ∞ e₁) (hi₁ : ContDiff ℝ ∞ e₁.symm)
    (he₂ : ContDiff ℝ ∞ e₂)
    {p : M} (h₀ : p ∈ (surfacePhaseChart q₀ e₀).source)
    (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (hcross : covectorDet
      (firstCoordinateCovector (fderiv ℝ (surfacePhaseTransition q₀ e₀ q₁ e₁) (surfacePhaseChart q₀ e₀ p)))
      (firstCoordinateCovector (fderiv ℝ (surfacePhaseTransition q₀ e₀ q₂ e₂) (surfacePhaseChart q₀ e₀ p))) ≠ 0) :
    (fderiv ℝ (surfacePhaseTransition q₁ e₁ q₂ e₂) (surfacePhaseChart q₁ e₁ p) dy).1 ≠ 0 := by
  let L₀₁ := fderiv ℝ (surfacePhaseTransition q₀ e₀ q₁ e₁) (surfacePhaseChart q₀ e₀ p)
  let L₀₂ := fderiv ℝ (surfacePhaseTransition q₀ e₀ q₂ e₂) (surfacePhaseChart q₀ e₀ p)
  let L₁₀ := fderiv ℝ (surfacePhaseTransition q₁ e₁ q₀ e₀) (surfacePhaseChart q₁ e₁ p)
  let v := L₁₀ dy
  have hv : v ≠ 0 := by
    have hI := surfacePhaseTransition_fderiv_injective q₁ q₀ e₁ e₀ he₁ hi₁ he₀ hi₀ h₁ h₀
    intro hz
    have hh : (dy : Base) = 0 := hI (hz.trans (map_zero _).symm)
    exact (show (dy : Base) ≠ 0 by simp [dy]) hh
  have hid := surfacePhaseTransition_fderiv_cocycle q₁ q₀ q₁ e₁ e₀ e₁ hi₁ he₀ hi₀ he₁ h₁ h₀ h₁
  rw [surfacePhaseTransition_self_fderiv q₁ e₁ ((surfacePhaseChart q₁ e₁).map_source h₁)] at hid
  have hv₁ : phaseLinear (firstCoordinateCovector L₀₁) v = 0 := by
    rw [firstCoordinateCovector_apply]
    have hh := congrArg (fun L : Base →L[ℝ] Base => (L dy).1) hid
    exact hh.symm
  have hn := phaseLinear_ne_zero_on_kernel hcross hv hv₁
  rw [firstCoordinateCovector_apply] at hn
  have hc := surfacePhaseTransition_fderiv_cocycle q₁ q₀ q₂ e₁ e₀ e₂ hi₁ he₀ hi₀ he₂ h₁ h₀ h₂
  rw [hc]
  exact hn

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_GenericPhaseCrossing
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic covectors selected in ordinary coordinates are the first
rows of the actual phase transitions. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates RealModes SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma phaseTransition_refl_first (q r : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (phi : M → ℝ) (hphi : ∀ p, (surfacePhaseChart r e p).1 = phi p) :
    Prod.fst ∘ surfacePhaseTransition q (OpenPartialHomeomorph.refl JetPolynomial.Base) r e =
      phi ∘ (coordinateChart q).symm := by
  funext x
  change (surfacePhaseChart r e
    ((surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base)).symm x)).1 = _
  rw [surfacePhaseChart_refl_symm_apply,hphi]
  rfl

lemma phaseTransition_refl_covector (q r : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (phi : M → ℝ)
    (hphi : ∀ p, (surfacePhaseChart r e p).1 = phi p)
    {p : M} (hq : p ∈ (coordinateChart q).source)
    (hr : p ∈ (surfacePhaseChart r e).source) :
    firstCoordinateCovector
      (fderiv ℝ (surfacePhaseTransition q (OpenPartialHomeomorph.refl JetPolynomial.Base) r e)
        (coordinateChart q p)) =
      phaseDerivative (phi ∘ (coordinateChart q).symm) (coordinateChart q p) := by
  have hq' : p ∈ (surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base)).source := by
    rwa [surfacePhaseChart_refl_source]
  have hs := surfacePhaseTransition_source q r (OpenPartialHomeomorph.refl JetPolynomial.Base) e hq' hr
  have ht := ((surfacePhaseTransition_smooth q (OpenPartialHomeomorph.refl JetPolynomial.Base)
    contDiff_id r e he) _ hs).contDiffAt
      ((surfacePhaseTransition q (OpenPartialHomeomorph.refl JetPolynomial.Base) r e).open_source.mem_nhds hs)
  have hh := phaseDerivative_fst (ht.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  rw [phaseTransition_refl_first q r e phi hphi] at hh
  exact hh.symm

omit [IsManifold planeModel ∞ M] in
lemma centeredPhase_first (q : M) (ell : Base) (L : ℝ)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ∀ x, (baseEquiv (e x)).1 =
      centeredConvexPhase ell L (coordinateChart q q) (baseEquiv x)) (p : M) :
    (surfacePhaseChart q e p).1 = centeredAtlasPhase q ell L p := by
  rw [surfacePhaseChart_apply,he]
  rfl

 theorem generic_phase_crossing_first_nonzero (q q₁ q₂ : M)
    (e₁ e₂ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he₁ : ContDiff ℝ ∞ e₁) (hi₁ : ContDiff ℝ ∞ e₁.symm)
    (he₂ : ContDiff ℝ ∞ e₂)
    (phi₁ phi₂ : M → ℝ)
    (hphi₁ : ∀ p, (surfacePhaseChart q₁ e₁ p).1 = phi₁ p)
    (hphi₂ : ∀ p, (surfacePhaseChart q₂ e₂ p).1 = phi₂ p)
    {p : M} (hq : p ∈ (coordinateChart q).source)
    (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (hcross : covectorDet
      (phaseDerivative (phi₁ ∘ (coordinateChart q).symm) (coordinateChart q p))
      (phaseDerivative (phi₂ ∘ (coordinateChart q).symm) (coordinateChart q p)) ≠ 0) :
    (fderiv ℝ (surfacePhaseTransition q₁ e₁ q₂ e₂) (surfacePhaseChart q₁ e₁ p) dy).1 ≠ 0 := by
  apply phase_crossing_first_nonzero q q₁ q₂
    (OpenPartialHomeomorph.refl JetPolynomial.Base) e₁ e₂
    contDiff_id contDiff_id he₁ hi₁ he₂
    (by rwa [surfacePhaseChart_refl_source]) h₁ h₂
  rw [surfacePhaseChart_refl_apply,
    phaseTransition_refl_covector q q₁ e₁ he₁ phi₁ hphi₁ hq h₁,
    phaseTransition_refl_covector q q₂ e₂ he₂ phi₂ hphi₂ hq h₂]
  exact hcross

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PreparedPhaseCrossingSlopes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic phase selection makes each relevant transported boundary
direction nonvertical, and a finite crossing set has a fixed slope bound. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {B : SmoothingAtlas M}
namespace PhaseBoundaryCurve

lemma directionIn_first_ne_of_covectors (c d : PhaseBoundaryCurve B)
    (q : M) (phi psi : M → ℝ)
    (hc : ∀ p, (surfacePhaseChart (c.index : M) c.phase p).1 = phi p)
    (hd : ∀ p, (surfacePhaseChart (d.index : M) d.phase p).1 = psi p)
    {p : M} (hq : p ∈ (coordinateChart q).source)
    (hp : p ∈ c.carrier) (hps : p ∈ (surfacePhaseChart (d.index : M) d.phase).source)
    (hind : covectorDet
      (phaseDerivative (phi ∘ (coordinateChart q).symm) (coordinateChart q p))
      (phaseDerivative (psi ∘ (coordinateChart q).symm) (coordinateChart q p)) ≠ 0) :
    (c.directionIn d p).1 ≠ 0 :=
  generic_phase_crossing_first_nonzero q (c.index : M) (d.index : M)
    c.phase d.phase c.smooth c.inverse_smooth d.smooth
    phi psi hc hd hq (c.source hp) hps hind

end PhaseBoundaryCurve

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPatchDefiners
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate-circle defining functions in a nonlinear phase chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma circular_boundary_phase_definer_at (q b : M) (ell : Base) (L r : ℝ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hphase : ∀ x, (e x).1 = centeredConvexPhase ell L (coordinateChart q q) x)
    {p : Base} (hp : p ∈ e.target) (hdom : e.symm p ∈ (coordinateChart q).target)
    (hboundary : (coordinateChart q).symm (e.symm p) ∈ circularBoundary b r)
    (htrans : circularPhaseDerivative q b ell L ((coordinateChart q).symm (e.symm p)) ≠ 0) :
    ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧ ∃ g : Base → ℝ,
      ContDiffOn ℝ ∞ g N ∧
      (∀ x ∈ N, (coordinateChart q).symm (e.symm x) ∈ circularBoundary b r → g x = 0) ∧
      fderiv ℝ g p dy ≠ 0 := by
  let m : Base → M := fun x => (coordinateChart q).symm (e.symm x)
  let f : Base → Base := coordinateTransition b q ∘ e.symm
  let φ : Base → ℝ := centeredAtlasPhase q ell L ∘ (coordinateChart b).symm
  let ρ : Base → ℝ := circularRadiusSquared (coordinateChart b b)
  let N : Set Base := e.target ∩ e.symm ⁻¹' (coordinateTransition b q).source
  have hN : IsOpen N := e.open_target.inter
    ((coordinateTransition b q).open_source.preimage hi.continuous)
  have hxp : e.symm p ∈ (coordinateTransition b q).source :=
    ⟨hdom,hboundary.1⟩
  have hpN : p ∈ N := ⟨hp,hxp⟩
  have hf : ContDiffOn ℝ ∞ f N :=
    (coordinateTransition_smoothOn b q).comp hi.contDiffOn (fun _ hx => hx.2)
  have hfp : DifferentiableAt ℝ f p := (hf.contDiffAt (hN.mem_nhds hpN)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hqm : m p ∈ (coordinateChart q).source := (coordinateChart q).map_target hxp.1
  have hfpeq : f p = coordinateChart b (m p) := rfl
  have hback : f p ∈ (coordinateTransition q b).source := by
    rw [hfpeq]
    exact coordinateTransition_mem_chart q b hboundary.1 hqm
  have hφ : DifferentiableAt ℝ φ (f p) :=
    ((centeredConvexPhase_smooth ell L (coordinateChart q q)).differentiable (by simp) _).comp _
      (((coordinateTransition_smoothOn q b).contDiffAt
        ((coordinateTransition q b).open_source.mem_nhds hback)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hcomp : φ ∘ f =ᶠ[𝓝 p] Prod.fst := by
    filter_upwards [hN.mem_nhds hpN] with x hx
    have hbx : m x ∈ (coordinateChart b).source := hx.2.2
    change centeredConvexPhase ell L (coordinateChart q q)
      (coordinateChart q ((coordinateChart b).symm (coordinateChart b (m x)))) = x.1
    rw [(coordinateChart b).left_inv hbx]
    change centeredConvexPhase ell L (coordinateChart q q)
      (coordinateChart q ((coordinateChart q).symm (e.symm x))) = x.1
    rw [(coordinateChart q).right_inv hx.2.1,← hphase,e.right_inv hx.1]
  have hdet : coordDet (fderiv ℝ f p) ≠ 0 := by
    rw [show f = coordinateTransition b q ∘ e.symm from rfl,
      fderiv_comp p (((coordinateTransition_smoothOn b q).contDiffAt
        ((coordinateTransition b q).open_source.mem_nhds hxp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        (hi.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p),coordDet_comp]
    exact mul_ne_zero (coordinateTransition_det_ne b q hxp)
      (coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source hi.contDiffOn
        he.contDiffOn (fun _ hx => e.map_target hx) (fun x hx => e.right_inv hx) hp)
  have hangle : phaseLinear (phaseDerivative φ (f p))
      (circularAngularTangent (coordinateChart b b) (f p)) ≠ 0 := htrans
  have hcross : covectorDet (phaseDerivative φ (f p)) (phaseDerivative ρ (f p)) ≠ 0 := by
    rw [show ρ = circularRadiusSquared (coordinateChart b b) from rfl,
      circular_radius_phase_determinant]
    exact mul_ne_zero (by norm_num) hangle
  have hd := phase_chart_transverse_definer_at hφ
    ((circularRadiusSquared_smooth (coordinateChart b b)).differentiable (by simp) _) hfp
    hcomp hdet hcross
  refine ⟨N,hN,hpN,fun x => ρ (f x)-r^2,
    ((circularRadiusSquared_smooth (coordinateChart b b)).comp_contDiffOn hf).sub contDiffOn_const,
    ?_,?_⟩
  · intro x hx hb
    exact sub_eq_zero.mpr hb.2
  · change fderiv ℝ ((circularRadiusSquared (coordinateChart b b) ∘ f) - (fun _ => r^2)) p dy ≠ 0
    rw [fderiv_sub (((circularRadiusSquared_smooth (coordinateChart b b)).comp_contDiffOn hf).contDiffAt
      (hN.mem_nhds hpN) |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (differentiableAt_const _)]
    simpa using hd



variable [T2Space M] {ι : Type*} [Fintype ι]

theorem circular_phase_defining_family_local (q : M) (ell : Base) (L R : ℝ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hphase : ∀ x, (e x).1 = centeredConvexPhase ell L (coordinateChart q q) x)
    (hQ : circularCoordinateRegion q R ⊆ (coordinateChart q).target)
    (hcover : circularDiskClosure q R ⊆ ((coordinateChart q).trans e).source)
    (center : ι → M) (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hreg : ∀ j, circularCoordinateRegion (center j) (r j) ⊆ (coordinateChart (center j)).target)
    (E₀ : Set M) (hE₀ : E₀.Finite)
    (hcross : ∀ j k, j ≠ k → circularBoundary (center j) (r j) ∩ circularBoundary (center k) (r k) ⊆ E₀)
    (htan : ∀ j, (circularPhaseTangencies q (center j) ell L (r j) R).Finite) :
    let E := (coordinateChart q).trans e
    let Curves := fun j => E '' (circularBoundary (center j) (r j) ∩ circularDiskClosure q R)
    (∀ j, IsCompact (Curves j)) ∧ ∃ P : Set Base, P.Finite ∧
      ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
        ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧
          (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p dy ≠ 0 := by
  classical
  let E := (coordinateChart q).trans e
  let C := fun j => circularBoundary (center j) (r j)
  let S := circularDiskClosure q R
  let Curves := fun j => E '' (C j ∩ S)
  let Z := E₀ ∪ ⋃ j, circularPhaseTangencies q (center j) ell L (r j) R
  let P := E '' Z
  have hZ : Z.Finite := hE₀.union (Set.finite_iUnion htan)
  have hP : P.Finite := hZ.image E
  have hS : IsCompact S := circularDiskClosure_compact q R hQ
  have hC (j : ι) : IsCompact (C j) := circularBoundary_compact (center j) (hr j) (hreg j)
  have hcompact (j : ι) : IsCompact (Curves j) :=
    ((hC j).inter hS).image_of_continuousOn (E.continuousOn.mono (fun _ hp => hcover hp.2))
  have hback {x : Base} (hx : x ∈ ⋃ j, Curves j) : x ∈ E.target ∧ E.symm x ∈ S := by
    obtain ⟨j,y,hy,rfl⟩ := mem_iUnion.mp hx
    exact ⟨E.map_source (hcover hy.2),by rw [E.left_inv (hcover hy.2)]; exact hy.2⟩
  have hpoint {j : ι} {x : Base} (hx : x ∈ Curves j) : E.symm x ∈ C j := by
    obtain ⟨y,hy,rfl⟩ := hx
    rw [E.left_inv (hcover hy.2)]
    exact hy.1
  refine ⟨hcompact,P,hP,?_⟩
  apply finite_boundary_local_definers C (fun j => (hC j).isClosed) E.symm
  · intro p hp
    exact E.continuousAt_symm (hback hp).1
  · intro p hp
    obtain ⟨j,hj⟩ := mem_iUnion.mp hp
    exact ⟨j,hpoint hj⟩
  · intro j k hjk p hp hpj hpk
    have hz : E.symm p ∈ Z := Or.inl (hcross j k hjk ⟨hpj,hpk⟩)
    exact ⟨E.symm p,hz,E.right_inv (hback hp).1⟩
  · intro j p hp hpj
    have hpE : p ∈ E.target := (hback hp.1).1
    have hpT : p ∈ e.target := hpE.1
    have hnt : circularPhaseDerivative q (center j) ell L (E.symm p) ≠ 0 := by
      intro hz
      apply hp.2
      refine ⟨E.symm p,Or.inr (mem_iUnion.mpr ⟨j,?_⟩),E.right_inv hpE⟩
      exact ⟨⟨hpj,(hback hp.1).2⟩,hz⟩
    exact circular_boundary_phase_definer_at q (center j) ell L (r j) e he hi hphase
      hpT hpE.2 hpj hnt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitivePatchDefiners
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic circular tangencies supply the actual patch's local definers. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {A B : SmoothingAtlas M} {i : A.centers}
  {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
  {F : M → Space} {amp phi : M → ℝ} {D : Set M}
namespace SupportedPrimitivePatch

lemma circular_definers (d : SupportedPrimitivePatch A i e F amp phi D)
    (ell : Base) (L R : ℝ) (hR : 0 < R)
    (hD : D = circularCoordinateDisk (i : M) R)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart e x).1 =
      centeredConvexPhase ell L (coordinateChart (i : M) i) x)
    (hreg : circularCoordinateRegion (i : M) R ⊆ (coordinateChart (i : M)).target)
    {ι : Type*} [Fintype ι] (curves : ι → PhaseBoundaryCurve B)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hcarrier : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (r j))
    (hregions : ∀ j, circularCoordinateRegion ((curves j).index : M) (r j) ⊆
      (coordinateChart ((curves j).index : M)).target)
    (E₀ : Set M) (hE₀ : E₀.Finite)
    (hcross : ∀ j k, j ≠ k → (curves j).carrier ∩ (curves k).carrier ⊆ E₀)
    (htan : ∀ j, (circularPhaseTangencies (i : M) ((curves j).index : M)
      ell L (r j) R).Finite) :
    ∃ P : Set Base, P.Finite ∧ ∀ p ∈ (⋃ j, d.curve (curves j)) \ P,
      ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧ ∃ f : Base → ℝ,
        ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ (⋃ j, d.curve (curves j)) ∩ N, f x = 0) ∧
        fderiv ℝ f p dy ≠ 0 := by
  have hcl : closure D = circularDiskClosure (i : M) R := by
    rw [hD,circularCoordinateDisk_closure (i : M) hR hreg]
  have hc : circularDiskClosure (i : M) R ⊆
      ((coordinateChart (i : M)).trans (JetPolynomial.realPhaseChart e)).source := by
    rw [← surfacePhaseChart_real_source,← hcl]
    exact d.source_closed
  have hC (j : ι) : d.curve (curves j) =
      ((coordinateChart (i : M)).trans (JetPolynomial.realPhaseChart e)) ''
        (circularBoundary ((curves j).index : M) (r j) ∩ circularDiskClosure (i : M) R) := by
    change (surfacePhaseChart (i : M) e) '' ((curves j).carrier ∩ closure D) = _
    rw [hcarrier,hcl]
    congr 1
    funext p
    exact surfacePhaseChart_real_apply (i : M) p e
  obtain ⟨_,P,hP,hlocal⟩ := circular_phase_defining_family_local (i : M) ell L R
    (JetPolynomial.realPhaseChart e) (JetPolynomial.realPhaseChart_smooth e d.phase_smooth)
    (JetPolynomial.realPhaseChart_symm_smooth e d.inverse_smooth) hphase hreg hc
    (fun j => ((curves j).index : M)) r hr hregions E₀ hE₀
    (fun j k hjk => by simpa only [← hcarrier] using hcross j k hjk) htan
  refine ⟨P,hP,?_⟩
  simpa only [hC] using hlocal

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryMetricStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact realization of an actual circular primitive from the fixed
metric convexity estimate and preserved boundary-normal condition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

theorem realize_circular_boundary_metric
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F) {r r₀ R : ℝ} (hr : 0 < r)
    (hrr₀ : r^2 < r₀^2) (hrR : r < R)
    (hpos : ∀ p, 0 < B.weight c.index p ↔ p ∈ circularCoordinateDisk (c.index : M) r₀)
    (hreg : circularCoordinateRegion (c.index : M) r ⊆ (coordinateChart (c.index : M)).target)
    (hfront : c.carrier = circularBoundary (c.index : M) r)
    (hcover : ∀ x ∈ circularCoordinateRegion (c.index : M) r, baseEquiv.symm x ∈ c.phase.source)
    (ell : Base) (L : ℝ)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart c.phase x).1 =
      centeredConvexPhase ell L (coordinateChart (c.index : M) c.index) x)
    (hconvex : ∀ p ∈ tsupport (B.weight c.index),
      ‖coordinateChart (c.index : M) p-coordinateChart (c.index : M) (c.index : M)‖ ≤ R →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g (c.index : M))
        (centeredConvexPhase ell L (coordinateChart (c.index : M) c.index))
        (coordinateChart (c.index : M) p) v v)
    (hboundary : ∀ p ∈ c.carrier, c.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c.second F p))
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p)
    (hamppos : ∀ p, 0 < amp p ↔ p ∈ circularCoordinateDisk (c.index : M) r)
    (hphi : ∀ p ∈ circularCoordinateDisk (c.index : M) r,
      phi =ᶠ[𝓝 p] (fun q => (c.phase (chart (c.index : M) q)) 0))
    {ι : Type*} [Fintype ι] (curves : ι → PhaseBoundaryCurve B) (radii : ι → ℝ)
    (hradii : ∀ j, 0 < radii j)
    (hcarriers : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (radii j))
    (hregions : ∀ j, circularCoordinateRegion ((curves j).index : M) (radii j) ⊆
      (coordinateChart ((curves j).index : M)).target)
    (hpair : ∀ j k, j ≠ k → ((curves j).carrier ∩ (curves k).carrier).Finite)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅)
    (hEf : Disjoint (boundaryCrossingSet curves univ) c.carrier)
    (hgeom : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n)
    (hfrontGeom : ∀ j p, p ∈ (curves j).carrier ∩ c.carrier →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < c.crossing (curves j) F p)
    (hfirst : ∀ j p, p ∈ boundaryCrossingSet curves univ ∩ circularCoordinateDisk (c.index : M) r →
      p ∈ (curves j).carrier → ((curves j).directionIn c p).1 ≠ 0)
    (htan : ∀ j, (circularPhaseTangencies (c.index : M) ((curves j).index : M)
      ell L (radii j) r).Finite)
    (data : MetricGoodPhaseData g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W, FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) W N := by
  obtain ⟨A,i,e,hi,he,_hinverse,⟨d⟩⟩ := c.supported_circular_patch hF n hr hrr₀ hrR
    hpos hreg hfront hcover (centeredConvexPhase_smooth ell L _) hphase hconvex
    hboundary hamp hamp0 hamppos hphi
  have hdisk : circularCoordinateDisk (c.index : M) r = circularCoordinateDisk (i : M) r := by rw [hi]
  have hphase' : ∀ x, (JetPolynomial.realPhaseChart e x).1 =
      centeredConvexPhase ell L (coordinateChart (i : M) i) x := by
    intro x
    rw [hi]
    change (baseEquiv (e (baseEquiv.symm x))).1 = _
    rw [he]
    exact hphase x
  obtain ⟨P,hP,hlocal⟩ := d.circular_definers ell L r hr hdisk hphase'
    (by simpa only [hi] using hreg) curves radii hradii hcarriers hregions
    (boundaryCrossingSet curves univ) (boundaryCrossingSet_finite curves univ hpair)
    (fun j k hjk p hp => boundaryCrossingSet_pair curves (mem_univ _) (mem_univ _) hjk hp.1 hp.2)
    (by simpa only [hi] using htan)
  have hcf : c.carrier = frontier (circularCoordinateDisk (c.index : M) r) :=
    hfront.trans (circularCoordinateDisk_frontier (c.index : M) hr hreg).symm
  apply d.boundary_step c hi he curves hpair htriple
    (circularCoordinateDisk_open _ _) (circularCoordinateDisk_regular _ hr hreg) hcf
    (by rwa [← hcf]) data hF n hgeom hboundary
    (by simpa only [← hcf] using hfrontGeom) ?_ hP hlocal h htarget
  intro j p hp hpj
  rw [surfacePhaseTransition_target_congr ((curves j).index : M) (i : M) (c.index : M)
    hi (curves j).phase e c.phase he]
  exact hfirst j p hp hpj

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PreparedCircularDirections
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chosen generic phase covectors give nonvertical remaining directions
at every crossing inside the current primitive disk. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompactSpace M] [T2Space M] [Fintype ι] [DecidableEq ι] in
lemma boundaryCrossingSet_eq_circular (curves : ι → PhaseBoundaryCurve B) (r : ι → ℝ)
    (hc : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (r j)) :
    boundaryCrossingSet curves univ = circularCrossingSet (fun j => ((curves j).index : M)) r := by
  ext p
  constructor
  · rintro ⟨j,_,k,_,hjk,hj,hk⟩
    exact mem_iUnion.mpr ⟨⟨(j,k),hjk⟩,by rw [← hc j,← hc k]; exact ⟨hj,hk⟩⟩
  · intro hp
    obtain ⟨⟨⟨j,k⟩,hjk⟩,hp⟩ := mem_iUnion.mp hp
    exact ⟨j,mem_univ _,k,mem_univ _,hjk,by simpa only [hc] using hp.1,
      by simpa only [hc] using hp.2⟩

omit [CompactSpace M] [Fintype ι] [DecidableEq ι] in
lemma prepared_circular_direction_first (curves : ι → PhaseBoundaryCurve B)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hc : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (r j))
    (hreg : ∀ j, circularCoordinateRegion ((curves j).index : M) (r j) ⊆
      (coordinateChart ((curves j).index : M)).target)
    (hcover : ∀ j x, x ∈ circularCoordinateRegion ((curves j).index : M) (r j) →
      baseEquiv.symm x ∈ (curves j).phase.source)
    (ell : ι → Base) (L : ι → ℝ)
    (hphase : ∀ j x, (baseEquiv ((curves j).phase x)).1 =
      centeredConvexPhase (ell j) (L j) (coordinateChart ((curves j).index : M) (curves j).index)
        (baseEquiv x))
    (hind : ∀ j k, j ≠ k → ∀ p ∈ circularCrossingSet (fun j => ((curves j).index : M)) r,
      p ∈ (coordinateChart ((curves j).index : M)).source →
      p ∈ (coordinateChart ((curves k).index : M)).source →
      covectorDet
        (phaseDerivative (centeredAtlasPhase ((curves j).index : M) (ell j) (L j) ∘
          (coordinateChart ((curves j).index : M)).symm) (coordinateChart ((curves j).index : M) p))
        (phaseDerivative (centeredAtlasPhase ((curves k).index : M) (ell k) (L k) ∘
          (coordinateChart ((curves j).index : M)).symm) (coordinateChart ((curves j).index : M) p)) ≠ 0)
    (a j : ι) (hja : j ≠ a) {p : M}
    (hp : p ∈ boundaryCrossingSet curves univ ∩ circularCoordinateDisk ((curves a).index : M) (r a))
    (hpj : p ∈ (curves j).carrier) : ((curves j).directionIn (curves a) p).1 ≠ 0 := by
  have hps := B.circular_closed_disk_phase_source (curves a).index (hr a) (hreg a)
    (curves a).phase (hcover a) (subset_closure hp.2)
  have hqj : p ∈ (coordinateChart ((curves j).index : M)).source := by
    rw [coordinateChart_source,← chart_source]
    exact ((curves j).source hpj).1
  have hqa : p ∈ (coordinateChart ((curves a).index : M)).source := by
    rw [coordinateChart_source,← chart_source]
    exact hps.1
  apply (curves j).directionIn_first_ne_of_covectors (curves a) ((curves j).index : M)
    (centeredAtlasPhase ((curves j).index : M) (ell j) (L j))
    (centeredAtlasPhase ((curves a).index : M) (ell a) (L a))
    (centeredPhase_first _ _ _ _ (hphase j)) (centeredPhase_first _ _ _ _ (hphase a))
    hqj hpj hps
  apply hind j a hja p _ hqj hqa
  rw [← boundaryCrossingSet_eq_circular curves r hc]
  exact hp.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryRemovalStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual circular correction removes its own boundary and preserves
all remaining finite geometric conditions. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem circular_boundary_removal_step (curves : ι → PhaseBoundaryCurve B) (a : ι)
    (r r₀ R : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hrr₀ : (r a)^2 < (r₀ a)^2) (hrR : r a < R a)
    (hpos : ∀ p, 0 < B.weight (curves a).index p ↔
      p ∈ circularCoordinateDisk ((curves a).index : M) (r₀ a))
    (hreg : ∀ j, circularCoordinateRegion ((curves j).index : M) (r j) ⊆
      (coordinateChart ((curves j).index : M)).target)
    (hcarrier : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (r j))
    (hcover : ∀ j x, x ∈ circularCoordinateRegion ((curves j).index : M) (r j) →
      baseEquiv.symm x ∈ (curves j).phase.source)
    (ell : ι → Base) (L : ι → ℝ)
    (hphase : ∀ j x, (baseEquiv ((curves j).phase x)).1 =
      centeredConvexPhase (ell j) (L j) (coordinateChart ((curves j).index : M) (curves j).index)
        (baseEquiv x))
    (hpair : ∀ j k, j ≠ k → ((curves j).carrier ∩ (curves k).carrier).Finite)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅)
    (htan : ∀ j, (circularPhaseTangencies ((curves a).index : M) ((curves j).index : M)
      (ell a) (L a) (r j) (r a)).Finite)
    (hind : ∀ j k, j ≠ k → ∀ p ∈ circularCrossingSet (fun j => ((curves j).index : M)) r,
      p ∈ (coordinateChart ((curves j).index : M)).source →
      p ∈ (coordinateChart ((curves k).index : M)).source →
      covectorDet
        (phaseDerivative (centeredAtlasPhase ((curves j).index : M) (ell j) (L j) ∘
          (coordinateChart ((curves j).index : M)).symm) (coordinateChart ((curves j).index : M) p))
        (phaseDerivative (centeredAtlasPhase ((curves k).index : M) (ell k) (L k) ∘
          (coordinateChart ((curves j).index : M)).symm) (coordinateChart ((curves j).index : M) p)) ≠ 0)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F) (hgeom : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n)
    (hconvex : ∀ p ∈ tsupport (B.weight (curves a).index),
      ‖coordinateChart ((curves a).index : M) p-coordinateChart ((curves a).index : M) (curves a).index‖ ≤ R a →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g ((curves a).index : M))
        (centeredConvexPhase (ell a) (L a) (coordinateChart ((curves a).index : M) (curves a).index))
        (coordinateChart ((curves a).index : M) p) v v)
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p)
    (hamppos : ∀ p, 0 < amp p ↔ p ∈ circularCoordinateDisk ((curves a).index : M) (r a))
    (hphi : ∀ p ∈ circularCoordinateDisk ((curves a).index : M) (r a),
      phi =ᶠ[𝓝 p] (fun q => ((curves a).phase (chart ((curves a).index : M) q)) 0))
    (data : MetricGoodPhaseData g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W,
        FiniteBoundaryGeometry (fun j : {j : ι // j ≠ a} => curves j)
          (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => curves j) univ) W N := by
  classical
  apply (curves a).realize_circular_boundary_metric hF n (hr a) hrr₀ hrR hpos (hreg a)
    (hcarrier a) (hcover a) (ell a) (L a)
    (fun x => by exact hphase a (baseEquiv.symm x)) hconvex
    (fun p hp => ⟨hgeom.nonzero a p hp,hgeom.avoids a p hp⟩)
    hamp hamp0 hamppos hphi (fun j : {j : ι // j ≠ a} => curves j)
    (fun j => r j) (fun j => hr j) (fun j => hcarrier j) (fun j => hreg j)
    (fun j k hjk => hpair j k (fun h => hjk (Subtype.ext h)))
    (fun j k l hjk hjl hkl => htriple j k l
      (fun h => hjk (Subtype.ext h)) (fun h => hjl (Subtype.ext h)) (fun h => hkl (Subtype.ext h)))
    (removed_boundary_crossings_disjoint curves a htriple) (hgeom.remove a)
    (hgeom.remove_frontier a) ?_ (fun j => htan j) data h htarget
  intro j p hp hpj
  exact prepared_circular_direction_first curves r hr hcarrier hreg hcover ell L hphase hind a j j.2
    ⟨removed_boundary_crossings_subset curves a hp.1,hp.2⟩ hpj

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPrimitiveFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite circular data used in the global primitive iteration.
All geometric fields are furnished by the generic radius/phase preparation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

 theorem one_step [DecidableEq ι] (d : CircularPrimitiveFamily B ι) (a : ι)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F) (hgeom : FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n)
    (hconvex : ∀ p ∈ tsupport (B.weight (d.curves a).index),
      ‖coordinateChart ((d.curves a).index : M) p-coordinateChart ((d.curves a).index : M) (d.curves a).index‖ ≤ d.chartRadius a →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g ((d.curves a).index : M))
        (centeredConvexPhase (d.linearPart a) (d.convexPart a)
          (coordinateChart ((d.curves a).index : M) (d.curves a).index))
        (coordinateChart ((d.curves a).index : M) p) v v)
    (data : MetricGoodPhaseData g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W,
        FiniteBoundaryGeometry (fun j : {j : ι // j ≠ a} => d.curves j)
          (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => d.curves j) univ) W N := by
  apply circular_boundary_removal_step d.curves a d.radius d.outerRadius d.chartRadius
    d.radius_pos (d.radius_outer a) (d.radius_chart a) (d.weight_positive a) d.region d.carrier d.cover
    d.linearPart d.convexPart d.first_coordinate d.pair_finite d.triple_empty
    (d.tangencies_finite a) ?_ hF n hgeom hconvex (d.amplitude_smooth a)
    (d.amplitude_nonneg a) (d.amplitude_positive a) (d.phase_germ a) data h htarget
  intro j k hjk p hp hj hk
  apply d.independent j k hjk p _ hj hk
  rwa [boundaryCrossingSet_eq_circular d.curves d.radius d.carrier]

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularMetricSequence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered finite primitive realization. The metric convexity is required
only at the actual prefix metrics, preserving the order of the cycles. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

 theorem realize_sequence_oai (N : ℕ) :
    ∀ (d : CircularPrimitiveFamily B (Fin N)) (g : Fin (N+1) → SmoothMetric M),
    (∀ a : Fin N, (g a.succ).inner = (g a.castSucc).inner +
      (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p)) →
    (∀ a : Fin N, d.ConvexMetric (g a.castSucc) a) →
    ∀ (F : M → Space) (n : PreferredNormal F),
    IsSmoothIsometricImmersion M (g 0) F → MetricGoodPhaseData (g 0) F →
    FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
    ∃ W : M → Space, IsSmoothIsometricImmersion M (g (Fin.last N)) W ∧
      Nonempty (MetricGoodPhaseData (g (Fin.last N)) W) ∧ Nonempty (PreferredNormal W) := by
  classical
  induction N with
  | zero =>
    intro d g _ _ F n hF data _
    exact ⟨F,hF,⟨data⟩,⟨n⟩⟩
  | succ N ih =>
    intro d g hstep hconvex F n hF data hgeom
    obtain ⟨W,hW,⟨good⟩,normal,hnew⟩ := d.one_step 0 hF n hgeom (hconvex 0) data
      (g (Fin.succ 0)) (hstep 0)
    let d' := d.restrict (Fin.succ : Fin N → Fin (N+1)) (Fin.succ_injective N)
    let g' : Fin (N+1) → SmoothMetric M := fun a => g a.succ
    have hstep' (a : Fin N) : (g' a.succ).inner = (g' a.castSucc).inner +
        (fun p => (d'.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d'.phase a) p) := by
      simpa only [g',d',restrict,Function.comp_apply,ConvexMetric,Fin.succ_castSucc] using hstep a.succ
    have hconvex' (a : Fin N) : d'.ConvexMetric (g' a.castSucc) a := by
      simpa only [g',d',restrict,Function.comp_apply,ConvexMetric,Fin.succ_castSucc] using hconvex a.succ
    let f : Fin N → {j : Fin (N+1) // j ≠ 0} := fun a => ⟨a.succ,Fin.succ_ne_zero a⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Fin.succ_injective N (congrArg Subtype.val hab)
    have hsub : boundaryCrossingSet d'.curves univ ⊆
        boundaryCrossingSet (fun j : {j : Fin (N+1) // j ≠ 0} => d.curves j) univ := by
      rintro p ⟨a,_,b,_,hab,ha,hb⟩
      exact ⟨f a,mem_univ _,f b,mem_univ _,fun h => hab (hf h),ha,hb⟩
    have hgeom' : FiniteBoundaryGeometry d'.curves (boundaryCrossingSet d'.curves univ) W normal :=
      hnew.restrict f hf hsub
    obtain ⟨V,hV,hgood,hN⟩ := ih d' g' hstep' hconvex' W normal hW good hgeom'
    exact ⟨V,hV,hgood,hN⟩

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence_oai.{u_1}
