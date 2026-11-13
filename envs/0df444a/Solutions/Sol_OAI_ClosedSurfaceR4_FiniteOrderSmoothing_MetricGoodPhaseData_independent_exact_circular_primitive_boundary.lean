-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_boundary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:39:55.026758+00:00
-- url     : https://prove2.me/submissions/9cc90083-4e46-413a-845a-b2d7ebf83276

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_circular_primitive_profiles

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalJets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma contDiff_realTwoJet {F : RField 4} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (realTwoJet F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean



lemma realMetricTensor_comp {n : ℕ} {F : RField n} {χ : Base → Base} {p : Base}
    (hF : DifferentiableAt ℝ F (χ p)) (hχ : DifferentiableAt ℝ χ p) :
    realMetricTensor (F ∘ χ) p = pullbackField χ p (realMetricTensor F (χ p)) := by
  ext i
  rw [realMetricTensor_apply]
  change realMetric (F ∘ χ) (firstDirection i) (secondDirection i) p =
    evaluate (realMetricTensor F (χ p))
      (fderiv ℝ χ p (firstDirection i)) (fderiv ℝ χ p (secondDirection i))
  rw [evaluate_realMetricTensor]
  simp only [realMetric, coordDeriv, fderiv_comp p hF hχ, ContinuousLinearMap.comp_apply]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetChainRule
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chain rule for coefficients depending on position and the actual
second jet of a map from a surface chart into four-space. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_derivative {G : Base → Space} (hG : ContDiff ℝ ∞ G) (v : Fin 2) (p : Base) :
    fderiv ℝ (lowJet G) p (coordinateVector v) = lowDerivative G v p := by
  ext i
  have h := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
    (fderiv_apply ((lowJet_smooth hG).differentiable (by simp) p) i)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    lowJet_coordinate_derivative] using h.symm

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three independent coordinates of a symmetric surface tensor, with
an explicit continuous linear reconstruction into the full tensor fiber. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberNormed
local instance coordinateFiberSpace_r2b8a52_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberToThree_fromThree (H : Tensor) : fiberToThree (fiberFromThree H) = H := by
  ext k
  change fiberFromThree H (planeCoordinates.symm (firstDirection k))
    (planeCoordinates.symm (secondDirection k)) = H k
  rw [fiberFromThree_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberSpace
local instance chartReadSectionNormed_r2b8a52_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r2b8a52_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorChartRead_on_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorChartRead i u (chart (i : M) p) = fiberToThree (A.bundleComponent A.tensorTriv i u p) := by
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp]
  simp only [one_pow, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma slowOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) (t : ℝ) :
    slowOn F S hS hF v p (t : Period) =
      slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t) :=
  bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the active chart locus the local metric is exactly the chart read
of the induced global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactFiberSpace
local instance metricReadExactDualSmul_r2b8a52_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactFiberNormed
local instance metricReadExactSectionNormed_r2b8a52_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadExactSectionSpace_r2b8a52_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metric_component_on_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M}
    (hp : p ∈ tsupport (A.weight i)) :
    A.bundleComponent A.tensorTriv i (inducedTensor F) p =
      fiberFromThree (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) := by
  have hsource := A.weight_support i hp
  let f : Base → TensorFiber := fun y => fiberFromThree
    (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry y))
  have he : A.bundleRestore A.tensorTriv i f p = inducedTensor F p := by
    ext v w
    rw [A.tensorRestore_apply i f hsource,A.outer_one i p hp,one_mul]
    change fiberFromThree
      (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) =
        inducedForm F p v w
    rw [fiberFromThree_apply]
    have hd := A.vectorPlaneRead_differential i hF hp
    rw [A.plane_chart_differential i hsource] at hd
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    rw [euclidean_metric_coordinate_value (A.vectorPlaneRead i F)
      ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _)]
    exact congrArg₂ (inner ℝ) hv.symm hw.symm
  have hc := congrArg ((A.tensorTriv i).continuousLinearMapAt ℝ p) he
  simp only [bundleRestore,A.outer_one i p hp,one_smul,
    (A.tensorTriv i).continuousLinearMapAt_symmL (A.tensorTriv_domain i hsource)] at hc
  exact hc.symm

lemma metric_read_on_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : Base}
    (hx : A.chartWeight i x ≠ 0) :
    RealModes.realMetricTensor (A.jetChartMap i F ∘ planeCoordinateIsometry.symm)
        (planeCoordinateIsometry x) = A.tensorChartRead i (inducedTensor F) x := by
  have hxt : x ∈ (chart (i : M)).target := by
    by_contra hn
    exact hx (by simp only [chartWeight,indicator_of_notMem hn])
  have hw : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
    simpa only [chartWeight,indicator_of_mem hxt] using hx
  have hp := subset_tsupport (A.weight i) hw
  have hread := A.tensorChartRead_on_weight i (inducedTensor F) hp
  rw [(chart (i : M)).right_inv hxt,A.metric_component_on_weight i hF hp,
    fiberToThree_fromThree,(chart (i : M)).right_inv hxt] at hread
  exact hread.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {O E}
namespace Family

@[simp] lemma slow_apply (F : Family O E) (v : A) {p : A} (hp : p ∈ O) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      SmoothPeriodicCalculus.slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := by
  rw [slow, ofLocal_apply _ _ hp, slowOn_apply _ _ _ _ _ hp]

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_JetMetricCoordinatePullback
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete metric-plus-polynomial operator transforms through fixed
nonlinear coordinates, including its finite periodic error. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open RealModes

lemma metric_coordinate_pullback {F : Base → Space} {T : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hT : ContDiff ℝ ∞ T) (x : Base) :
    realMetricTensor ((F ∘ T) ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x
        (realMetricTensor (F ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry (T x))) := by
  let τ : SmallModes.Base → SmallModes.Base :=
    planeCoordinateIsometry ∘ T ∘ planeCoordinateIsometry.symm
  have hτ : ContDiff ℝ ∞ τ := planeCoordinateIsometry.contDiff.comp
    (hT.comp planeCoordinateIsometry.symm.contDiff)
  have he : (F ∘ planeCoordinateIsometry.symm) ∘ τ =
      (F ∘ T) ∘ planeCoordinateIsometry.symm := by
    funext p
    simp [τ]
  rw [← he,realMetricTensor_comp
    ((hF.comp planeCoordinateIsometry.symm.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hτ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)]
  have hd : fderiv ℝ τ (planeCoordinateIsometry x) = tensorCoordinateDerivative T x := by
    dsimp [τ]
    rw [fderiv_comp _ (planeCoordinateIsometry.differentiableAt)
      ((hT.comp planeCoordinateIsometry.symm.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
      fderiv_comp _ (hT.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) planeCoordinateIsometry.symm.differentiableAt]
    simp only [LinearIsometryEquiv.fderiv,LinearIsometryEquiv.symm_apply_apply]
    rfl
  simp only [PhaseMean.pullbackField,hd,τ,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply,tensorCoordinatePullbackValue]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricGaussInvariance
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gauss scalar of an exact realization is fixed by the prescribed metric
in a neighborhood, independent of the choice of immersion. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma coordDeriv_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Base → E} {p : Base} (h : f =ᶠ[𝓝 p] g) (v : Base) :
    coordDeriv v f =ᶠ[𝓝 p] coordDeriv v g :=
  h.fderiv.mono (fun _ he => congrArg (fun L : Base →L[ℝ] E => L v) he)

lemma coordinateGauss_germ {E F G E' F' G' : Base → ℝ} {p : Base}
    (hE : E =ᶠ[𝓝 p] E') (hF : F =ᶠ[𝓝 p] F') (hG : G =ᶠ[𝓝 p] G') :
    coordinateGauss E F G p = coordinateGauss E' F' G' p := by
  simp only [coordinateGauss,hE.eq_of_nhds,hF.eq_of_nhds,hG.eq_of_nhds,
    (coordDeriv_germ hE dx).eq_of_nhds,(coordDeriv_germ hE dy).eq_of_nhds,
    (coordDeriv_germ hF dx).eq_of_nhds,(coordDeriv_germ hF dy).eq_of_nhds,
    (coordDeriv_germ hG dx).eq_of_nhds,(coordDeriv_germ hG dy).eq_of_nhds,
    (coordDeriv_germ (coordDeriv_germ hF dy) dx).eq_of_nhds,
    (coordDeriv_germ (coordDeriv_germ hE dy) dy).eq_of_nhds,
    (coordDeriv_germ (coordDeriv_germ hG dx) dx).eq_of_nhds]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth orthonormal frames obtained by interpolating non-antipodal plane directions. -/
noncomputable section
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma normalize_unit {v : Vec} (hv : v ≠ 0) : normalize v ⬝ᵥ normalize v = 1 := by
  have hp := dot_self_pos hv
  have hs : Real.sqrt (v ⬝ᵥ v) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have heq := Real.sq_sqrt hp.le
  field_simp
  nlinarith [heq]

lemma dot_normalize_zero {v w : Vec} (h : w ⬝ᵥ v = 0) : w ⬝ᵥ normalize v = 0 := by
  simp [normalize, dotProduct_smul, h]

lemma normalize_nonzero {v : Vec} (hv : v ≠ 0) : normalize v ≠ 0 := by
  intro hz
  have hu := normalize_unit hv
  rw [hz] at hu
  norm_num at hu

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalize_smoothAt {v : E → Vec} {x : E} (hv : ContDiffAt ℝ ∞ v x) (hn : v x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => normalize (v z)) x := by
  have hd : ContDiffAt ℝ ∞ (fun z => v z ⬝ᵥ v z) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hp := dot_self_pos hn
  exact ((hd.sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').smul hv

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCoordinateData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth velocity coordinates and their calibrated collar values. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma velocityRadius_smoothOn {v : E → Vec} {a : E → ℝ} {U : Set E}
    (hv : ContDiffOn ℝ ∞ v U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, v x ≠ 0 ∨ a x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => velocityRadius (v x) (a x)) U := by
  apply ((dot_smoothOn hv hv).add (ha.pow 2)).sqrt
  intro x hx
  have hp := velocityRadius_pos (hn x hx)
  exact (Real.sqrt_pos.mp hp).ne'

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal frames and scaled second-form coefficients are smooth functions of
exactly the five derivative components retained by the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

lemma contDiffAt_profileNormalPart {J : BoundaryProfile}
    (hJ : gramDet (J 0) (J 1) ≠ 0) : ContDiffAt ℝ ∞ profileNormalPart J := by
  exact contDiffAt_realNormalPart
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 2 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt hJ

lemma contDiffAt_profilePreferred {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profilePreferred J :=
  normalize_smoothAt (contDiffAt_profileNormalPart hJ.1) hJ.2

lemma contDiffAt_profileComplement {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileComplement J := by
  have hn := realNormalPart_perp (J 0) (J 1) (J 2) hJ.1
  exact contDiffAt_unitPerp
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (contDiffAt_profilePreferred hJ) hJ.1 (normalize_nonzero hJ.2)
    (dot_normalize_zero hn.1) (dot_normalize_zero hn.2)

lemma isOpen_regularBoundaryProfiles : IsOpen regularBoundaryProfiles := by
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hd : Continuous (fun K : BoundaryProfile => gramDet (K 0) (K 1)) := by
    unfold gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_profileNormalPart hJ.1).continuousAt.eventually_ne hJ.2)

lemma contDiffAt_profileCoefficients {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileCoefficients J := by
  have hslot (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : BoundaryProfile => K i) J :=
    (ContinuousLinearMap.proj i : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
  have hdot {f g : BoundaryProfile → Vec}
      (hf : ContDiffAt ℝ ∞ f J) (hg : ContDiffAt ℝ ∞ g J) :
      ContDiffAt ℝ ∞ (fun K => f K ⬝ᵥ g K) J :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hf i).mul (contDiffAt_pi.mp hg i))
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (hdot (contDiffAt_profileNormalPart hJ.1)
      (contDiffAt_profileNormalPart hJ.1)).sqrt (dot_self_pos hJ.2).ne'
  · exact hdot (hslot 3) (contDiffAt_profilePreferred hJ)
  · exact hdot (hslot 3) (contDiffAt_profileComplement hJ)
  · exact hdot (hslot 4) (contDiffAt_profileComplement hJ)

lemma contDiffAt_profileGeometry {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileGeometry J :=
  ((contDiffAt_profilePreferred hJ).prodMk (contDiffAt_profileComplement hJ)).prodMk
    (contDiffAt_profileCoefficients hJ)

/-- Uniformly transfer all five derivative estimates to the actual normal
frame and its scaled coefficients on a compact family of regular profiles. -/
theorem compact_boundary_profile_stability {K : Set BoundaryProfile}
    (hK : IsCompact K) (hregular : K ⊆ regularBoundaryProfiles) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ J ∈ K, ∀ H : BoundaryProfile,
      ‖H-J‖ < δ → H ∈ regularBoundaryProfiles ∧
        ‖profileGeometry H-profileGeometry J‖ < ε := by
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open
    isOpen_regularBoundaryProfiles hregular
  have hc : ContinuousOn profileGeometry (Metric.cthickening r K) :=
    fun J hJ => (contDiffAt_profileGeometry (hsub hJ)).continuousAt.continuousWithinAt
  have hu := hK.cthickening.uniformContinuousOn_of_continuous hc
  intro ε hε
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro J hJ H hHJ
  have hH : H ∈ Metric.cthickening r K :=
    Metric.thickening_subset_cthickening r K
      (Metric.mem_thickening_iff.mpr ⟨J,hJ,by
        simpa only [dist_eq_norm] using hHJ.trans_le (min_le_left r d)⟩)
  refine ⟨hsub hH,?_⟩
  have hJ' : J ∈ Metric.cthickening r K := Metric.self_subset_cthickening K hJ
  simpa only [dist_eq_norm] using hclose H hH J hJ'
    (by simpa only [dist_eq_norm] using hHJ.trans_le (min_le_right r d))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFastEvaluation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast-phase differentiation on an admissible chart domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma angle_apply (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := by
  rw [angle, ofLocal_apply _ _ hp]
  exact LocalPeriodicCalculus.bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityLoop
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A controlled loop on a neighborhood of the actual second-jet section.
Its translation depends on position alone, so the prescribed turn derivatives
along the original section persist under the joint density construction. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

lemma jetSection_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jetSection F) := contDiff_id.prodMk (contDiff_realTwoJet hF)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceJetCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translate the geometric surface jets to the coordinates used by the
quantitative finite-polynomial construction. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceJetCoordinates
open RealModes SmallModes WeightedEstimates

lemma directional_chart (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) (w : List (Fin 2)) :
    iteratedDirectional (w.map JetPolynomial.coordinateVector) (f ∘ baseEquiv) =
      (iteratedDirectional (w.map (fun i => baseEquiv (JetPolynomial.coordinateVector i))) f) ∘ baseEquiv := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, iteratedDirectional]
    rw [ih]
    funext p
    have hs : ContDiff ℝ ∞
        (iteratedDirectional (w.map (fun i => baseEquiv (JetPolynomial.coordinateVector i))) f) :=
      contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn _)
    rw [fderiv_comp p (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) baseEquiv.differentiableAt,
      baseEquiv.fderiv, ContinuousLinearMap.comp_apply]
    rfl

lemma directional_component {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (w : List Base) (a : Fin 4) :
    iteratedDirectional w (fun p => F p a) = fun p => iteratedDirectional w F p a := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [iteratedDirectional]
    rw [ih]
    funext p
    have hs : ContDiff ℝ ∞ (iteratedDirectional w F) :=
      contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hF.contDiffOn w)
    rw [fderiv_apply (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) a]
    rfl

theorem decode_lowJet {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : JetPolynomial.Base) :
    decode (JetPolynomial.lowJet (F ∘ baseEquiv) p) = CollarVelocity.jetSection F (baseEquiv p) := by
  apply Prod.ext
  · rfl
  · funext i a
    change JetPolynomial.jet (F ∘ baseEquiv) (JetPolynomial.lowWord (![1, 2, 3, 4, 6] i)) a p =
      realTwoJet F (baseEquiv p) i a
    have he (w : List (Fin 2)) : JetPolynomial.jet (F ∘ baseEquiv) w a p =
        iteratedDirectional (w.map (fun j => baseEquiv (JetPolynomial.coordinateVector j))) F (baseEquiv p) a := by
      change iteratedDirectional (w.map JetPolynomial.coordinateVector)
        ((fun q => F q a) ∘ baseEquiv) p = _
      rw [directional_chart _ (contDiff_pi.mp hF a) w, Function.comp_apply, directional_component hF]
    rw [he]
    fin_cases i <;> simp [JetPolynomial.lowWord, realTwoJet, iteratedDirectional, coordDeriv,
      JetPolynomial.coordinateVector, dx, dy] <;> rfl

end ClosedSurfaceR4.SurfaceJetCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityIdentities
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading metric and support of the actual second-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

variable {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O)

lemma geometry_velocity {p : JetPolynomial.Base} (hp : p ∈ S) :
    (l.geometry G hG hGO).V.val p = l.euclideanVelocity (lowJet G p) := by
  apply ContinuousMap.ext
  intro t
  change (Family.ofLocal (fun q => l.euclideanVelocity (lowJet G q)) _).val p t = _
  exact Family.ofLocal_apply _ _ hp t

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LeadingProfileMap
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five leading profiles depend smoothly on the second jet, its first
transverse derivative, and the periodic parameter. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma leadingVelocity_smooth : ContDiffOn ℝ ∞ l.leadingVelocity (O ×ˢ univ) :=
  (l.smoothTangent.comp contDiffOn_fst (fun _ hz => hz.1)).add l.smoothVelocity

lemma leadingProfileMap_smooth :
    ContDiffOn ℝ ∞ l.leadingProfileMap ((O ×ˢ univ) ×ˢ univ) := by
  have hJ : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => z.1.1) ((O ×ˢ univ) ×ˢ univ) :=
    contDiffOn_fst.fst
  have hV : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => l.leadingVelocity z.1)
      ((O ×ˢ univ) ×ˢ univ) :=
    l.leadingVelocity_smooth.comp contDiffOn_fst (fun _ hz => hz.1)
  have hdV : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => fderiv ℝ l.leadingVelocity z.1)
      ((O ×ˢ univ) ×ˢ univ) := (l.leadingVelocity_smooth.fderiv_of_isOpen
    (O.isOpen.prod isOpen_univ) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp contDiffOn_fst (fun _ hz => hz.1)
  have hdW : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => fderiv ℝ l.velocity z.1)
      ((O ×ˢ univ) ×ˢ univ) := (l.smoothVelocity.fderiv_of_isOpen
    (O.isOpen.prod isOpen_univ) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp contDiffOn_fst (fun _ hz => hz.1)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn hV
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn ((slot_smooth 2).contDiffOn.comp hJ (fun _ _ => mem_univ _))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn ((slot_smooth 6).contDiffOn.comp hJ (fun _ _ => mem_univ _))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn
      (hdV.clm_apply (contDiffOn_snd.prodMk contDiffOn_const))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn
      (hdW.clm_apply contDiffOn_const)

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularJetProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the canonical boundary profiles with the actual circular loop
in the analytic second-jet coordinates. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4
namespace GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma circular_angular_derivative {R : E → ℝ} {e₁ e₂ : E → Vec}
    {α : E × ℝ → ℝ} {x : E} {t : ℝ}
    (hR : DifferentiableAt ℝ R x) (h₁ : DifferentiableAt ℝ e₁ x)
    (h₂ : DifferentiableAt ℝ e₂ x) (hα : DifferentiableAt ℝ α (x,t)) :
    fderiv ℝ (fun z : E × ℝ => R z.1 • direction (e₁ z.1) (e₂ z.1) (α z))
      (x,t) (0,1) = (R x*fderiv ℝ α (x,t) (0,1)) •
        angularDirection (e₁ x) (e₂ x) (α (x,t)) := by
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (x,t))
  have hd := (hR.hasFDerivAt.comp (x,t) hf).smul
    ((hα.hasFDerivAt.cos.smul (h₁.hasFDerivAt.comp (x,t) hf)).add
      (hα.hasFDerivAt.sin.smul (h₂.hasFDerivAt.comp (x,t) hf)))
  change HasFDerivAt (fun z : E × ℝ =>
    R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) _ (x,t) at hd
  rw [hd.fderiv]
  ext i
  simp [angularDirection,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
    Function.comp_def]
  ring

end GeometryPreservation

namespace SurfaceVelocityFamily.Loop
open NormalFrame VelocityFrame RealModes JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem circular_leadingProfileMap {R : LowJet → ℝ} {e₁ e₂ : LowJet → Vec}
    {α : LowJet × ℝ → ℝ} (hR : ContDiffOn ℝ ∞ R O)
    (h₁ : ContDiffOn ℝ ∞ e₁ O) (h₂ : ContDiffOn ℝ ∞ e₂ O)
    (hα : ContDiffOn ℝ ∞ α (O ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      R J • direction (e₁ J) (e₂ J) (α (J,t)))
    {J : LowJet} (hJ : J ∈ O) (t : ℝ) (D : LowJet) :
    boundaryProfileMap (l.leadingProfileMap ((J,t),D)) =
      circularFamilyProfile tangent (slot 1) (slot 2) (slot 6) R e₁ e₂ α D (J,t) := by
  have hnb : (O : Set LowJet) ×ˢ (univ : Set ℝ) ∈ 𝓝 (J,t) :=
    (O.isOpen.prod isOpen_univ).mem_nhds ⟨hJ,mem_univ t⟩
  have hvgerm : l.velocity =ᶠ[𝓝 (J,t)]
      (fun z : LowJet × ℝ => R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) := by
    filter_upwards [hnb] with z hz
    exact hvel z.1 hz.1 z.2
  have hlgerm : l.leadingVelocity =ᶠ[𝓝 (J,t)]
      (fun z : LowJet × ℝ => tangent z.1+
        R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) := by
    filter_upwards [hvgerm] with z hz
    exact congrArg (fun v => tangent z.1+v) hz
  have hangle := circular_angular_derivative
    ((hR.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₁.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₂.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hα.contDiffAt hnb).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  funext i
  fin_cases i
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (l.leadingVelocity (J,t))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    exact hlgerm.eq_of_nhds
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (slot 2 J)) = _
    exact spaceCoordinates.apply_symm_apply _
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (slot 6 J)) = _
    exact spaceCoordinates.apply_symm_apply _
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean
      (fderiv ℝ l.leadingVelocity (J,t) (D,0))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun L : (LowJet × ℝ) →L[ℝ] Vec => L (D,0)) hlgerm.fderiv_eq
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean
      (fderiv ℝ l.velocity (J,t) (0,1))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply,hvgerm.fderiv_eq]
    exact hangle

end SurfaceVelocityFamily.Loop
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularProfilePullback
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pull back the circular profiles through the actual second-jet section.
The only derivative of the section that enters is its transverse derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem circularFamilyProfile_comp {φ : E → F} {Q X Y C e₁ e₂ : F → Vec}
    {R : F → ℝ} {α : F × ℝ → ℝ} {x : E} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hQ : DifferentiableAt ℝ Q (φ x))
    (hR : DifferentiableAt ℝ R (φ x)) (h₁ : DifferentiableAt ℝ e₁ (φ x))
    (h₂ : DifferentiableAt ℝ e₂ (φ x)) (hα : DifferentiableAt ℝ α (φ x,t)) (d : E) :
    circularFamilyProfile (Q ∘ φ) (X ∘ φ) (Y ∘ φ) (C ∘ φ) (R ∘ φ)
      (e₁ ∘ φ) (e₂ ∘ φ) (fun z => α (φ z.1,z.2)) d (x,t) =
    circularFamilyProfile Q X Y C R e₁ e₂ α (fderiv ℝ φ x d) (φ x,t) := by
  have hσ := (hφ.hasFDerivAt.comp (x,t)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x,t)))).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x,t)))
  have hβ : fderiv ℝ (fun z : E × ℝ => α (φ z.1,z.2)) (x,t) (0,1) =
      fderiv ℝ α (φ x,t) (0,1) := by
    simpa [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
      ContinuousLinearMap.snd] using
      congrArg (fun L : (E × ℝ) →L[ℝ] ℝ => L (0,1)) (hα.hasFDerivAt.comp (x,t) hσ).fderiv
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (φ x,t))
  have hV := (hQ.hasFDerivAt.comp (φ x,t) hf).add ((hR.hasFDerivAt.comp (φ x,t) hf).smul
    ((hα.hasFDerivAt.cos.smul (h₁.hasFDerivAt.comp (φ x,t) hf)).add
      (hα.hasFDerivAt.sin.smul (h₂.hasFDerivAt.comp (φ x,t) hf))))
  change HasFDerivAt (fun z : F × ℝ => Q z.1+
    R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) _ (φ x,t) at hV
  have hW :
      fderiv ℝ (fun z : E × ℝ => Q (φ z.1)+
        R (φ z.1) • direction (e₁ (φ z.1)) (e₂ (φ z.1)) (α (φ z.1,z.2))) (x,t) (d,0) =
      fderiv ℝ (fun z : F × ℝ => Q z.1+
        R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) (φ x,t) (fderiv ℝ φ x d,0) := by
    simpa [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
      ContinuousLinearMap.snd] using
      congrArg (fun L : (E × ℝ) →L[ℝ] Vec => L (d,0)) (hV.differentiableAt.hasFDerivAt.comp (x,t) hσ).fderiv
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hW
  · change ((R ∘ φ) x * fderiv ℝ (fun z => α (φ z.1,z.2)) (x,t) (0,1)) • _ = _
    rw [hβ]
    rfl

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LeadingProfileIdentification
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional leading-profile map evaluates to the exact
geometric velocity and its derivatives in the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation CovarianceCorrector
open LocalPeriodicExpansion
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

private lemma jet_parameter_pullback_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (c : LowJet × ℝ → RealModes.RVec 4)
    (p : JetPolynomial.Base) (t : ℝ) (hc : DifferentiableAt ℝ c (lowJet G p,t))
    (v : JetPolynomial.Base) (a : ℝ) :
    fderiv ℝ (fun q : JetPolynomial.Base × ℝ =>
      JetVelocityCoordinates.toEuclidean (c (lowJet G q.1,q.2))) (p,t) (v,a) =
      JetVelocityCoordinates.toEuclidean (fderiv ℝ c (lowJet G p,t)
        (fderiv ℝ (lowJet G) p v,a)) := by
  have hlow : HasFDerivAt (lowJet G) (fderiv ℝ (lowJet G) p) p :=
    ((lowJet_smooth hG).differentiable (by simp) p).hasFDerivAt
  have hfirst : HasFDerivAt (fun q : JetPolynomial.Base × ℝ => lowJet G q.1)
      ((fderiv ℝ (lowJet G) p).comp (ContinuousLinearMap.fst ℝ JetPolynomial.Base ℝ)) (p,t) :=
    by
      simpa only [Function.comp_def] using
        (hlow.comp (p,t) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p,t))))
  have hP : HasFDerivAt (fun q : JetPolynomial.Base × ℝ => (lowJet G q.1,q.2))
      (((fderiv ℝ (lowJet G) p).comp (ContinuousLinearMap.fst ℝ JetPolynomial.Base ℝ)).prod
        (ContinuousLinearMap.snd ℝ JetPolynomial.Base ℝ)) (p,t) :=
    hfirst.prodMk (ContinuousLinearMap.snd ℝ JetPolynomial.Base ℝ).hasFDerivAt
  have hd := ((JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp (lowJet G p,t)
    hc.hasFDerivAt).comp (p,t) hP).fderiv
  change (fderiv ℝ ((JetVelocityCoordinates.toEuclidean ∘ c) ∘
    (fun q : JetPolynomial.Base × ℝ => (lowJet G q.1,q.2))) (p,t)) (v,a) = _
  rw [hd]
  rfl

lemma geometry_longitudinal_value {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    (l.geometry G hG hGO).longitudinal.val p (t : Period) =
      JetVelocityCoordinates.toEuclidean (l.leadingVelocity (lowJet G p,t)) := by
  rw [Geometry.longitudinal,Family.add_apply,Family.constant_apply _ _ hp,
    l.geometry_velocity hG hGO hp,l.euclideanVelocity_apply (hGO hp)]
  exact (map_add JetVelocityCoordinates.toEuclidean _ _).symm

/-- All five entries depend on the third jet only through the single
transverse derivative of the second jet. -/
theorem leadingProfileMap_geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    l.leadingProfileMap ((lowJet G p,t),lowDerivative G 1 p) =
      ![(l.geometry G hG hGO).longitudinal.val p (t : Period),
        (l.geometry G hG hGO).Y p,(l.geometry G hG hGO).C p,
        ((l.geometry G hG hGO).longitudinal.slow (coordinateVector 1)).val p (t : Period),
        (l.geometry G hG hGO).V.angle.val p (t : Period)] := by
  have hlong : (fun q : JetPolynomial.Base × ℝ =>
      (l.geometry G hG hGO).longitudinal.val q.1 (q.2 : Period)) =ᶠ[𝓝 (p,t)]
      (fun q => JetVelocityCoordinates.toEuclidean (l.leadingVelocity (lowJet G q.1,q.2))) := by
    filter_upwards [(S.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ t⟩] with q hq
    exact l.geometry_longitudinal_value hG hGO hq.1 q.2
  have hvel : (fun q : JetPolynomial.Base × ℝ =>
      (l.geometry G hG hGO).V.val q.1 (q.2 : Period)) =ᶠ[𝓝 (p,t)]
      (fun q => JetVelocityCoordinates.toEuclidean (l.velocity (lowJet G q.1,q.2))) := by
    filter_upwards [(S.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ t⟩] with q hq
    rw [l.geometry_velocity hG hGO hq.1,l.euclideanVelocity_apply (hGO hq.1)]
  have hmem : (lowJet G p,t) ∈ (O : Set LowJet) ×ˢ univ := ⟨hGO hp,mem_univ t⟩
  have hW := (l.leadingVelocity_smooth.contDiffAt
    ((O.isOpen.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hV := (l.smoothVelocity.contDiffAt
    ((O.isOpen.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  funext i
  fin_cases i
  · exact (l.geometry_longitudinal_value hG hGO hp t).symm
  · rfl
  · rfl
  · change JetVelocityCoordinates.toEuclidean
        (fderiv ℝ l.leadingVelocity (lowJet G p,t) (lowDerivative G 1 p,0)) =
      ((l.geometry G hG hGO).longitudinal.slow (coordinateVector 1)).val p (t : Period)
    rw [Family.slow_apply _ _ hp]
    change _ = fderiv ℝ _ (p,t) (coordinateVector 1,0)
    rw [hlong.fderiv_eq,jet_parameter_pullback_derivative hG _ p t hW,
      lowJet_derivative hG]
  · change JetVelocityCoordinates.toEuclidean (fderiv ℝ l.velocity (lowJet G p,t) (0,1)) =
      (l.geometry G hG hGO).V.angle.val p (t : Period)
    rw [Family.angle_apply _ hp]
    change _ = fderiv ℝ _ (p,t) (0,1)
    rw [hvel.fderiv_eq,jet_parameter_pullback_derivative hG _ p t hV,map_zero]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularSectionProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circular profiles of the actual original immersion, expressed through
its second jet and its transverse third derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open NormalFrame VelocityFrame RealModes JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem circular_geometricLeadingProfile {R : LowJet → ℝ} {e₁ e₂ : LowJet → Vec}
    {α : LowJet × ℝ → ℝ} (hR : ContDiffOn ℝ ∞ R O)
    (h₁ : ContDiffOn ℝ ∞ e₁ O) (h₂ : ContDiffOn ℝ ∞ e₂ O)
    (hα : ContDiffOn ℝ ∞ α (O ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      R J • direction (e₁ J) (e₂ J) (α (J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    boundaryProfileMap (l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period)) =
      circularFamilyProfile (tangent ∘ lowJet G) ((slot 1) ∘ lowJet G)
        ((slot 2) ∘ lowJet G) ((slot 6) ∘ lowJet G) (R ∘ lowJet G)
        (e₁ ∘ lowJet G) (e₂ ∘ lowJet G) (fun z => α (lowJet G z.1,z.2))
        (coordinateVector 1) (p,t) := by
  have hj := hGO hp
  have he : l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period) =
      l.leadingProfileMap ((lowJet G p,t),lowDerivative G 1 p) :=
    (l.leadingProfileMap_geometry hG hGO hp t).symm
  rw [he,l.circular_leadingProfileMap hR h₁ h₂ hα hvel hj]
  have hQ : DifferentiableAt ℝ tangent (lowJet G p) :=
    (l.smoothTangent.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh := circularFamilyProfile_comp (t := t) (X := slot 1) (Y := slot 2) (C := slot 6)
    ((lowJet_smooth hG).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) hQ
    ((hR.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₁.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₂.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hα.contDiffAt ((O.isOpen.prod isOpen_univ).mem_nhds ⟨hj,mem_univ t⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (coordinateVector 1)
  rw [lowJet_derivative hG] at hh
  exact hh.symm

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseBoundaryProfile
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read the exact immersion's five profiles in the real coordinate chart
used by the Gauss and boundary calculations. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseRealChartMap_smooth (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.phaseRealChartMap i T F) :=
  (A.jetChartMap_smooth i hF).comp (hT.comp baseEquiv.symm.contDiff)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricRead
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric and intrinsic Gauss expression in phase coordinates are
fixed by the prescribed global metric, independently of its isometric
realization. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_isometry (i : A.centers) {T : JetPolynomial.Base → JetPolynomial.Base}
    (hT : ContDiff ℝ ∞ T) {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : JetPolynomial.Base}
    (hp : A.chartWeight i (T p) ≠ 0) :
    realMetricTensor (A.phaseRealChartMap i T F) (baseEquiv p) =
      A.phaseMetricRead i T g (baseEquiv p) := by
  have hm : g.inner = inducedTensor F := by
    funext q
    ext v w
    exact (hF.2 q v w).symm
  change realMetricTensor ((A.jetChartMap i F ∘ T) ∘ planeCoordinateIsometry.symm)
    (planeCoordinateIsometry p) = _
  rw [metric_coordinate_pullback (A.jetChartMap_smooth i hF.1) hT p,
    A.metric_read_on_weight i hF.1 hp,← hm]
  simp only [phaseMetricRead,baseEquiv.symm_apply_apply]

lemma phaseMetricRead_isometry_germ (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : A.chartWeight i (T (baseEquiv.symm p)) ≠ 0) :
    realMetricTensor (A.phaseRealChartMap i T F) =ᶠ[𝓝 p] A.phaseMetricRead i T g := by
  have hc : Continuous (fun x : SmallModes.Base => A.chartWeight i (T (baseEquiv.symm x))) :=
    (A.chartWeight_smooth i).continuous.comp (hT.continuous.comp baseEquiv.symm.continuous)
  filter_upwards [((isOpen_ne : IsOpen {r : ℝ | r ≠ 0}).preimage hc).mem_nhds hp] with x hx
  have hh := A.phaseMetricRead_isometry i hT hF (p := baseEquiv.symm x) hx
  rw [baseEquiv.apply_symm_apply] at hh
  exact hh

lemma phaseGauss_isometry (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : A.chartWeight i (T (baseEquiv.symm p)) ≠ 0) :
    coordinateGauss (realMetric (A.phaseRealChartMap i T F) SmallModes.dx SmallModes.dx)
      (realMetric (A.phaseRealChartMap i T F) SmallModes.dx SmallModes.dy)
      (realMetric (A.phaseRealChartMap i T F) SmallModes.dy SmallModes.dy) p =
    coordinateGauss (fun x => A.phaseMetricRead i T g x 0)
      (fun x => A.phaseMetricRead i T g x 1) (fun x => A.phaseMetricRead i T g x 2) p := by
  have hg := A.phaseMetricRead_isometry_germ i hT hF hp
  apply coordinateGauss_germ
  · exact hg.mono (fun x hx => congrFun hx 0)
  · exact hg.mono (fun x hx => congrFun hx 1)
  · exact hg.mono (fun x hx => congrFun hx 2)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricRegularity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_isometry_det (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : A.chartWeight i (T (baseEquiv.symm p)) ≠ 0) :
    gramDet (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i T F) p)
      (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i T F) p) =
    A.phaseMetricRead i T g p 0 * A.phaseMetricRead i T g p 2 -
      (A.phaseMetricRead i T g p 1)^2 := by
  have hm := A.phaseMetricRead_isometry i hT hF (p := baseEquiv.symm p) hp
  rw [baseEquiv.apply_symm_apply] at hm
  have hh := congrArg (fun H : PhaseMean.Tensor => H 0*H 2-(H 1)^2) hm
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame
lemma coordinateGauss_eq_curvature_mul (F : RField 4) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p *
        gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
  change _ = (_ / gramDet (coordDeriv dx F p) (coordDeriv dy F p)) * _
  exact (div_mul_cancel₀ _ hD).symm
end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLeadingRegularity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform regularity of every five-profile perturbation along a compact
set of spatial points and one full oscillation period. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma geometricProfile_real_continuousOn {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) :
    ContinuousOn (fun z : JetPolynomial.Base × ℝ => boundaryProfileMap
      (l.geometricLeadingProfile G hG hGO z.1 (z.2 : CovarianceCorrector.Period))) (S ×ˢ univ) := by
  have hd : ContDiff ℝ ∞ (lowDerivative G 1) := by
    convert ((lowJet_smooth hG).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
      (contDiff_const (c := coordinateVector 1)) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (lowJet_derivative hG 1 p).symm
  let f : JetPolynomial.Base × ℝ → LeadingProfileInput :=
    fun z => ((lowJet G z.1,z.2),lowDerivative G 1 z.1)
  have hf : Continuous f :=
    (((lowJet_smooth hG).continuous.comp continuous_fst).prodMk continuous_snd).prodMk
      (hd.continuous.comp continuous_fst)
  have hmaps : MapsTo f (S ×ˢ univ) ((O ×ˢ univ) ×ˢ univ) :=
    fun z hz => ⟨⟨hGO hz.1,mem_univ _⟩,mem_univ _⟩
  have hh := boundaryProfileMap.continuous.comp_continuousOn
    (l.leadingProfileMap_smooth.continuousOn.comp hf.continuousOn hmaps)
  apply hh.congr
  intro z hz
  exact congrArg boundaryProfileMap (l.leadingProfileMap_geometry hG hGO hz.1 z.2).symm

theorem compact_regular_profile_family {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {J : X → BoundaryProfile}
    (hJ : ContinuousOn J K) (hreg : ∀ x ∈ K, J x ∈ regularBoundaryProfiles) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ H : BoundaryProfile, ‖H-J x‖ < δ →
      H ∈ regularBoundaryProfiles := by
  have hc : IsCompact (J '' K) := hK.image_of_continuousOn hJ
  have hr : J '' K ⊆ regularBoundaryProfiles := by
    rintro _ ⟨x,hx,rfl⟩
    exact hreg x hx
  obtain ⟨δ,hδ,hnear⟩ := compact_boundary_profile_stability hc hr 1 zero_lt_one
  exact ⟨δ,hδ,fun x hx H herr => (hnear _ (mem_image_of_mem J hx) H herr).1⟩

theorem compact_leading_regularity {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {C : Set JetPolynomial.Base}
    (hC : IsCompact C) (hCS : C ⊆ S)
    (hreg : ∀ p ∈ C, ∀ t ∈ Icc (0 : ℝ) 1,
      boundaryProfileMap (l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period)) ∈
        regularBoundaryProfiles) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ C, ∀ t ∈ Icc (0 : ℝ) 1, ∀ H : BoundaryProfile,
      ‖H-boundaryProfileMap (l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period))‖ < δ →
      H ∈ regularBoundaryProfiles := by
  let f : JetPolynomial.Base × ℝ → BoundaryProfile := fun z =>
    boundaryProfileMap (l.geometricLeadingProfile G hG hGO z.1 (z.2 : CovarianceCorrector.Period))
  have hf : ContinuousOn f (C ×ˢ Icc (0 : ℝ) 1) :=
    (l.geometricProfile_real_continuousOn hG hGO).mono (fun z hz => ⟨hCS hz.1,mem_univ _⟩)
  obtain ⟨δ,hδ,hnear⟩ := compact_regular_profile_family (hC.prod isCompact_Icc) hf
    (fun z hz => hreg z.1 hz.1 z.2 hz.2)
  exact ⟨δ,hδ,fun p hp t ht H herr => hnear (p,t) ⟨hp,ht⟩ H herr⟩

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ActualCircularProfile
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed real surface profile is exactly the analytic loop's
five-profile map, including its transverse mixed derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation SurfaceJetCoordinates
open JetVelocityCoordinates

lemma actual_circular_geometric_profile {F : SmallModes.Base → Vec} (hF : ContDiff ℝ ∞ F)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (F ∘ baseEquiv)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    boundaryProfileMap (l.geometricLeadingProfile (F ∘ baseEquiv) (hF.comp baseEquiv.contDiff)
      hGO p (t : CovarianceCorrector.Period)) =
      surfaceCircularProfile F a e₁ e₂ α (baseEquiv p,t) := by
  let σ := JetPolynomial.lowJet (F ∘ baseEquiv)
  let R₀ : JetPolynomial.LowJet → ℝ := fun J => velocityRadius (normal J) (a (decode J).1)
  have hA : ContDiff ℝ ∞ (fun J : JetPolynomial.LowJet => a (decode J).1) :=
    ha.comp (contDiff_fst.comp decode_smooth)
  have hR₀ : ContDiffOn ℝ ∞ R₀ O := velocityRadius_smoothOn l.smoothNormal hA.contDiffOn (by
    intro J hJ
    have hh := l.nonzero J hJ
    rw [hamp J hJ] at hh
    exact hh)
  have he₁ := h₁.comp decode_smooth.contDiffOn hOZ
  have he₂ := h₂.comp decode_smooth.contDiffOn hOZ
  have hα₀ : ContDiffOn ℝ ∞ (fun z : JetPolynomial.LowJet × ℝ => α (decode z.1,z.2))
      (O ×ˢ univ) := hα.comp ((decode_smooth.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun _ hz => ⟨hOZ hz.1,hz.2⟩)
  rw [l.circular_geometricLeadingProfile hR₀ he₁ he₂ hα₀ hvel
    (hF.comp baseEquiv.contDiff) hGO hp t]
  let X := coordDeriv dx F
  let Y := coordDeriv dy F
  let C := coordDeriv dy (coordDeriv dy F)
  let v : SmallModes.Base → Vec := fun x => jetNormal (CollarVelocity.jetSection F x)
  let Q := X-v
  let R : SmallModes.Base → ℝ := fun x => velocityRadius (v x) (a x)
  let E₁ := e₁ ∘ CollarVelocity.jetSection F
  let E₂ := e₂ ∘ CollarVelocity.jetSection F
  let β : SmallModes.Base × ℝ → ℝ := fun z => α (CollarVelocity.jetSection F z.1,z.2)
  have hq : tangent ∘ σ = Q ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 0 - jetNormal (decode (σ x)) = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hx : (slot 1) ∘ σ = X ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 0 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hy : (slot 2) ∘ σ = Y ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 1 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hc : (slot 6) ∘ σ = C ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 4 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hr : R₀ ∘ σ = R ∘ baseEquiv := by
    funext x
    change velocityRadius (jetNormal (decode (σ x))) (a (decode (σ x)).1) = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have he1 : (e₁ ∘ decode) ∘ σ = E₁ ∘ baseEquiv := by
    funext x
    exact congrArg e₁ (decode_lowJet hF x)
  have he2 : (e₂ ∘ decode) ∘ σ = E₂ ∘ baseEquiv := by
    funext x
    exact congrArg e₂ (decode_lowJet hF x)
  have hb : (fun z : JetPolynomial.Base × ℝ => α (decode (σ z.1),z.2)) =
      fun z => β (baseEquiv z.1,z.2) := by
    funext z
    rw [show decode (σ z.1) = CollarVelocity.jetSection F (baseEquiv z.1) from decode_lowJet hF z.1]
  change circularFamilyProfile (tangent ∘ σ) ((slot 1) ∘ σ) ((slot 2) ∘ σ) ((slot 6) ∘ σ)
    (R₀ ∘ σ) ((e₁ ∘ decode) ∘ σ) ((e₂ ∘ decode) ∘ σ)
    (fun z => α (decode (σ z.1),z.2)) (JetPolynomial.coordinateVector 1) (p,t) = _
  rw [hq,hx,hy,hc,hr,he1,he2,hb]
  have hJ := hGO hp
  have hZp : CollarVelocity.jetSection F (baseEquiv p) ∈ Z := by
    rw [← decode_lowJet hF p]
    exact hOZ hJ
  have hD : gramDet (Y (baseEquiv p)) (C (baseEquiv p)) ≠ 0 := by
    have hh := l.gram_ne _ hJ
    change gramDet ((decode (σ p)).2 1) ((decode (σ p)).2 4) ≠ 0 at hh
    rw [show decode (σ p) = CollarVelocity.jetSection F (baseEquiv p) from decode_lowJet hF p] at hh
    exact hh
  have hv : ContDiffAt ℝ ∞ v (baseEquiv p) :=
    contDiffAt_realNormalPart (contDiff_real_coordDeriv hF dy).contDiffAt
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffAt
      (contDiff_real_coordDeriv hF dx).contDiffAt hD
  have hn : v (baseEquiv p) ≠ 0 ∨ a (baseEquiv p) ≠ 0 := by
    have hh := l.nonzero _ hJ
    rw [hamp _ hJ] at hh
    change jetNormal (decode (σ p)) ≠ 0 ∨ a (baseEquiv p) ≠ 0 at hh
    rw [show decode (σ p) = CollarVelocity.jetSection F (baseEquiv p) from decode_lowJet hF p] at hh
    exact hh
  have hdot : ContDiffAt ℝ ∞ (fun x => v x ⬝ᵥ v x) (baseEquiv p) :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hR : ContDiffAt ℝ ∞ R (baseEquiv p) :=
    (hdot.add (ha.contDiffAt.pow 2)).sqrt (Real.sqrt_pos.mp (velocityRadius_pos hn)).ne'
  have hσ := CollarVelocity.jetSection_smooth hF
  have hE1 := (h₁.contDiffAt (Z.isOpen.mem_nhds hZp)).comp _ hσ.contDiffAt
  have hE2 := (h₂.contDiffAt (Z.isOpen.mem_nhds hZp)).comp _ hσ.contDiffAt
  have hβ : ContDiffAt ℝ ∞ β (baseEquiv p,t) :=
    (hα.contDiffAt ((Z.isOpen.prod isOpen_univ).mem_nhds ⟨hZp,mem_univ t⟩)).comp _
      ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  rw [circularFamilyProfile_comp (Q := Q) (X := X) (Y := Y) (C := C) (R := R)
    (e₁ := E₁) (e₂ := E₂) (α := β) baseEquiv.differentiableAt
    (((contDiff_real_coordDeriv hF dx).contDiffAt.sub hv).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hR.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hE1.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hE2.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hβ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),baseEquiv.fderiv]
  have hd : baseEquiv.toContinuousLinearMap (JetPolynomial.coordinateVector 1) = dy := baseEquiv_one
  rw [hd]
  rfl

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseCircularPeriod
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic profile attached to an atlas phase chart is exactly one
of the real circular profiles used in the finite boundary construction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation SurfaceVelocityFamily VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseRealChartMap_comp_base (i : A.centers) (T : JetPolynomial.Base → JetPolynomial.Base)
    (F : M → Space) : A.phaseRealChartMap i T F ∘ baseEquiv = A.jetChartMap i F ∘ T := by
  funext p
  simp only [Function.comp_apply,phaseRealChartMap,baseEquiv.symm_apply_apply]

private lemma geometric_profile_congr {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (l : _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop O) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G H : JetPolynomial.Base → JetPolynomial.Space} (he : G = H)
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hGO : MapsTo (JetPolynomial.lowJet G) S O) (hHO : MapsTo (JetPolynomial.lowJet H) S O)
    (p : JetPolynomial.Base) (t : CovarianceCorrector.Period) :
    l.geometricLeadingProfile G hG hGO p t = l.geometricLeadingProfile H hH hHO p t := by
  subst H
  rfl

lemma phase_circular_geometric_profile (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → NormalFrame.Vec}
    (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (A.jetChartMap i F ∘ T)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    boundaryProfileMap (l.geometricLeadingProfile (A.jetChartMap i F ∘ T)
        ((A.jetChartMap_smooth i hF).comp hT) hGO p (t : CovarianceCorrector.Period)) =
      surfaceCircularProfile (A.phaseRealChartMap i T F) a e₁ e₂ α (baseEquiv p,t) := by
  have hcomp := A.phaseRealChartMap_comp_base i T F
  have hGO' : MapsTo (JetPolynomial.lowJet (A.phaseRealChartMap i T F ∘ baseEquiv)) S O := by
    simpa only [hcomp] using hGO
  have he := l.actual_circular_geometric_profile (A.phaseRealChartMap_smooth i hT hF)
    ha hOZ hamp h₁ h₂ hα hvel hGO' hp t
  have heq := geometric_profile_congr l hcomp
    ((A.phaseRealChartMap_smooth i hT hF).comp baseEquiv.contDiff)
    ((A.jetChartMap_smooth i hF).comp hT) hGO' hGO p (t : CovarianceCorrector.Period)
  exact (congrArg boundaryProfileMap heq).symm.trans he


end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentCircularBoundary
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularBoundaryDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularBoundaryFiberSpace
local instance independent_exactCircularBoundaryDualSmul_r2b8a52_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularBoundaryFiberNormed
local instance independent_exactCircularBoundarySectionNormed_r2b8a52_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_exactCircularBoundarySectionSpace_r2b8a52_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_exact_circular_primitive_boundary_oai [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {Z : TopologicalSpace.Opens GeometricJet} (hOZ : (O : Set LowJet) ⊆ jetDomain Z)
    {e₁ e₂ : GeometricJet → NormalFrame.Vec}
    (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    {ι : Type*} {Curves : ι → Set SmallModes.Base} {b c k : ι → SmallModes.Base → ℝ}
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactive : ∀ j x, x ∈ Curves j → A₀.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hcurv : ∀ j x, x ∈ Curves j → k j x ≤
      RealModes.coordinateGauss (fun y => A₀.phaseMetricRead i e.symm h y 0)
        (fun y => A₀.phaseMetricRead i e.symm h y 1)
        (fun y => A₀.phaseMetricRead i e.symm h y 2) x)
    (η : ℝ) (hη : 0 < η)
    (havoid : ∀ z : ℝ, 0 < z → z < η → ∀ j x, x ∈ Curves j →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : SmallModes.Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F)
        a e₁ e₂ α (x,t)‖ < η →
      k j x ≤ RealModes.coordinateGauss (RealModes.realMetric G SmallModes.dx SmallModes.dx)
        (RealModes.realMetric G SmallModes.dx SmallModes.dy) (RealModes.realMetric G SmallModes.dy SmallModes.dy) p →
      RealModes.realSecondForm G (b j x,c j x) (b j x,c j x) p ≠ 0 ∧
      VelocityFrame.normalize (RealModes.realSecondForm G (b j x,c j x) (b j x,c j x) p) ≠
        -profilePreferred (realBoundaryProfile G z p))
    {E : Set SmallModes.Base}
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hactiveE : ∀ x ∈ E, A₀.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hdetE : ∀ x ∈ E, A₀.phaseMetricRead i e.symm h x 0 * A₀.phaseMetricRead i e.symm h x 2 -
      (A₀.phaseMetricRead i e.symm h x 1)^2 ≠ 0)
    (B slopeBound : ℝ)
    (hcurvE : ∀ x ∈ E, -B ≤ RealModes.coordinateGauss
      (fun y => A₀.phaseMetricRead i e.symm h y 0)
      (fun y => A₀.phaseMetricRead i e.symm h y 1)
      (fun y => A₀.phaseMetricRead i e.symm h y 2) x)
    (hcross : ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : SmallModes.Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F)
        a e₁ e₂ α (x,t)‖ < η → ∀ κ : ℝ,
      RealModes.coordinateGauss (RealModes.realMetric G SmallModes.dx SmallModes.dx)
        (RealModes.realMetric G SmallModes.dx SmallModes.dy) (RealModes.realMetric G SmallModes.dy SmallModes.dy) p =
        κ*NormalFrame.gramDet (SmallModes.coordDeriv SmallModes.dx G p) (SmallModes.coordDeriv SmallModes.dy G p) →
      -B ≤ RealModes.coordinateGauss (RealModes.realMetric G SmallModes.dx SmallModes.dx)
        (RealModes.realMetric G SmallModes.dx SmallModes.dy) (RealModes.realMetric G SmallModes.dy SmallModes.dy) p →
      ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        0 < orderedCrossing G (1,r) (1,s) p κ ∧ 0 < orderedCrossing G (1,s) (1,r) p κ ∧
        ((0 < RealModes.realSecondForm G (1,r) (1,r) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p) ∧
          0 < RealModes.realSecondForm G (1,s) (1,s) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p)) ∨
         (0 < RealModes.realSecondForm G (1,r) (1,r) p ⬝ᵥ RealModes.realSecondForm G (1,s) (1,s) p ∧
          ∃ w : NormalFrame.Vec, profilePreferred (realBoundaryProfile G z p) ⬝ᵥ w = 0 ∧
            0 < RealModes.realSecondForm G (1,r) (1,r) p ⬝ᵥ w ∧
            0 < RealModes.realSecondForm G (1,s) (1,s) p ⬝ᵥ w)))
    (hregular : ∀ p ∈ C, ∀ t ∈ Icc (0 : ℝ) 1,
      surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F) a e₁ e₂ α (baseEquiv p,t) ∈
        regularBoundaryProfiles) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C, realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p) ∈
        regularBoundaryProfiles) ∧
      (∀ j x, x ∈ Curves j →
        RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W) (b j x,c j x) (b j x,c j x) x ≠ 0 ∧
        VelocityFrame.normalize (RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W)
          (b j x,c j x) (b j x,c j x) x) ≠
          -profilePreferred (realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z x)) ∧
      (∀ x ∈ E, ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        let H := A₀.phaseRealChartMap i e.symm W
        let κ := RealModes.coordinateGaussianCurvature
          (RealModes.realMetric H SmallModes.dx SmallModes.dx)
          (RealModes.realMetric H SmallModes.dx SmallModes.dy)
          (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
        0 < orderedCrossing H (1,r) (1,s) x κ ∧ 0 < orderedCrossing H (1,s) (1,r) x κ ∧
        ((0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x) ∧
          0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x)) ∨
         (0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ RealModes.realSecondForm H (1,s) (1,s) x ∧
          ∃ w : NormalFrame.Vec, profilePreferred (realBoundaryProfile H z x) ⬝ᵥ w = 0 ∧
            0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ w ∧
            0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ w))) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  intro ε hε ζ hζ
  let hGO : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S O := fun _ hp => hQO (hFQ hp)
  have hreg : ∀ p ∈ C, ∀ t ∈ Icc (0 : ℝ) 1,
      boundaryProfileMap (l.geometricLeadingProfile (A₀.jetChartMap i F ∘ e.symm)
        ((A₀.jetChartMap_smooth i hF).comp hi) hGO p (t : Period)) ∈ regularBoundaryProfiles := by
    intro p hp t ht
    rw [A₀.phase_circular_geometric_profile i hF hi ha hOZ l hamp h₁ h₂ hα hvel hGO (hCS hp).1 t]
    exact hregular p hp t ht
  obtain ⟨δreg,hδreg,hnearreg⟩ := l.compact_leading_regularity
    ((A₀.jetChartMap_smooth i hF).comp hi) hGO hC (fun p hp => (hCS hp).1) hreg
  let δ := min ε (min η δreg)
  have hδ : 0 < δ := lt_min hε (lt_min hη hδreg)
  have hδη : δ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ δreg := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hgeometry,hprofiles,G,hG,hslow,V,hV,hcorrection,hext⟩ :=
    data.independent_exact_circular_primitive_profiles A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
      l ha hamp hOZ h₁ h₂ hα hvel S hSc hTS hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy
      h htarget hC hCS δ hδ (min ζ η) (lt_min hζ hη)
  refine ⟨z,hz,hzζ.trans_le (min_le_left _ _),hz1,W,hW,hgeometry,?_,?_,?_,G,hG,?_,V,hV,hcorrection,hext⟩
  · intro p hp
    obtain ⟨t,ht,herror⟩ := hprofiles p hp
    have heq := A₀.phase_circular_geometric_profile i hF hi ha hOZ l hamp h₁ h₂ hα hvel hGO (hCS hp).1 t
    rw [← heq] at herror
    exact hnearreg p hp t ht _ (herror.trans_le hδr)
  · intro j x hx
    obtain ⟨t,ht,herror⟩ := hprofiles (baseEquiv.symm x) (hCurveC j x hx)
    rw [baseEquiv.apply_symm_apply] at herror
    apply havoid z hz (hzζ.trans_le (min_le_right _ _)) j x hx t ht
      (A₀.phaseRealChartMap i e.symm W) (A₀.phaseRealChartMap_smooth i hi hW.1) x
      (herror.trans_le hδη)
    rw [A₀.phaseGauss_isometry i hi hW (hactive j x hx)]
    exact hcurv j x hx
  · intro x hx r s hr hs
    obtain ⟨t,ht,herror⟩ := hprofiles (baseEquiv.symm x) (hEC x hx)
    rw [baseEquiv.apply_symm_apply] at herror
    let H := A₀.phaseRealChartMap i e.symm W
    have hDH : NormalFrame.gramDet (SmallModes.coordDeriv SmallModes.dx H x)
        (SmallModes.coordDeriv SmallModes.dy H x) ≠ 0 := by
      rw [A₀.phaseMetricRead_isometry_det i hi hW (hactiveE x hx)]
      exact hdetE x hx
    apply hcross z hz (hzζ.trans_le (min_le_right _ _)) x hx t ht H
      (A₀.phaseRealChartMap_smooth i hi hW.1) x (herror.trans_le hδη)
      _ (RealModes.coordinateGauss_eq_curvature_mul H x hDH) _ r s hr hs
    rw [A₀.phaseGauss_isometry i hi hW (hactiveE x hx)]
    exact hcurvE x hx
  · exact fun j => (hslow j).mono_const (min_le_left _ _)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_boundary_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_boundary_oai.{u_1, u_2}
