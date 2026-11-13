-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:34.989209+00:00
-- url     : https://prove2.me/submissions/61126b16-80e6-40b6-8cd9-79925f055a3c

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
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
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalProjection
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.NormalFrame

lemma gramDet_change_basis (X Y : RVec 4) (a b c d : ℝ) :
    NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) =
      (a*d-b*c)^2 * NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
  ring

lemma realNormalPart_linear (X Y : RVec 4) :
    IsLinearMap ℝ (realNormalPart X Y) := by
  constructor
  · intro W Z
    ext i
    simp [realNormalPart, dotProduct_add, Pi.add_apply]
    ring
  · intro s W
    ext i
    simp [realNormalPart, dotProduct_smul, Pi.smul_apply]
    ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma real_second_coordDeriv {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) (v w : Base) :
    coordDeriv v (coordDeriv w F) p = fderiv ℝ (fderiv ℝ F) p v w := by
  have h := (hF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ F q) w) p) v = _
  rw [h]
  simp

lemma real_second_coordDeriv_comm {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) : coordDeriv v (coordDeriv w F) p = coordDeriv w (coordDeriv v F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  rw [real_second_coordDeriv hd, real_second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hF.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

lemma coordDeriv_eq_basis {n : ℕ} (F : RField n) (v p : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  conv_lhs => arg 1; rw [base_eq_basis v]
  simp [coordDeriv]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma second_coordDeriv_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v w p : Base) : coordDeriv v (coordDeriv w F) p =
      (v.1*w.1) • coordDeriv dx (coordDeriv dx F) p +
      (v.1*w.2+v.2*w.1) • coordDeriv dx (coordDeriv dy F) p +
      (v.2*w.2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis w]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    realSecondForm F v w p =
      (v.1*w.1) • realSecondTensor F p 0 +
      (v.1*w.2+v.2*w.1) • realSecondTensor F p 1 +
      (v.2*w.2) • realSecondTensor F p 2 := by
  unfold realSecondForm
  rw [second_coordDeriv_bilinear hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [realSecondTensor, realSecondForm]

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
local instance coordinateFiberSpace_r23e10a_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance chartReadSectionNormed_r23e10a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r23e10a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance metricReadExactDualSmul_r23e10a_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactFiberNormed
local instance metricReadExactSectionNormed_r23e10a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadExactSectionSpace_r23e10a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTensorPullback
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma tensorCoordinateJacobian_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (k l : Fin 3) : ContDiff ℝ ∞ (tensorCoordinateJacobian T k l) := by
  have hd (v : Base) (a : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ T x v a) :=
    contDiff_pi.mp ((hT.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const) a
  fin_cases l
  · exact (hd _ 0).mul (hd _ 0)
  · exact ((hd _ 0).mul (hd _ 1)).add ((hd _ 1).mul (hd _ 0))
  · exact (hd _ 1).mul (hd _ 1)

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialRepresentation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed coordinate representatives of the same global polynomial
tensor. These are derived from the actual read/restore maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepFiberSpace
local instance polyRepDualSmul_r23e10a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepFiberNormed
local instance polyRepSectionNormed_r23e10a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polyRepSectionSpace_r23e10a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorChartRead_sum {ι : Type*} [Fintype ι] (i : A.centers)
    (u : ι → ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (∑ k, u k) = ∑ k, A.tensorChartRead i (u k) := by
  classical
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_mem hx,bundleComponent,Finset.sum_apply,map_sum,Finset.smul_sum]
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_notMem hx,map_zero,Finset.sum_apply,Finset.sum_const_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasMetricLocalModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local coordinate models of the complete perturbed global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricLocalDualAdd
local instance metricLocalFiberNormed_r23e10a_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricLocalFiberSpace_r23e10a_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricLocalDualSmul_r23e10a_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricLocalSectionNormed_r23e10a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricLocalSectionSpace_r23e10a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorChartRead_add (i : A.centers) (u v : ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (u+v) = A.tensorChartRead i u+A.tensorChartRead i v := by
  have h := A.tensorChartRead_sum i ![u,v]
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasSelfTensorRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A tensor restored in a chart reads back exactly where its outer cutoff is one. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.selfReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.selfReadFiberSpace
local instance selfReadDualSmul_r23e10a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.selfReadFiberNormed
local instance selfReadSectionNormed_r23e10a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance selfReadSectionSpace_r23e10a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorChartRead_restore_self (i : A.centers) (f : Base → PhaseMean.Tensor)
    {x : Base} (hx : x ∈ (chart (i : M)).target)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    A.tensorChartRead i (A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f y))) x = f x := by
  have hb := A.tensorTriv_domain i ((chart (i : M)).map_target hx)
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i (A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f y)))) x) = _
  rw [localize,indicator_of_mem hx]
  simp only [ho,one_pow,one_smul,bundleComponent,bundleRestore,
    (chart (i : M)).right_inv hx]
  rw [(A.tensorTriv i).continuousLinearMapAt_symmL hb,fiberToThree_fromThree]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorCoordinatePullbackBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed nonlinear coordinate changes preserve weighted tensor error
bounds with a constant independent of the fast scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma tensorCoordinatePullbackValue_sum (T : Base → Base) (x : Base) :
    tensorCoordinatePullbackValue T x =
      ∑ k : Fin 3, ∑ l : Fin 3,
        tensorCoordinateJacobian T k l x • tensorCoordinateMatrixUnit k l := by
  ext A k
  simp only [sum_apply,smul_apply,
    Finset.sum_apply,Pi.smul_apply,tensorCoordinateMatrixUnit,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
    Pi.single_apply]
  simp only [mul_ite,mul_one,mul_zero]
  have hi (j : Fin 3) :
      (∑ l : Fin 3, if k = j then tensorCoordinateJacobian T j l x * A l else 0) =
        if k = j then ∑ l : Fin 3, tensorCoordinateJacobian T j l x * A l else 0 := by
    split_ifs <;> simp_all
  simp_rw [hi]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  exact (tensorCoordinateJacobian_sum T x A k).symm

lemma tensorCoordinatePullbackValue_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (tensorCoordinatePullbackValue T) := by
  have he : tensorCoordinatePullbackValue T = fun x =>
      ∑ k : Fin 3, ∑ l : Fin 3,
        tensorCoordinateJacobian T k l x • tensorCoordinateMatrixUnit k l :=
    funext (tensorCoordinatePullbackValue_sum T)
  rw [he]
  apply ContDiff.sum
  intro k _
  apply ContDiff.sum
  intro l _
  exact (tensorCoordinateJacobian_smooth hT k l).smul contDiff_const

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
attribute [-instance] _root_.instVAddIntReal_solutions
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

lemma dot_normalize_zero {v w : Vec} (h : w ⬝ᵥ v = 0) : w ⬝ᵥ normalize v = 0 := by
  simp [normalize, dotProduct_smul, h]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalGeometry
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular derivative contributes only to the complementary normal component. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma dot_normalPart_eq {X Y w m : Vec} (hX : m ⬝ᵥ X = 0) (hY : m ⬝ᵥ Y = 0) :
    m ⬝ᵥ realNormalPart X Y w = m ⬝ᵥ w := by
  simp [realNormalPart, dotProduct_sub, dotProduct_smul, hX, hY]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCoordinateData
attribute [-instance] _root_.instVAddIntReal_solutions
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

lemma dot_normalize_self {v : Vec} (hv : v ≠ 0) :
    v ⬝ᵥ normalize v = Real.sqrt (v ⬝ᵥ v) := by
  have hp := dot_self_pos hv
  have hn := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, dotProduct_smul, smul_eq_mul]
  apply (inv_mul_eq_iff_eq_mul₀ hn).mpr
  nlinarith [Real.sq_sqrt hp.le]

end ClosedSurfaceR4.VelocityFrame

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

lemma phaseMetricRead_smooth (i : A.centers) {T : JetPolynomial.Base → JetPolynomial.Base}
    (hT : ContDiff ℝ ∞ T) (g : SmoothMetric M) : ContDiff ℝ ∞ (A.phaseMetricRead i T g) :=
  ((tensorCoordinatePullbackValue_smooth hT).clm_apply
    ((A.tensorChartRead_smooth i g.contMDiff).comp hT)).comp baseEquiv.symm.contDiff

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OrderedBoundaryInvariant
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's ordered crossing expression in coordinates adapted to
the boundary curve, for the actual second fundamental form. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes SmallModes

theorem orderedCrossing_dy {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : realSecondForm F dy dy p ≠ 0) (b c κ : ℝ) :
    orderedCrossing F dy (b, c) p κ =
      (b * (coordDeriv dy (coordDeriv dx F) p ⬝ᵥ normalize (realSecondForm F dy dy p)) +
        c * Real.sqrt (realSecondForm F dy dy p ⬝ᵥ realSecondForm F dy dy p)) ^ 2 +
      (κ * gramDet (coordDeriv dx F p) (coordDeriv dy F p)) * b ^ 2 := by
  let B := realSecondForm F dy dy p
  let n := normalize B
  have hp := realNormalPart_perp (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dy (coordDeriv dy F) p) hD
  have hXn : n ⬝ᵥ coordDeriv dx F p = 0 :=
    (dotProduct_comm _ _).trans (dot_normalize_zero hp.1)
  have hYn : n ⬝ᵥ coordDeriv dy F p = 0 :=
    (dotProduct_comm _ _).trans (dot_normalize_zero hp.2)
  have hm : realSecondForm F dx dy p ⬝ᵥ n = coordDeriv dy (coordDeriv dx F) p ⬝ᵥ n := by
    rw [realSecondForm, dotProduct_comm, dot_normalPart_eq hXn hYn, dotProduct_comm,
      real_second_coordDeriv_comm hF p dx dy]
  have hs : B ⬝ᵥ n = Real.sqrt (B ⬝ᵥ B) := dot_normalize_self hB
  have hBvw : realSecondForm F dy (b, c) p = b • realSecondForm F dx dy p + c • B := by
    rw [realSecondForm_bilinear hF]
    simp [dy, realSecondTensor, B]
  have hW : coordDeriv (b, c) F p = b • coordDeriv dx F p + c • coordDeriv dy F p :=
    coordDeriv_eq_basis F (b, c) p
  have hg : gramDet (coordDeriv dy F p) (coordDeriv (b, c) F p) =
      b ^ 2 * gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
    rw [hW]
    convert gramDet_change_basis (coordDeriv dx F p) (coordDeriv dy F p) 0 1 b c using 1 <;>
      simp
  change (realSecondForm F dy (b, c) p ⬝ᵥ n) ^ 2 + _ = _
  rw [hBvw, add_dotProduct, smul_dotProduct, smul_dotProduct, hm, hs, hg]
  change (b * _ + c * _) ^ 2 + _ = _
  ring

end ClosedSurfaceR4.VelocityFrame

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AmplitudeBoundaryMetric
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a zero of a nonnegative smooth amplitude, its square has zero two-jet.
Thus adding the primitive metric does not change the boundary Gauss scalar. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes

private lemma scalar_partial_smooth_p1 {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) (v : Base) :
    ContDiff ℝ ∞ (coordDeriv v f) :=
  (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

private lemma scalar_partial_mul {f g : Base → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v p : Base) :
    coordDeriv v (fun x => f x*g x) p = coordDeriv v f p*g p+f p*coordDeriv v g p := by
  unfold coordDeriv
  rw [fderiv_fun_mul (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

private lemma scalar_partial_add {f g : Base → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v p : Base) :
    coordDeriv v (fun x => f x+g x) p = coordDeriv v f p+coordDeriv v g p := by
  unfold coordDeriv
  rw [fderiv_fun_add (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  rfl

lemma square_twoJet_zero {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) {p : Base}
    (hzero : a p = 0) (hnonneg : ∀ᶠ q in 𝓝 p, 0 ≤ a q) :
    (fun q => (a q)^2) p = 0 ∧
      (∀ v, coordDeriv v (fun q => (a q)^2) p = 0) ∧
      ∀ v w, coordDeriv v (coordDeriv w (fun q => (a q)^2)) p = 0 := by
  have hmin : IsLocalMin a p := by simpa only [IsLocalMin,IsMinFilter,hzero] using hnonneg
  have hda : fderiv ℝ a p = 0 := hmin.fderiv_eq_zero
  have hd (v : Base) : coordDeriv v a p = 0 := by simp [coordDeriv,hda]
  have heq (w : Base) : coordDeriv w (fun q => (a q)^2) =
      fun q => coordDeriv w a q*a q+a q*coordDeriv w a q := by
    funext q
    simpa only [pow_two] using scalar_partial_mul ha ha w q
  refine ⟨by simp [hzero],?_,?_⟩
  · intro v
    rw [heq]
    simp [hzero]
  · intro v w
    rw [heq,scalar_partial_add ((scalar_partial_smooth_p1 ha w).mul ha)
      (ha.mul (scalar_partial_smooth_p1 ha w)),
      scalar_partial_mul (scalar_partial_smooth_p1 ha w) ha,
      scalar_partial_mul ha (scalar_partial_smooth_p1 ha w)]
    simp [hzero,hd]

lemma factor_square_twoJet_zero {a f : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hf : ContDiff ℝ ∞ f) {p : Base} (hzero : a p = 0)
    (hnonneg : ∀ᶠ q in 𝓝 p, 0 ≤ a q) :
    (fun q => f q*(a q)^2) p = 0 ∧
      (∀ v, coordDeriv v (fun q => f q*(a q)^2) p = 0) ∧
      ∀ v w, coordDeriv v (coordDeriv w (fun q => f q*(a q)^2)) p = 0 := by
  obtain ⟨hz,hd,hdd⟩ := square_twoJet_zero ha hzero hnonneg
  have hsq : ContDiff ℝ ∞ (fun q => (a q)^2) := ha.pow 2
  have heq (w : Base) : coordDeriv w (fun q => f q*(a q)^2) =
      fun q => coordDeriv w f q*(a q)^2+f q*coordDeriv w (fun q => (a q)^2) q := by
    funext q
    exact scalar_partial_mul hf hsq w q
  refine ⟨by simp [hzero],?_,?_⟩
  · intro v
    rw [heq]
    simp only [hz,hd,mul_zero,add_zero]
  · intro v w
    rw [heq,scalar_partial_add ((scalar_partial_smooth_p1 hf w).mul hsq)
      (hf.mul (scalar_partial_smooth_p1 hsq w)),
      scalar_partial_mul (scalar_partial_smooth_p1 hf w) hsq,
      scalar_partial_mul hf (scalar_partial_smooth_p1 hsq w)]
    simp only [hz,hd,hdd,mul_zero,add_zero]

lemma coordinateGauss_add_factor_square_boundary {E F G a f : Base → ℝ}
    (hE : ContDiff ℝ ∞ E) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) {p : Base}
    (hzero : a p = 0) (hnonneg : ∀ᶠ q in 𝓝 p, 0 ≤ a q) :
    coordinateGauss (fun q => E q+f q*(a q)^2) F G p = coordinateGauss E F G p := by
  obtain ⟨hz,hd,hdd⟩ := factor_square_twoJet_zero ha hf hzero hnonneg
  have hsq : ContDiff ℝ ∞ (fun q => f q*(a q)^2) := hf.mul (ha.pow 2)
  have hfirst (v : Base) : coordDeriv v (fun q => E q+f q*(a q)^2) =
      fun q => coordDeriv v E q+coordDeriv v (fun q => f q*(a q)^2) q := by
    funext q
    exact scalar_partial_add hE hsq v q
  have hsecond (v w : Base) : coordDeriv v (coordDeriv w (fun q => E q+f q*(a q)^2)) p =
      coordDeriv v (coordDeriv w E) p := by
    rw [hfirst,scalar_partial_add (scalar_partial_smooth_p1 hE w)
      (scalar_partial_smooth_p1 hsq w),hdd,add_zero]
  unfold coordinateGauss
  rw [hsecond]
  simp only [hfirst,hd,hz,add_zero]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveTensorPullback
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.PhaseMean
open SmallModes

lemma evaluate_pullback (L : Base →L[ℝ] Base) (H : Tensor) (v w : Base) :
    evaluate (pullback L H) v w = evaluate H (L v) (L w) := by
  have hL (u : Base) : L u = u.1 • L dx + u.2 • L dy := by
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext <;> simp [dx,dy]
  change evaluate H (L dx) (L dx) * v.1 * w.1 +
    evaluate H (L dx) (L dy) * (v.1*w.2+v.2*w.1) +
    evaluate H (L dy) (L dy) * v.2 * w.2 = evaluate H (L v) (L w)
  rw [hL v,hL w]
  simp only [evaluate,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InverseTensorPullback
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor pullback cancels along the actual local phase inverse. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.JetPolynomial

lemma tensorCoordinatePullback_inverse
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : Base} (hp : p ∈ e.target) (H : PhaseMean.Tensor) :
    tensorCoordinatePullbackValue e.symm p (tensorCoordinatePullbackValue e (e.symm p) H) = H := by
  have hinv : e ∘ e.symm =ᶠ[𝓝 p] id := by
    filter_upwards [e.open_target.mem_nhds hp] with q hq
    exact e.right_inv hq
  have hchain : (fderiv ℝ e (e.symm p)).comp (fderiv ℝ e.symm p) =
      ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
      hinv.fderiv_eq,fderiv_id]
  have hcancel (v : SmallModes.Base) :
      tensorCoordinateDerivative e (e.symm p) (tensorCoordinateDerivative e.symm p v) = v := by
    change planeCoordinateIsometry
      ((fderiv ℝ e (e.symm p)) (planeCoordinateIsometry.symm
        (planeCoordinateIsometry ((fderiv ℝ e.symm p) (planeCoordinateIsometry.symm v))))) = v
    rw [LinearIsometryEquiv.symm_apply_apply]
    change planeCoordinateIsometry (((fderiv ℝ e (e.symm p)).comp
      (fderiv ℝ e.symm p)) (planeCoordinateIsometry.symm v)) = v
    rw [hchain,ContinuousLinearMap.id_apply,LinearIsometryEquiv.apply_symm_apply]
  funext j
  change PhaseMean.evaluate (PhaseMean.pullback (tensorCoordinateDerivative e (e.symm p)) H)
    (tensorCoordinateDerivative e.symm p (PhaseMean.firstDirection j))
    (tensorCoordinateDerivative e.symm p (PhaseMean.secondDirection j)) = H j
  rw [PhaseMean.evaluate_pullback,hcancel,hcancel]
  fin_cases j <;> simp [PhaseMean.evaluate,PhaseMean.firstDirection,PhaseMean.secondDirection,SmallModes.dx,SmallModes.dy]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveMetricRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A tensor restored in a chart reads back exactly where its outer cutoff is one. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveReadFiberSpace
local instance primitiveReadDualSmul_r23e10a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveReadFiberNormed
local instance primitiveReadSectionNormed_r23e10a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveReadSectionSpace_r23e10a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma phaseMetricRead_primitive (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (g h : SmoothMetric M) (χ : Base → ℝ) (a : SmallModes.Base → ℝ)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {p : Base} (hp : p ∈ e.target) (hactive : A.chartWeight i (e.symm p) ≠ 0) :
    A.phaseMetricRead i e.symm h (baseEquiv p) =
      A.phaseMetricRead i e.symm g (baseEquiv p) +
        χ (e.symm p) • ![(a (baseEquiv p))^2,0,0] := by
  have hx : e.symm p ∈ (chart (i : M)).target := by
    by_contra hn
    simp [chartWeight,hn] at hactive
  have hw : A.weight i ((chart (i : M)).symm (e.symm p)) ≠ 0 := by
    simpa only [chartWeight,indicator_of_mem hx] using hactive
  have ho := A.outer_one i _ (subset_tsupport (A.weight i) hw)
  simp only [phaseMetricRead,baseEquiv.symm_apply_apply]
  rw [htarget,A.tensorChartRead_add,Pi.add_apply,map_add,
    A.tensorChartRead_restore_self i _ hx ho,localizedTensorPullback,map_smul,e.right_inv hp,
    tensorCoordinatePullback_inverse e he hi hp]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveBoundaryGauss
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A tensor restored in a chart reads back exactly where its outer cutoff is one. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadFiberSpace
local instance boundaryGaussReadDualSmul_r23e10a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadFiberNormed
local instance boundaryGaussReadSectionNormed_r23e10a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance boundaryGaussReadSectionSpace_r23e10a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma phaseMetricRead_primitive_germ (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (g h : SmoothMetric M) (χ : Base → ℝ) (a : SmallModes.Base → ℝ)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {x : SmallModes.Base} (hx : baseEquiv.symm x ∈ e.target)
    (hactive : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0) :
    A.phaseMetricRead i e.symm h =ᶠ[𝓝 x] fun y => A.phaseMetricRead i e.symm g y +
      χ (e.symm (baseEquiv.symm y)) • ![(a y)^2,0,0] := by
  have ht := (e.open_target.preimage baseEquiv.symm.continuous).mem_nhds hx
  have hn := (isOpen_ne.preimage ((A.chartWeight_smooth i).continuous.comp
    (hi.continuous.comp baseEquiv.symm.continuous))).mem_nhds hactive
  filter_upwards [ht,hn] with y hy hya
  have hh := A.phaseMetricRead_primitive i e he hi g h χ a htarget hy hya
  simpa only [baseEquiv.apply_symm_apply] using hh

lemma phase_primitive_gauss_zero (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (g h : SmoothMetric M) {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {x : SmallModes.Base} (hx : baseEquiv.symm x ∈ e.target)
    (hactive : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hz : a x = 0) (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ a y) :
    RealModes.coordinateGauss (fun y => A.phaseMetricRead i e.symm h y 0)
      (fun y => A.phaseMetricRead i e.symm h y 1) (fun y => A.phaseMetricRead i e.symm h y 2) x =
    RealModes.coordinateGauss (fun y => A.phaseMetricRead i e.symm g y 0)
      (fun y => A.phaseMetricRead i e.symm g y 1) (fun y => A.phaseMetricRead i e.symm g y 2) x := by
  have heq := A.phaseMetricRead_primitive_germ i e he hi g h χ a htarget hx hactive
  have h0 := heq.mono (fun y hy => congrFun hy 0)
  have h1 : (fun y => A.phaseMetricRead i e.symm h y 1) =ᶠ[𝓝 x]
      (fun y => A.phaseMetricRead i e.symm g y 1) :=
    heq.mono (fun y hy => by simpa using congrFun hy 1)
  have h2 : (fun y => A.phaseMetricRead i e.symm h y 2) =ᶠ[𝓝 x]
      (fun y => A.phaseMetricRead i e.symm g y 2) :=
    heq.mono (fun y hy => by simpa using congrFun hy 2)
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero] at h0
  rw [RealModes.coordinateGauss_germ h0 h1 h2]
  exact RealModes.coordinateGauss_add_factor_square_boundary
    (contDiff_pi.mp (A.phaseMetricRead_smooth i hi g) 0) ha
    (hχ.comp (hi.comp baseEquiv.symm.contDiff)) hz hnonneg

/-- At a zero of the amplitude, the original immersion's ordered crossing
invariant is exactly the scalar boundary expression for the new metric. -/
lemma phase_primitive_boundary_crossing_oai (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (h : SmoothMetric M) {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {x : SmallModes.Base} (hx : baseEquiv.symm x ∈ e.target)
    (hactive : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hz : a x = 0) (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ a y)
    (hD : NormalFrame.gramDet
      (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i e.symm F) x)
      (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i e.symm F) x) ≠ 0)
    (hB : RealModes.realSecondForm (A.phaseRealChartMap i e.symm F)
      SmallModes.dy SmallModes.dy x ≠ 0) (b c : ℝ) :
    let H := A.phaseRealChartMap i e.symm F
    let κ := RealModes.coordinateGaussianCurvature
      (RealModes.realMetric H SmallModes.dx SmallModes.dx)
      (RealModes.realMetric H SmallModes.dx SmallModes.dy)
      (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
    VelocityFrame.orderedCrossing H SmallModes.dy (b,c) x κ =
      ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx H) x ⬝ᵥ
        VelocityFrame.normalize (RealModes.realSecondForm H SmallModes.dy SmallModes.dy x))*b +
        Real.sqrt (RealModes.realSecondForm H SmallModes.dy SmallModes.dy x ⬝ᵥ
          RealModes.realSecondForm H SmallModes.dy SmallModes.dy x)*c)^2 +
        (RealModes.coordinateGauss (fun y => A.phaseMetricRead i e.symm h y 0)
          (fun y => A.phaseMetricRead i e.symm h y 1)
          (fun y => A.phaseMetricRead i e.symm h y 2) x)*b^2 := by
  dsimp only
  rw [VelocityFrame.orderedCrossing_dy (A.phaseRealChartMap_smooth i hi hF.1) x hD hB,
    ← RealModes.coordinateGauss_eq_curvature_mul _ _ hD,
    A.phaseGauss_isometry i hi hF hactive,
    ← A.phase_primitive_gauss_zero i e he hi g h hχ ha htarget hx hactive hz hnonneg]
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing_oai.{u_1}
