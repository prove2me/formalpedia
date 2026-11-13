-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:03:37.568349+00:00
-- url     : https://prove2.me/submissions/eef78419-e2bc-44c2-82ab-814f795ecc81

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q + G q) p = coordDeriv v F p + coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_add hF hG, add_apply]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

lemma WeightedBound.neg {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun x => -f x) := by
  simpa using hb.const_smul hU hf (-1)

lemma WeightedBound.sub {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (C + D) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hbf.add hU hs hf hg.neg (hbg.neg hU hg)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedModes
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
open ClosedSurfaceR4.QuadraticMean (realPartCLM)

lemma realMetric_add {n : ℕ} {F U : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hU : DifferentiableAt ℝ U p) (v w : Base) :
    realMetric (fun q => F q + U q) v w p =
      realMetric F v w p + realLinearized F U v w p + realMetric U v w p := by
  unfold realMetric realLinearized
  rw [partial_add hF hU v, partial_add hF hU w]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (coordDeriv v U p)]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
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
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearizedTensor_apply {n : ℕ} (F U : RField n) (p : Base) (i : Fin 3) :
    realLinearizedTensor F U p i = realLinearized F U (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DoubleModes
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
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realMetricTensor_add {n : ℕ} {F X : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hX : DifferentiableAt ℝ X p) :
    realMetricTensor (fun q => F q + X q) p =
      realMetricTensor F p + realLinearizedTensor F X p + realMetricTensor X p := by
  ext i
  simp only [Pi.add_apply, realMetricTensor_apply, realLinearizedTensor_apply,
    realMetric_add hF hX]


end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorBounds
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
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_realLinearizedTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {X Y : RField n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (realLinearizedTensor X Y) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [realLinearizedTensor_apply, realLinearized]
  exact (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
    (contDiffOn_coordDeriv_vector hU hY _)).add
    (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
      (contDiffOn_coordDeriv_vector hU hY _))

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricCalculus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact metric identities for actual smooth maps on the surface. The
finite-sum identity retains every cross term between distinct chart modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma surfaceDifferential_add {F U : M → V} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ,V) F p)
    (hU : MDifferentiableAt planeModel 𝓘(ℝ,V) U p) :
    surfaceDifferential (F+U) p = surfaceDifferential F p + surfaceDifferential U p :=
  mfderiv_add hF hU

lemma inducedForm_add {F U : M → V} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ,V) F p)
    (hU : MDifferentiableAt planeModel 𝓘(ℝ,V) U p) (v w : TangentSpace planeModel p) :
    inducedForm (F+U) p v w - inducedForm F p v w =
      linearMetricForm F U p v w + inducedForm U p v w := by
  unfold inducedForm linearMetricForm
  rw [surfaceDifferential_add hF hU]
  simp only [add_apply,inner_add_left,inner_add_right]
  ring

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricTensor
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric tensors and cross tensors of manifold displacements.
Cross tensors vanish away from the intersection of the two supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

local instance metricTensorFiberNormed_r7ff60a_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricTensorFiberSpace_r7ff60a_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTensorDualAdd
local instance metricTensorDualSmul_r7ff60a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricTensorSectionNormed_r7ff60a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricTensorSectionSpace_r7ff60a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma inducedTensor_add {F U : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hU : ContMDiff planeModel spaceModel ∞ U) :
    inducedTensor (F+U) = inducedTensor F + linearMetricTensor F U + inducedTensor U := by
  funext p
  ext v w
  have h := inducedForm_add ((hF p).mdifferentiableAt (by simp))
    ((hU p).mdifferentiableAt (by simp)) v w
  change inducedForm (F+U) p v w = inducedForm F p v w +
    linearMetricForm F U p v w + inducedForm U p v w
  linarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearMetricChartReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed metric is reconstructed from the genuine chart readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance linearReadFiberNormed_r7ff60a_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance linearReadFiberSpace_r7ff60a_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance linearReadDualAdd_r7ff60a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance linearReadDualSmul_r7ff60a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearReadSectionNormed
local instance linearReadSectionSpace_r7ff60a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma vectorPlaneRead_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F+G) = A.vectorPlaneRead i F + A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_add]

theorem linearMetric_from_chart_reads {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G) :
    A.tensorPlaneRestore (fun i y => (A.planeWeight i y)^2 •
      RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (spaceCoordinates ∘ A.vectorPlaneRead i G) y) = linearMetricTensor F G := by
  have he := A.metric_from_chart_reads (hF.add hG)
  rw [inducedTensor_add hF hG] at he
  have hlocal : (fun i y => (A.planeWeight i y)^2 •
      RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i (F+G)) y) =
      (fun i y => (A.planeWeight i y)^2 •
        RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y) +
      (fun i y => (A.planeWeight i y)^2 •
        RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (spaceCoordinates ∘ A.vectorPlaneRead i G) y) +
      (fun i y => (A.planeWeight i y)^2 •
        RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) y) := by
    funext i y
    rw [A.vectorPlaneRead_add]
    have hc : spaceCoordinates ∘ (A.vectorPlaneRead i F + A.vectorPlaneRead i G) =
        fun x => (spaceCoordinates ∘ A.vectorPlaneRead i F) x +
          (spaceCoordinates ∘ A.vectorPlaneRead i G) x := by
      funext x
      exact map_add spaceCoordinates _ _
    rw [hc,RealModes.realMetricTensor_add
      ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) y)
      ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) y)]
    simp only [smul_add,Pi.add_apply]
  rw [hlocal,A.tensorPlaneRestore_add,A.tensorPlaneRestore_add,
    A.metric_from_chart_reads hF,A.metric_from_chart_reads hG] at he
  exact add_left_cancel (add_right_cancel he)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and elementary norm operations for actual global metric tensors. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualSmul
variable (A : SmoothingAtlas M)
include A

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberSpace
local instance metricBoundSectionNormed_r7ff60a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_r7ff60a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma linearMetricTensor_smooth {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (linearMetricTensor F G p)) := by
  rw [← A.linearMetric_from_chart_reads hF hG]
  apply A.tensorPlaneRestore_smooth
  intro i
  apply ((A.planeWeight_smooth i).pow 2).smul
  exact contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).contDiffOn
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)).contDiffOn)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasQuadraticResidual
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero-phase residual of the actual charted free family. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasSectionNormed
local instance quadraticAtlasSectionSpace_r7ff60a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_const_smul
    {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ}
    (hb : A.TensorWeightedBound s m C u) (a : ℝ) :
    A.TensorWeightedBound s m (|a| * C) (a • u) := by
  intro i
  have hb' := (hb i).const_smul uniqueDiffOn_univ
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu).contDiffOn a
  change _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (|a| * C) (A.bundleLocalize A.tensorTriv i (a • u))
  rw [A.bundleLocalize_smul]
  exact hb'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalMetricStep
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalized-defect identity for the unsmoothed global map update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
local instance metricStepFiberNormed_r7ff60a_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricStepFiberSpace_r7ff60a_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricStepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

local instance metricStepDualSmul_r7ff60a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricStepSectionNormed
local instance metricStepSectionSpace_r7ff60a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma linearMetricTensor_sub_left {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G)
    (U : M → Space) : linearMetricTensor (F-G) U = linearMetricTensor F U - linearMetricTensor G U := by
  funext p
  ext v w
  change linearMetricForm (F-G) U p v w = linearMetricForm F U p v w - linearMetricForm G U p v w
  have hd : surfaceDifferential (F-G) p = surfaceDifferential F p - surfaceDifferential G p :=
    mfderiv_sub ((hF p).mdifferentiableAt (by simp)) ((hG p).mdifferentiableAt (by simp))
  simp only [linearMetricForm,hd,sub_apply,inner_sub_left,inner_sub_right]
  ring

lemma metric_increment_difference {F G U : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G)
    (hU : ContMDiff planeModel spaceModel ∞ U) :
    (inducedTensor (F+U)-inducedTensor F) - (inducedTensor (G+U)-inducedTensor G) =
      linearMetricTensor (F-G) U := by
  rw [inducedTensor_add hF hU,inducedTensor_add hG hU,linearMetricTensor_sub_left hF hG]
  abel

lemma square_smul_normalizedTensorDefect (target : ∀ p : M, CovariantTwoTensor p)
    {δ : ℝ} (hδ : δ ≠ 0) (F : M → Space) :
    δ^2 • normalizedTensorDefect target δ F = target - inducedTensor F := by
  rw [normalizedTensorDefect,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 hδ),one_smul]

/-- The smoothing tail enters only through the mixed term with the increment. -/
theorem global_normalized_defect_identity
    (target Hs : ∀ p : M, CovariantTwoTensor p) {δ δ' : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    {F G U : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U) :
    δ'^2 • (normalizedTensorDefect target δ' (F+U)-target) =
      δ^2 • (normalizedTensorDefect target δ F-Hs) - realizedTensorError target Hs δ δ' G U -
        linearMetricTensor (F-G) U := by
  rw [smul_sub,smul_sub,square_smul_normalizedTensorDefect target hδ',
    square_smul_normalizedTensorDefect target hδ]
  rw [← metric_increment_difference hF hG hU]
  unfold realizedTensorError
  abel

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalMetricStepBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global weighted estimate for the concrete unsmoothed normalized-defect update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundSectionNormed
local instance stepBoundSectionSpace_r7ff60a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_sub {T S : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hS : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (S p)))
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbT : A.TensorWeightedBound s m C T) (hbS : A.TensorWeightedBound s m D S) :
    A.TensorWeightedBound s m (C+D) (T-S) := by
  intro i
  have he : A.bundleLocalize A.tensorTriv i (T-S) =
      A.bundleLocalize A.tensorTriv i T - A.bundleLocalize A.tensorTriv i S := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).target <;>
      simp [bundleLocalize,localize,bundleComponent,hx,smul_sub]
  change WeightedEstimates.WeightedBound univ s m (C+D) (A.bundleLocalize A.tensorTriv i (T-S))
  rw [he]
  exact (hbT i).sub uniqueDiffOn_univ hs
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT).contDiffOn
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hS).contDiffOn (hbS i)

include A in
lemma realizedTensorError_smooth {target Hs : ∀ p : M, CovariantTwoTensor p}
    (ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    (hs : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (Hs p)))
    (δ δ' : ℝ) {G U : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (realizedTensorError target Hs δ δ' G U p)) :=
  ((A.inducedTensor_smooth (hG.add hU)).sub_section (A.inducedTensor_smooth hG)).sub_section
    (hs.const_smul_section.sub_section ht.const_smul_section)

theorem global_normalized_metric_step_bound_oai {target Hs : ∀ p : M, CovariantTwoTensor p}
    (ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    (hs : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (Hs p)))
    {δ δ' τ BH BE BC : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0) (hτ : 0 ≤ τ) (m : ℕ)
    {F G U : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U)
    (hbH : A.TensorWeightedBound τ m BH (normalizedTensorDefect target δ F-Hs))
    (hbE : A.TensorWeightedBound τ m BE (realizedTensorError target Hs δ δ' G U))
    (hbC : A.TensorWeightedBound τ m BC (linearMetricTensor (F-G) U)) :
    A.TensorWeightedBound τ m ((δ'^2)⁻¹*(δ^2*BH+BE+BC))
      (normalizedTensorDefect target δ' (F+U)-target) := by
  have hHs := (A.normalizedTensorDefect_smooth ht δ hF).sub_section hs
  have hEs := A.realizedTensorError_smooth ht hs δ δ' hG hU
  have hCs := A.linearMetricTensor_smooth (hF.sub hG) hU
  have h₁ := A.tensorWeightedBound_const_smul hHs hbH (δ^2)
  rw [abs_of_nonneg (sq_nonneg δ)] at h₁
  have h₂ := A.tensorWeightedBound_sub hHs.const_smul_section hEs hτ h₁ hbE
  have h₃ := A.tensorWeightedBound_sub (hHs.const_smul_section.sub_section hEs) hCs hτ h₂ hbC
  have h₄ := A.tensorWeightedBound_const_smul
    ((hHs.const_smul_section.sub_section hEs).sub_section hCs) h₃ ((δ'^2)⁻¹)
  rw [abs_inv,abs_of_nonneg (sq_nonneg δ')] at h₄
  have heq : normalizedTensorDefect target δ' (F+U)-target = (δ'^2)⁻¹ •
      (δ^2 • (normalizedTensorDefect target δ F-Hs) - realizedTensorError target Hs δ δ' G U -
        linearMetricTensor (F-G) U) := by
    rw [← global_normalized_defect_identity target Hs hδ hδ' hF hG hU,
      smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 hδ'),one_smul]
  rw [heq]
  exact h₄

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound_oai.{u_1}
