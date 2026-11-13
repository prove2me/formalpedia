-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorFrameRead_C1_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:21.709174+00:00
-- url     : https://prove2.me/submissions/1774e124-1bfe-41dd-a0ed-5b4507779ce0

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
import Definitions.Def_OAIQ249SI012

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
local instance coordinateFiberSpace_rf83561_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberToThree_apply (B : TensorFiber) (k : Fin 3) :
    fiberToThree B k = B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k)) := rfl

lemma plane_basis_expansion (v : Plane) :
    v = (planeCoordinates v).1 • planeCoordinates.symm SmallModes.dx +
      (planeCoordinates v).2 • planeCoordinates.symm SmallModes.dy := by
  apply planeCoordinates.injective
  simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  exact RealModes.base_decomposition (planeCoordinates v)

lemma fiberFromThree_toThree (B : TensorFiber) (hB : ∀ v w, B v w = B w v) :
    fiberFromThree (fiberToThree B) = B := by
  ext v w
  rw [fiberFromThree_apply]
  have hcross := hB (planeCoordinates.symm SmallModes.dy) (planeCoordinates.symm SmallModes.dx)
  conv_rhs => rw [plane_basis_expansion v, plane_basis_expansion w]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  simp only [evaluate, fiberToThree_apply]
  simp only [firstDirection, secondDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]
  dsimp
  rw [hcross]
  ring

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
local instance chartReadSectionNormed_rf83561_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_rf83561_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceMetricStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual remainder metric inherits the fixed positive inverse margins
from C1 approximation of the reference immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricFiberSpace
local instance refMetricDualSmul_rf83561_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricSectionNormed
local instance refMetricSectionSpace_rf83561_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensor_frame_read (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ∀ p v w, u p v w = u p w v) {p : M} (hp : p ∈ tsupport (B.weight i)) :
    (B.tensorTriv i).continuousLinearMapAt ℝ p (u p) =
      fiberFromThree (B.tensorChartRead i u (chart (i : M) p)) := by
  rw [B.tensorChartRead_on_weight i u hp]
  apply (fiberFromThree_toThree _ ?_).symm
  intro v w
  change B.bundleComponent B.tensorTriv i u p v w = B.bundleComponent B.tensorTriv i u p w v
  rw [B.tensorComponent_apply i u (B.weight_support i hp),
    B.tensorComponent_apply i u (B.weight_support i hp)]
  exact hu p _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorFrameReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary first-jet bounds for symmetric tensor components on the fixed
primitive chart supports, including their boundaries. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorReadBoundsDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorReadBoundsDualSmul
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorReadBoundsFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorReadBoundsFiberSpace
local instance tensorReadBoundsSectionNormed_rf83561_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorReadBoundsSectionSpace_rf83561_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorFrameRead_smoothOn (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiffOn ℝ ∞ (B.tensorFrameRead i u) (chart (i : M)).target := by
  have h := (B.bundleComponent_smooth_on B.tensorTriv B.tensorTriv_domain i hu).comp
    (chart_symm_smooth (i : M)) (fun _ hx => (chart (i : M)).map_target hx)
  exact h.contDiffOn

lemma tensorFrameRead_jets (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hsym : ∀ p v w, u p v w = u p w v) (m : ℕ)
    {y : JetPolynomial.Base} (hy : y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base)) :
    iteratedFDeriv ℝ m (fiberFromThree ∘ B.tensorChartRead i u) y =
      iteratedFDeriv ℝ m (B.tensorFrameRead i u) y := by
  have hK : tsupport (B.chartWeight i) ⊆ (chart (i : M)).target := by
    rw [B.chartWeight_tsupport]
    rintro _ ⟨p,hp,rfl⟩
    exact (chart (i : M)).map_source (B.weight_support i hp)
  apply iteratedFDeriv_eq_on_tsupport (B.chartWeight_smooth i).continuous
    (chart (i : M)).open_target hK
    (fiberFromThree.contDiff.comp (B.tensorChartRead_smooth i hu)).contDiffOn
    (B.tensorFrameRead_smoothOn i u hu) ?_ m
  · rwa [B.chartWeight_tsupport]
  · intro y hy
    rw [B.chartWeight_tsupport] at hy
    obtain ⟨p,hp,rfl⟩ := hy
    change fiberFromThree (B.tensorChartRead i u (chart (i : M) p)) =
      (B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm (chart (i : M) p))
        (u ((chart (i : M)).symm (chart (i : M) p)))
    rw [(chart (i : M)).left_inv (B.weight_support i hp)]
    exact (B.tensor_frame_read i u hsym hp).symm

theorem tensorFrameRead_C1_bound_oai {D : ℝ} (hD : 0 ≤ D) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ u : ∀ p : M, CovariantTwoTensor p,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      (∀ p v w, u p v w = u p w v) → B.TensorWeightedBound 1 1 D u →
      ∀ i p, p ∈ tsupport (B.weight i) →
        ‖B.tensorFrameRead i u (chart (i : M) p)‖ ≤ E ∧
        ‖fderiv ℝ (B.tensorFrameRead i u) (chart (i : M) p)‖ ≤ E := by
  classical
  choose R hR hread using fun i : B.centers => B.tensorChartRead_bound i 1
  let E := 1+‖fiberFromThree‖*(∑ i, R i)*D
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hR i)
  have hE : 1 ≤ E := by
    dsimp only [E]
    linarith [mul_nonneg (mul_nonneg (norm_nonneg fiberFromThree) hsum) hD]
  refine ⟨E,hE,?_⟩
  intro u hu hsym hb i p hp
  have h := hread i u 1 D zero_lt_one le_rfl hD hu hb
  have hh := h.linear uniqueDiffOn_univ (by norm_num : (0 : ℝ) ≤ 1)
    (B.tensorChartRead_smooth i hu).contDiffOn fiberFromThree
  have hi : ‖fiberFromThree‖*(R i*D) ≤ E := by
    have hx := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hR j) (Finset.mem_univ i)) hD) (norm_nonneg fiberFromThree)
    dsimp only [E]
    nlinarith
  have hj := congrArg norm (B.tensorFrameRead_jets i u hu hsym 0 ⟨p,hp,rfl⟩)
  simp only [norm_iteratedFDeriv_zero] at hj
  have hv := (hh.norm_le (mem_univ (chart (i : M) p))).trans hi
  refine ⟨hj ▸ hv,?_⟩
  have hd := hh.deriv_le zero_lt_one le_rfl (mem_univ (chart (i : M) p))
  simp only [iteratedFDerivWithin_univ,one_pow,div_one] at hd
  rw [B.tensorFrameRead_jets i u hu hsym 1 ⟨p,hp,rfl⟩,
    norm_iteratedFDeriv_one] at hd
  exact hd.trans hi

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorFrameRead_C1_bound_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorFrameRead_C1_bound_oai.{u_1}
