-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.actual_amplitude_parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:39:02.397406+00:00
-- url     : https://prove2.me/submissions/41090bc7-72b9-4c6f-b936-a766225dd190

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_amplitude_parameter_margin
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_metric_frame_tolerance

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
local instance coordinateFiberSpace_r96404c_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance chartReadSectionNormed_r96404c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r96404c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCoordinateCovector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorFrameAlgebra
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate conjugation of the actual primitive operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraDualSmul
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraSectionNormed
local instance frameAlgebraSectionSpace_r96404c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraSectionGroup
lemma tensor_frame_square (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (v : Plane →L[ℝ] ℝ) :
    (B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v) =
      (B.covectorFrame i p v).smulRight (B.covectorFrame i p v) := by
  ext x y
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,chart_source] using hp
  have h := B.tensorComponent_apply i (fun _ => v.smulRight v) hp x y
  change (B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v) x y = _ at h
  change (B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v) x y =
    v ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p x) *
      v ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p y)
  erw [(trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL_apply (R := ℝ) ht,
    (trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL_apply (R := ℝ) ht]
  exact h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveFrameBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact bounds for actual coefficient and differential fields in the
fixed tensor frames, including overlapping phase charts. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameBoundDualSmul
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameBoundFiberSpace
local instance frameBoundSectionNormed_r96404c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameBoundSectionSpace_r96404c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] [T2Space M] in
lemma covectorFrame_norm_sq (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (v : Plane →L[ℝ] ℝ) :
    ‖B.covectorFrame i p v‖^2 = ‖(B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v)‖ := by
  rw [B.tensor_frame_square i hp,ContinuousLinearMap.norm_smulRight_apply,pow_two]

omit [T2Space M] in
 theorem covectorFrame_bound_at (phi : M → ℝ) (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi)
    (i : B.centers) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ tsupport (B.weight i),
      ‖B.covectorFrame i p (mfderiv planeModel 𝓘(ℝ) phi p)‖ ≤ D := by
  have hsec := B.phaseDifferentialSquare_smooth phi hphi
  have hc := (B.bundleComponent_smooth_on B.tensorTriv B.tensorTriv_domain i hsec).continuousOn.mono
    (B.weight_support i)
  obtain ⟨C,hC⟩ := (isClosed_tsupport (B.weight i)).isCompact.exists_bound_of_continuousOn hc
  refine ⟨|C|+1,by linarith [abs_nonneg C],?_⟩
  intro p hp
  have hh := hC p hp
  let v : Plane →L[ℝ] ℝ := mfderiv planeModel 𝓘(ℝ) phi p
  have he := B.covectorFrame_norm_sq i (B.weight_support i hp) v
  change ‖(B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v)‖ ≤ C at hh
  rw [← he] at hh
  change ‖B.covectorFrame i p v‖ ≤ |C|+1
  nlinarith [norm_nonneg (B.covectorFrame i p v),le_abs_self C,abs_nonneg C]

omit [T2Space M] in
 theorem covectorFrame_bound (phi : M → ℝ) (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i p, p ∈ tsupport (B.weight i) →
      ‖B.covectorFrame i p (mfderiv planeModel 𝓘(ℝ) phi p)‖ ≤ D := by
  choose D hD hb using B.covectorFrame_bound_at phi hphi
  refine ⟨1+∑ i, D i,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.univ) (fun i _ => zero_le_one.trans (hD i)); linarith
  · intro i p hp
    exact (hb i p hp).trans (by
      have := Finset.single_le_sum (fun i _ => zero_le_one.trans (hD i)) (Finset.mem_univ i)
      linarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCovectorRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual covector in a tangent frame is the derivative of the
scalar phase in that chart. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

lemma covectorFrame_mfderiv (phi : M → ℝ) (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi)
    (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source) :
    B.covectorFrame i p (mfderiv planeModel 𝓘(ℝ) phi p) =
      (fderiv ℝ (phi ∘ (chart (i : M)).symm) (chart (i : M) p)).comp
        (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap := by
  let f := phi ∘ (chart (i : M)).symm
  have hf : ContDiffOn ℝ ∞ f (chart (i : M)).target :=
    (hphi.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  have hx := (chart (i : M)).map_source hp
  have hfa := hf.contDiffAt ((chart (i : M)).open_target.mem_nhds hx)
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have he : phi =ᶠ[𝓝 p] (f ∘ chart (i : M)) := by
    filter_upwards [(chart (i : M)).open_source.mem_nhds hp] with q hq
    exact congrArg phi ((chart (i : M)).left_inv hq).symm
  have hd := he.mfderiv_eq (I := planeModel) (I' := 𝓘(ℝ))
  erw [mfderiv_comp p (hfa.contMDiffAt.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv,B.jetChart_tangentCoordinates i hp] at hd
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,chart_source] using hp
  apply ContinuousLinearMap.ext
  intro v
  change (mfderiv planeModel 𝓘(ℝ) phi p)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v) = _
  rw [hd]
  change fderiv ℝ f (chart (i : M) p)
      ((EuclideanSpace.equiv (Fin 2) ℝ)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v))) = _
  rw [(trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt_symmL ht]
  rfl

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
local instance refMetricDualSmul_r96404c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricSectionNormed
local instance refMetricSectionSpace_r96404c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPhaseDependence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact affine dependence of supported circular phases on their linear
parameters. The curvature parameter stays fixed. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_smooth (i : B.centers) (ell : Base) (L : ℝ) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (B.circularPhase i ell L) :=
  restore_smooth (i : M) (B.outer_smooth i) (B.outer_support i)
    ((centeredConvexPhase_smooth _ _ _).comp JetPolynomial.planeCoordinateIsometry.contDiff)

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_sub (i : B.centers) (ell ell₀ : Base) (L : ℝ) :
    B.circularPhase i ell L-B.circularPhase i ell₀ L =
      (ell.1-ell₀.1) • B.circularPhase i (1,0) 0+
        (ell.2-ell₀.2) • B.circularPhase i (0,1) 0 := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [circularPhase,restore,hp,indicator_of_mem,Function.comp_apply,
      Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,centeredConvexPhase,
      convexQuadraticPhase,phaseLinear,Prod.fst_sub,Prod.snd_sub,
      add_apply,smul_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  · simp only [circularPhase,restore,indicator_of_notMem hp,Pi.sub_apply,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,sub_self,mul_zero,add_zero]

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_mfderiv_sub (i : B.centers) (ell ell₀ : Base) (L : ℝ) (p : M) :
    (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
      (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell₀ L) p) =
      (ell.1-ell₀.1) • (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)+
        (ell.2-ell₀.2) • (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p) := by
  have h1 := ((B.circularPhase_smooth i ell L) p).mdifferentiableAt (by simp)
  have h0 := ((B.circularPhase_smooth i ell₀ L) p).mdifferentiableAt (by simp)
  have hx := ((B.circularPhase_smooth i (1,0) 0) p).mdifferentiableAt (by simp)
  have hy := ((B.circularPhase_smooth i (0,1) 0) p).mdifferentiableAt (by simp)
  erw [← mfderiv_sub h1 h0,B.circularPhase_sub]
  erw [mfderiv_add (hx.const_smul _) (hy.const_smul _),
    const_smul_mfderiv hx,const_smul_mfderiv hy]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPhaseTolerance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact-frame constant controls the phase perturbation before
any independent choices or cycle count. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem circularPhase_frame_bound : ∃ D : ℝ, 1 ≤ D ∧
    ∀ i j p, p ∈ tsupport (B.weight j) → ∀ (ell ell₀ : Base) (L : ℝ),
      ‖B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
        B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell₀ L) p)‖ ≤
        D*‖ell-ell₀‖ := by
  choose Dx hDx hx using fun i => B.covectorFrame_bound (B.circularPhase i (1,0) 0)
    (B.circularPhase_smooth i (1,0) 0)
  choose Dy hDy hy using fun i => B.covectorFrame_bound (B.circularPhase i (0,1) 0)
    (B.circularPhase_smooth i (0,1) 0)
  let D := 1+∑ i, (Dx i+Dy i)
  have hD : 1 ≤ D := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun i _ => add_nonneg (zero_le_one.trans (hDx i))
      (zero_le_one.trans (hDy i)))
    dsimp only [D] <;> linarith
  refine ⟨D,hD,?_⟩
  intro i j p hp ell ell₀ L
  have he : B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
      B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell₀ L) p) =
      (ell.1-ell₀.1) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)+
      (ell.2-ell₀.2) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p) := by
    unfold covectorFrame
    erw [← ContinuousLinearMap.sub_comp,B.circularPhase_mfderiv_sub]
    erw [ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp,ContinuousLinearMap.smul_comp]
  rw [he]
  have h1 : |ell.1-ell₀.1| ≤ ‖ell-ell₀‖ := by simpa only [Prod.fst_sub,Real.norm_eq_abs] using norm_fst_le (ell-ell₀)
  have h2 : |ell.2-ell₀.2| ≤ ‖ell-ell₀‖ := by simpa only [Prod.snd_sub,Real.norm_eq_abs] using norm_snd_le (ell-ell₀)
  have hxy : Dx i+Dy i ≤ D := by
    have := Finset.single_le_sum (fun i _ => add_nonneg (zero_le_one.trans (hDx i))
      (zero_le_one.trans (hDy i))) (Finset.mem_univ i)
    dsimp only [D] <;> linarith
  calc
    _ ≤ ‖(ell.1-ell₀.1) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)‖+
        ‖(ell.2-ell₀.2) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p)‖ := norm_add_le _ _
    _ ≤ ‖ell-ell₀‖*Dx i+‖ell-ell₀‖*Dy i := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul h1 (hx i j p hp) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul h2 (hy i j p hp) (norm_nonneg _) (norm_nonneg _))
    _ = (Dx i+Dy i)*‖ell-ell₀‖ := by ring
    _ ≤ D*‖ell-ell₀‖ := mul_le_mul_of_nonneg_right hxy (norm_nonneg _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateTolerance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise perturbations bound the actual finite coordinate data. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordToleranceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordToleranceFiberSpace
local instance coordToleranceDualSmul_r96404c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordToleranceFiberNormed
local instance coordToleranceSectionNormed_r96404c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordToleranceSectionSpace_r96404c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma primitiveCoordinateData_sub_lt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi psi0 phi phi0 : (B.centers × Fin 3) → M → ℝ)
    (u u0 : ∀ p : M, CovariantTwoTensor p) (i : B.centers)
    (S : Set (B.centers × Fin 3)) {p : M} (hp : p ∈ (chart (i : M)).source)
    {eps : ℝ} (heps : 0 < eps)
    (hw : ∀ a, |psi a p-psi0 a p| < eps)
    (hv : ∀ a ∈ S, ‖B.phaseCovectorRead i (phi a) (chart (i : M) p)-
      B.phaseCovectorRead i (phi0 a) (chart (i : M) p)‖ < eps)
    (hH : ‖(B.tensorTriv i).continuousLinearMapAt ℝ p (u p)-
      (B.tensorTriv i).continuousLinearMapAt ℝ p (u0 p)‖ < eps) :
    ‖B.primitiveCoordinateData P psi phi u i S (chart (i : M) p)-
      B.primitiveCoordinateData P psi0 phi0 u0 i S (chart (i : M) p)‖ < eps := by
  classical
  let q := fun a => if a ∈ S then B.coefficientFrameRead P i a (chart (i : M) p) else 0
  let v := fun a => if a ∈ S then B.phaseCovectorRead i (phi a) (chart (i : M) p) else 0
  let v0 := fun a => if a ∈ S then B.phaseCovectorRead i (phi0 a) (chart (i : M) p) else 0
  unfold primitiveCoordinateData
  rw [(chart (i : M)).left_inv hp]
  change max (max (max ‖q-q‖ ‖(fun a => psi a p)-(fun a => psi0 a p)‖) ‖v-v0‖)
    ‖(B.tensorTriv i).continuousLinearMapAt ℝ p (u p)-
      (B.tensorTriv i).continuousLinearMapAt ℝ p (u0 p)‖ < eps
  rw [sub_self,norm_zero]
  refine max_lt (max_lt (max_lt heps ?_) ?_) hH
  · apply (pi_norm_lt_iff heps).mpr
    intro a
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using hw a
  · apply (pi_norm_lt_iff heps).mpr
    intro a
    dsimp only [v,v0,Pi.sub_apply]
    split_ifs with ha
    · exact hv a ha
    · simpa only [sub_self,norm_zero] using heps

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceAmplitudeParameterBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual independent circular data remain inside the fixed positive
amplitude neighborhood for every sufficiently close starting map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualParamFiberSpace
local instance actualParamDualAdd_r96404c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualParamDualSmul_r96404c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualParamFiberNormed
local instance actualParamSectionNormed_r96404c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualParamSectionSpace_r96404c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem actual_amplitude_parameter_bound_oai {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ pt wt mt R : ℝ, 0 < pt ∧ 0 < wt ∧ 0 < mt ∧ 1 ≤ R ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < pt) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < wt) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mt (G-F) →
      ∀ i p, p ∈ tsupport (d.B.weight i) → ∀ a : d.B.centers × Fin 3,
      p ∈ tsupport (d.B.weight a.1) →
      let z := d.B.primitiveCoordinateData d.basis psi (d.perturbedPhases ell)
        (g.inner-inducedTensor (r • G)) i {b | p ∈ tsupport (d.B.weight b.1)} (chart (i : M) p)
      (primitiveDataOperator z.1).IsInvertible ∧ 0 < primitiveParameterCoefficient a z ∧
        |primitiveParameterAmplitude a z| ≤ R ∧
        ‖fderiv ℝ (primitiveParameterAmplitude a) z‖ ≤ R := by
  obtain ⟨eps,R,heps,hR,hmargin⟩ := d.amplitude_parameter_margin
  obtain ⟨D,hD,hphase⟩ := d.B.circularPhase_frame_bound
  obtain ⟨mt,hmt,hmetric⟩ := d.metric_frame_tolerance hF r href heps
  have hDp : 0 < D+1 := by linarith
  refine ⟨eps/(D+1),eps,mt,R,div_pos heps hDp,heps,hmt,hR,?_⟩
  intro ell psi hell hw G hG hnear i p hp a ha
  apply hmargin i p hp a ha
  apply d.B.primitiveCoordinateData_sub_lt d.basis psi (fun b => d.B.weight b.1)
    (d.perturbedPhases ell) d.globalPhases (g.inner-inducedTensor (r • G)) gref.inner i
    {b | p ∈ tsupport (d.B.weight b.1)} (d.B.weight_support i hp) heps (fun b => hw b p)
  · intro b _hb
    have hs := d.B.weight_support i hp
    have he := (d.B.covectorFrame_mfderiv (d.B.circularPhase b.1 (ell b.1 b.2) (d.L b.1))
      (d.B.circularPhase_smooth _ _ _) i hs)
    have he0 := (d.B.covectorFrame_mfderiv (d.B.circularPhase b.1 ((d.P b.1).ξ b.2) (d.L b.1))
      (d.B.circularPhase_smooth _ _ _) i hs)
    change ‖d.B.phaseCovectorRead i (d.B.circularPhase b.1 (ell b.1 b.2) (d.L b.1)) (chart (i : M) p)-
      d.B.phaseCovectorRead i (d.B.circularPhase b.1 ((d.P b.1).ξ b.2) (d.L b.1)) (chart (i : M) p)‖ < eps
    simp only [SmoothingAtlas.phaseCovectorRead]
    rw [← he,← he0]
    have hb := hphase b.1 i p hp (ell b.1 b.2) ((d.P b.1).ξ b.2) (d.L b.1)
    have ht := (lt_div_iff₀ hDp).mp (hell b.1 b.2)
    have hn := norm_nonneg (ell b.1 b.2-(d.P b.1).ξ b.2)
    exact hb.trans_lt (by nlinarith)
  · have h := hmetric G hG hnear i p hp
    rw [d.B.tensor_frame_read i gref.inner gref.symm hp]
    exact h

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.actual_amplitude_parameter_bound_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.actual_amplitude_parameter_bound_oai.{u_1}
