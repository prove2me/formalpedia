-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_direction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:37:37.762429+00:00
-- url     : https://prove2.me/submissions/f7925968-e38b-49cf-a4d0-395ef45a6ecd

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010

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
local instance coordinateFiberSpace_r4f5d51_1 : NormedSpace ℝ TensorFiber := inferInstance
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

lemma fiberFromThree_symmetric (H : Tensor) (v w : Plane) :
    fiberFromThree H v w = fiberFromThree H w v := by
  rw [fiberFromThree_apply, fiberFromThree_apply]
  simp only [evaluate]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothingSymmetry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor coordinate maps commute with transposition. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r4f5d51_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r4f5d51_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualSmul
variable (A : SmoothingAtlas M)

lemma tensorComponent_flip (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    A.bundleComponent A.tensorTriv i (fun p => tensorTranspose (u p)) p =
      (A.bundleComponent A.tensorTriv i u p).flip := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  have hs : p ∈ (trivializationAt ℝ (fun _ : M => ℝ) (i : M)).baseSet := mem_univ p
  unfold bundleComponent
  rw [(A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp),
    (A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp)]
  unfold tensorTriv
  simp only [hom_trivializationAt_apply]
  ext v w
  simp only [ContinuousLinearMap.flip_apply]
  rw [inCoordinates_apply_eq₂ ht ht hs, inCoordinates_apply_eq₂ ht ht hs]
  rfl

lemma tensorRestore_flip (i : A.centers) (h : Base → TensorFiber) :
    A.bundleRestore A.tensorTriv i (fun x => (h x).flip) =
      fun p => tensorTranspose (A.bundleRestore A.tensorTriv i h p) := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · have hd := A.tensorTriv_domain i hp
    have hinj : Function.Injective ((A.tensorTriv i).continuousLinearMapAt ℝ p) := by
      intro v w heq
      have heq' := congrArg ((A.tensorTriv i).symmL ℝ p) heq
      simpa only [(A.tensorTriv i).symmL_continuousLinearMapAt hd] using heq'
    apply hinj
    have hflip := A.tensorComponent_flip i (A.bundleRestore A.tensorTriv i h) hp
    change (A.tensorTriv i).continuousLinearMapAt ℝ p
        (tensorTranspose (A.bundleRestore A.tensorTriv i h p)) =
      ((A.tensorTriv i).continuousLinearMapAt ℝ p (A.bundleRestore A.tensorTriv i h p)).flip at hflip
    have hcoord (f : Base → TensorFiber) :
        (A.tensorTriv i).continuousLinearMapAt ℝ p (A.bundleRestore A.tensorTriv i f p) =
          A.outer i p • f (chart (i : M) p) := by
      change (A.tensorTriv i).continuousLinearMapAt ℝ p
        (A.outer i p • (A.tensorTriv i).symmL ℝ p (f (chart (i : M) p))) = _
      rw [(A.tensorTriv i).continuousLinearMapAt ℝ p |>.map_smul]
      rw [(A.tensorTriv i).continuousLinearMapAt_symmL hd]
    rw [hflip, hcoord, hcoord]
    ext v w
    rfl
  · have ho : A.outer i p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hp (A.outer_support i hh))
    simp only [bundleRestore, ho, zero_smul]
    rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPhaseDecomposition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite phase-basis decomposition on global symmetric tensor sections.
The atlas partition restores the tensor exactly, including chart overlaps. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance phaseFiberNormed_r4f5d51_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_r4f5d51_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_r4f5d51_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_r4f5d51_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_r4f5d51_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_r4f5d51_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorDecode_symmetric {f : Base → A.centers → TensorFiber}
    (hf : ∀ x i v w, f x i v w = f x i w v) :
    ∀ p v w, A.tensorDecode f p v w = A.tensorDecode f p w v := by
  have ht (i : A.centers) : (fun x => (f x i).flip) = (fun x => f x i) := by
    funext x
    ext v w
    exact hf x i w v
  intro p v w
  simp only [tensorDecode, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hh := A.tensorRestore_flip i (fun x => f x i)
  rw [ht] at hh
  exact congrArg (fun b : CovariantTwoTensor p => b v w) (congrFun hh p)

end SmoothingAtlas
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
local instance chartReadSectionNormed_r4f5d51_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r4f5d51_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r4f5d51_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_symmetric (f : A.centers → SmallModes.Base → Tensor) :
    ∀ p v w, A.tensorPlaneRestore f p v w = A.tensorPlaneRestore f p w v := by
  apply A.tensorDecode_symmetric
  intro x i v w
  exact fiberFromThree_symmetric _ _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasRestore
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A displacement supported on an atlas weight's compact support is
restored exactly in that chart; the outer cutoff introduces no jet error. -/
noncomputable section
open Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma mem_weight_support_of_plane (i : A.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (h : planeCoordinateIsometry (chart (i : M) p) ∈
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) : p ∈ tsupport (A.weight i) := by
  obtain ⟨y,hy,he⟩ := h
  have hyEq : y = chart (i : M) p := planeCoordinateIsometry.injective he
  subst y
  obtain ⟨q,hq,hqp⟩ := hy
  have hqEq : q = p := (chart (i : M)).injOn (A.weight_support i hq) hp hqp
  rwa [hqEq] at hq

lemma restore_plane_on_source (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) p =
      f (planeCoordinateIsometry (chart (i : M) p)) := by
  rw [restore,indicator_of_mem hp]
  change A.outer i p • f (planeCoordinateIsometry (chart (i : M) p)) = _
  by_cases hz : f (planeCoordinateIsometry (chart (i : M) p)) = 0
  · rw [hz,smul_zero]
  · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hf (subset_tsupport f hz))),one_smul]

lemma restore_plane_in_coordinates (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {x : JetPolynomial.Base} (hx : x ∈ (chart (i : M)).target) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) ((chart (i : M)).symm x) =
      f (planeCoordinateIsometry x) := by
  rw [A.restore_plane_on_source i f hf ((chart (i : M)).map_target hx),(chart (i : M)).right_inv hx]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported restoration commutes with all local derivatives, including
its actual manifold differential, and preserves the original atlas support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restore_plane_tsupport (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    tsupport (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) ⊆
      tsupport (A.weight i) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_cases hs : p ∈ (chart (i : M)).source
  · apply A.mem_weight_support_of_plane i hs
    apply hf
    apply subset_tsupport f
    intro hz
    apply hp
    rw [A.restore_plane_on_source i f hf hs,hz]
  · exfalso
    apply hp
    simp only [restore,indicator_of_notMem hs]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global polynomial variation is local in its varying field.
In particular, restoring the polynomial does not enlarge that support. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance polynomialSupportFiberNormed_r4f5d51_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSupportFiberSpace_r4f5d51_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialSupportDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
local instance polynomialSupportFiberNormed_r4f5d51_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSupportFiberSpace_r4f5d51_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialSupportDualSmul_r4f5d51_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance polynomialSupportSectionNormed_r4f5d51_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSupportSectionSpace_r4f5d51_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma jetChartMap_eventually_zero (i : A.centers) {X : M → Space} {p : M}
    (hp : p ∈ (chart (i : M)).source) (hX : X =ᶠ[𝓝 p] 0) :
    A.jetChartMap i X =ᶠ[𝓝 (chart (i : M) p)] 0 := by
  have ht := (chart (i : M)).map_source hp
  have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    simpa only [(chart (i : M)).left_inv hp] using
      ((chart (i : M)).continuousAt_symm ht).tendsto
  have he := hX.comp_tendsto hc
  filter_upwards [he,(chart (i : M)).open_target.mem_nhds ht] with y hy hyt
  change X ((chart (i : M)).symm y) = 0 at hy
  change spaceCoordinates (localize (i : M) (A.outer i) X y) = 0
  simp only [localize,indicator_of_mem hyt,hy,smul_zero,map_zero]

lemma atlasPolynomialVariation_zero_of_notMem {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    (F X : M → Space) {p : M} (hp : p ∉ tsupport X) :
    A.atlasPolynomialVariation P ε F X p = 0 := by
  classical
  unfold atlasPolynomialVariation tensorPlaneRestore
  apply Finset.sum_eq_zero
  intro i _
  by_cases ho : A.outer i p = 0
  · simp only [bundleRestore,ho,zero_smul]
  · have hps := A.outer_support i (subset_tsupport (A.outer i) ho)
    have hz := A.jetChartMap_eventually_zero i hps (notMem_tsupport_iff_eventuallyEq.mp hp)
    have hn : chart (i : M) p ∉ tsupport (A.jetChartMap i X) :=
      notMem_tsupport_iff_eventuallyEq.mpr hz
    have hcomp : (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘
        planeCoordinateIsometry = A.jetChartMap i X := by
      funext y
      simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    have he : coordinateRealLinearized (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
        (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
      funext k
      simp only [coordinateRealLinearized,linearized,hcomp,
        planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [(P i k l).variation_zero_of_notMem (A.jetChartMap i F) hn 0,mul_zero]
    simp only [bundleRestore,he,map_zero,smul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasSupportedPolynomialVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variation of a globally defined polynomial in a chart-supported
direction is the restoration of that chart's actual local linearization. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedVariationDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedVariationFiberSpace
local instance supportedVariationDualSmul_r4f5d51_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedVariationFiberNormed
local instance supportedVariationSectionNormed_r4f5d51_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance supportedVariationSectionSpace_r4f5d51_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma restore_chart_read_on_weight (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ tsupport (A.weight i)) (hu : ∀ v w, u p v w = u p w v) :
    A.bundleRestore A.tensorTriv i (fun x => fiberFromThree (A.tensorChartRead i u x)) p = u p := by
  have hsource := A.weight_support i hp
  have hc : ∀ v w, A.bundleComponent A.tensorTriv i u p v w =
      A.bundleComponent A.tensorTriv i u p w v := by
    intro v w
    rw [A.tensorComponent_apply i u hsource,A.tensorComponent_apply i u hsource]
    exact hu _ _
  change A.outer i p • (A.tensorTriv i).symmL ℝ p
    (fiberFromThree (A.tensorChartRead i u (chart (i : M) p))) = _
  rw [A.tensorChartRead_on_weight i u hp,fiberFromThree_toThree _ hc,
    A.outer_one i p hp,one_smul]
  exact (A.tensorTriv i).symmL_continuousLinearMapAt (A.tensorTriv_domain i hsource) _

theorem supported_polynomial_variation {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (i : A.centers) (Q : Fin 3 → Fin m → Expression)
    (F X : M → Space)
    (hsp : tsupport X ⊆ tsupport (A.weight i)) (ε : ℝ)
    (hread : ∀ x ∈ (A.chartWeightCompact i : Set Base),
      coordinateRealLinearized Q ε (A.jetChartMap i F)
          (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialVariation P ε F X) x) :
    A.atlasPolynomialVariation P ε F X = A.bundleRestore A.tensorTriv i
      (fun x => fiberFromThree (coordinateRealLinearized Q ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x))) := by
  funext p
  by_cases hp : p ∈ tsupport (A.weight i)
  · have he := A.restore_chart_read_on_weight i (A.atlasPolynomialVariation P ε F X) hp
      (A.tensorPlaneRestore_symmetric _ p)
    have hr := hread (chart (i : M) p) ⟨p,hp,rfl⟩
    change _ = A.outer i p • (A.tensorTriv i).symmL ℝ p (fiberFromThree _)
    rw [hr]
    exact he.symm
  · have hX : p ∉ tsupport X := fun hx => hp (hsp hx)
    rw [A.atlasPolynomialVariation_zero_of_notMem P ε F X hX]
    by_cases ho : A.outer i p = 0
    · simp only [bundleRestore,ho,zero_smul]
    · have hsource := A.outer_support i (subset_tsupport (A.outer i) ho)
      have hn : chart (i : M) p ∉ tsupport (A.jetChartMap i X) :=
        notMem_tsupport_iff_eventuallyEq.mpr
          (A.jetChartMap_eventually_zero i hsource (notMem_tsupport_iff_eventuallyEq.mp hX))
      have hcomp : (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘
          planeCoordinateIsometry = A.jetChartMap i X := by
        funext y
        simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
      have hz : coordinateRealLinearized Q ε (A.jetChartMap i F)
          (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
          (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        funext k
        simp only [coordinateRealLinearized,linearized,hcomp,
          planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
        apply Finset.sum_eq_zero
        intro l _
        rw [(Q k l).variation_zero_of_notMem (A.jetChartMap i F) hn 0,mul_zero]
      simp only [bundleRestore,hz,map_zero,smul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasRestoredPolynomialDirection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported Euclidean field is restored with exactly its original
localized jet, so the local polynomial solver acts on the actual direction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberSpace
local instance restoredDirectionDualSmul_r4f5d51_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberNormed
local instance restoredDirectionSectionNormed_r4f5d51_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredDirectionSectionSpace_r4f5d51_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma jetChartMap_restored_direction (i : A.centers) (X : RealModes.RField 4)
    (hX : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.jetChartMap i (restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) = X ∘ planeCoordinateIsometry := by
  have hsp := (tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) X).trans hX
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · change spaceCoordinates (localize (i : M) (A.outer i)
      (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) x) = _
    rw [localize,indicator_of_mem hx,A.restore_plane_in_coordinates i _ hsp hx]
    simp only [Function.comp_apply,map_smul,ContinuousLinearEquiv.apply_symm_apply]
    by_cases hz : X (planeCoordinateIsometry x) = 0
    · rw [hz,smul_zero]
    · have hp : (chart (i : M)).symm x ∈ tsupport (A.weight i) := by
        apply A.mem_weight_support_of_plane i ((chart (i : M)).map_target hx)
        rw [(chart (i : M)).right_inv hx]
        exact hX (subset_tsupport X hz)
      rw [A.outer_one i _ hp,one_pow,one_smul]
  · have hz : X (planeCoordinateIsometry x) = 0 := by
      by_contra hn
      obtain ⟨y,hy,he⟩ := hX (subset_tsupport X hn)
      have hyx : y = x := planeCoordinateIsometry.injective he
      subst y
      obtain ⟨p,hp,rfl⟩ := hy
      exact hx ((chart (i : M)).map_source (A.weight_support i hp))
    change spaceCoordinates (localize (i : M) (A.outer i) _ x) = _
    rw [localize,indicator_of_notMem hx,map_zero]
    exact hz.symm

theorem restored_polynomial_direction_oai {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (i : A.centers) (Q : Fin 3 → Fin m → Expression)
    (F : M → Space) (X : RealModes.RField 4)
    (hsp : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) (ε : ℝ)
    (hread : ∀ x ∈ (A.chartWeightCompact i : Set Base),
      coordinateRealLinearized Q ε (A.jetChartMap i F) X 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialVariation P ε F
          (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry))) x) :
    A.atlasPolynomialVariation P ε F
      (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun x => fiberFromThree
        (coordinateRealLinearized Q ε (A.jetChartMap i F) X 0 (planeCoordinateIsometry x))) := by
  have hs := A.restore_plane_tsupport i (spaceCoordinates.symm ∘ X)
    ((tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) X).trans hsp)
  have he : A.jetChartMap i (restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) ∘ planeCoordinateIsometry.symm = X := by
    rw [A.jetChartMap_restored_direction i X hsp]
    funext y
    simp only [Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
  have hh := A.supported_polynomial_variation P i Q F
    (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) hs ε
  simpa only [he] using hh (by simpa only [he] using hread)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_direction_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_direction_oai.{u_1}
