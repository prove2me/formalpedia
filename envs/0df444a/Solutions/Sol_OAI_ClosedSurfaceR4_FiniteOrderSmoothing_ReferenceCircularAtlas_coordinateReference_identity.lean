-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:36:19.44332+00:00
-- url     : https://prove2.me/submissions/0912782b-6ef9-4912-b0cc-c7df5c828a35

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveFullOperator_frame

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SpatialPhaseBasis
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual point-dependent phase bases. Outside the region of invertible
phase triples a fixed basis supplies harmless global values. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma resolvedPhaseBasis_covectors (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : admissiblePhaseCovectors P xi) : (resolvedPhaseBasis P xi).ξ = xi := by
  simp only [resolvedPhaseBasis,dite_eq_left hxi]

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

lemma centeredSpatialBasis_covectors (P : PhaseBasis) (ell : Fin 3 → Base) (L : ℝ)
    (c p : Base)
    (hp : admissiblePhaseCovectors P
      (fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p)) :
    (centeredSpatialBasis P ell L c p).ξ =
      fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p :=
  resolvedPhaseBasis_covectors P hp

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
local instance coordinateFiberSpace_r1e7d08_1 : NormedSpace ℝ TensorFiber := inferInstance
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CurvedAtlasPrimitives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
local instance curvedPrimitiveFiberNormed_r1e7d08_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance curvedPrimitiveFiberSpace_r1e7d08_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance curvedPrimitiveDualAdd_r1e7d08_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance curvedPrimitiveDualSmul_r1e7d08_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M) (P : A.centers → JetPolynomial.Base → PhaseBasis)
  (u : ∀ p : M, CovariantTwoTensor p)

local instance curvedPrimitiveSectionNormed_r1e7d08_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance curvedPrimitiveSectionSpace_r1e7d08_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma curvedAtlasPhase_smooth (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j)) (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.curvedAtlasPhase phi a) :=
  restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
    ((hphi a.1 a.2).comp JetPolynomial.planeCoordinateIsometry.contDiff)

lemma curvedAtlasPhase_eventually (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (a : A.centers × Fin 3)
    (houter : ∀ p ∈ tsupport (A.weight a.1), A.outer a.1 =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight a.1)) :
    A.curvedAtlasPhase phi a =ᶠ[𝓝 p] (phi a.1 a.2 ∘ coordinateChart (a.1 : M)) := by
  filter_upwards [houter p hp,
    (chart (a.1 : M)).open_source.mem_nhds (A.weight_support a.1 hp)] with x hx hxs
  rw [curvedAtlasPhase,restore,indicator_of_mem hxs,hx,one_smul]
  rfl

lemma curvedAtlasPhase_mfderiv (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j)) (a : A.centers × Fin 3)
    (houter : ∀ p ∈ tsupport (A.weight a.1), A.outer a.1 =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight a.1)) :
    mfderiv planeModel 𝓘(ℝ) (A.curvedAtlasPhase phi a) p =
      (fderiv ℝ (phi a.1 a.2) (coordinateChart (a.1 : M) p)).comp
        (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart (a.1 : M)) p) := by
  have he := A.curvedAtlasPhase_eventually phi a houter hp
  have hd := he.mfderiv_eq (I := planeModel) (I' := 𝓘(ℝ))
  have hpS : p ∈ (coordinateChart (a.1 : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support a.1 hp
  have hc := ((coordinateChart_smoothOn (a.1 : M)) p hpS).contMDiffAt
    ((coordinateChart (a.1 : M)).open_source.mem_nhds hpS)
  rw [mfderiv_comp p
    ((hphi a.1 a.2).contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv] at hd
  change (mfderiv planeModel 𝓘(ℝ) (A.curvedAtlasPhase phi a) p : Plane →L[ℝ] ℝ) =
    (ContinuousLinearMap.id ℝ ℝ).comp
      ((fderiv ℝ (phi a.1 a.2) (coordinateChart (a.1 : M) p)).comp
        (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart (a.1 : M)) p)) at hd
  simpa only [ContinuousLinearMap.id_comp] using hd

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveFiberInverse
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite rank-one correction acts on symmetric tensors. Adding the
identity on the antisymmetric summand gives an honest invertible operator
on the full four-dimensional tensor fiber, without an orientation choice. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseFiberNormed
local instance primitiveInverseFiberSpace_r1e7d08_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveInverseFiberComplete_r1e7d08_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseFiberGroup
lemma tensorSymmetrizer_apply (B : TensorFiber) (v w : Plane) :
    tensorSymmetrizer B v w = (B v w+B w v)/2 := by
  change (1/2 : ℝ)*(B v w+B w v) = (B v w+B w v)/2
  ring

lemma tensorSymmetrizer_symmetric (B : TensorFiber) (v w : Plane) :
    tensorSymmetrizer B v w = tensorSymmetrizer B w v := by
  rw [tensorSymmetrizer_apply,tensorSymmetrizer_apply,add_comm]

lemma tensorSymmetrizer_eq_self {B : TensorFiber} (hB : ∀ v w, B v w = B w v) :
    tensorSymmetrizer B = B := by
  ext v w
  rw [tensorSymmetrizer_apply,hB v w]
  ring

lemma tensorSymmetrizer_idempotent (B : TensorFiber) :
    tensorSymmetrizer (tensorSymmetrizer B) = tensorSymmetrizer B :=
  tensorSymmetrizer_eq_self (tensorSymmetrizer_symmetric B)

variable {ι : Type*} [Fintype ι]

lemma finitePrimitiveOperator_apply (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    finitePrimitiveOperator q psi xi B =
      ∑ i, ((psi i)^2*q i (tensorSymmetrizer B)) • ((xi i).smulRight (xi i)) := by
  simp only [finitePrimitiveOperator,sum_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,smul_smul]

lemma finitePrimitiveOperator_symmetrizer (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    finitePrimitiveOperator q psi xi (tensorSymmetrizer B) = finitePrimitiveOperator q psi xi B := by
  simp only [finitePrimitiveOperator_apply,tensorSymmetrizer_idempotent]

lemma completedPrimitiveOperator_apply (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    completedPrimitiveOperator q psi xi B =
      finitePrimitiveOperator q psi xi B+B-tensorSymmetrizer B := rfl

lemma completedPrimitiveOperator_eq_id
    (q : ι → TensorFiber →L[ℝ] ℝ) (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ)
    (hbase : ∀ B : TensorFiber, (∀ v w, B v w = B w v) →
      finitePrimitiveOperator q psi xi B = B) :
    completedPrimitiveOperator q psi xi = ContinuousLinearMap.id ℝ TensorFiber := by
  ext B v w
  have hb := hbase (tensorSymmetrizer B) (tensorSymmetrizer_symmetric B)
  rw [finitePrimitiveOperator_symmetrizer] at hb
  rw [completedPrimitiveOperator_apply,hb]
  simp only [add_apply,sub_apply,ContinuousLinearMap.id_apply]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPrimitiveOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fiberwise correction operator for independently perturbed
primitive cutoffs. Its reference value is the identity, and its inverse
solves the finite rank-one equation on the original tensor bundle. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberSpace
local instance atlasOperatorFiberComplete_r1e7d08_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberSpace
local instance atlasOperatorFiberComplete_r1e7d08_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionNormed
local instance atlasOperatorSectionSpace_r1e7d08_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionGroup
lemma local_primitive_operator_decomposition
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hfit : ∀ i j p, p ∈ tsupport (A.weight i) →
      (P i (chart (i : M) p)).ξ j = phaseDerivative (phi i j) (coordinateChart (i : M) p))
    (i : A.centers) {p : M} (hp : p ∈ tsupport (A.weight i))
    (B : CovariantTwoTensor p) (hB : ∀ v w, B v w = B w v) :
    ∑ j : Fin 3, A.primitiveCoefficientField P (i,j) p B •
      (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p).smulRight
        (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p) = B := by
  let C : TensorFiber := (A.tensorTriv i).continuousLinearMapAt ℝ p B
  let T := (trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
  let u : ∀ x : M, CovariantTwoTensor x := fun _ => (show TensorFiber from B)
  have hpS := A.weight_support i hp
  have hC : ∀ v w, C v w = C w v := by
    intro v w
    change A.bundleComponent A.tensorTriv i u p v w = A.bundleComponent A.tensorTriv i u p w v
    rw [A.tensorComponent_apply i u hpS,A.tensorComponent_apply i u hpS]
    exact hB _ _
  have hd := congrArg fiberFromThree ((P i (chart (i : M) p)).decomposition (fiberToThree C))
  simp only [map_sum,map_smul] at hd
  rw [fiberFromThree_toThree C hC] at hd
  have hval (j : Fin 3) (v : Plane) :
      A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p v =
        phaseLinear ((P i (chart (i : M) p)).ξ j) (planeCoordinates (T v)) := by
    rw [primitivePhaseCovector,A.curvedAtlasPhase_mfderiv phi hphi (i,j) (houter i) hp,
      A.coordinateChart_tangentCoordinates i hpS]
    change fderiv ℝ (phi i j) (coordinateChart (i : M) p) (planeCoordinates (T v)) = _
    rw [hfit i j p hp,phaseLinear_phaseDerivative]
  ext v w
  have he := congrArg (fun D : TensorFiber => D (T v) (T w)) hd
  simp only [sum_apply,smul_apply,smul_eq_mul,fiberFromThree_apply,covectorSquare_evaluate] at he
  have heB : C (T v) (T w) = B v w := A.tensorComponent_tangentCoordinates i u hpS v w
  simp only [sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,hval]
  change (∑ j : Fin 3, (P i (chart (i : M) p)).Q j (fiberToThree C) *
    (phaseLinear ((P i (chart (i : M) p)).ξ j) (planeCoordinates (T v)) *
      phaseLinear ((P i (chart (i : M) p)).ξ j) (planeCoordinates (T w)))) = _
  exact he.trans heB

/-- At the original square partition the completed operator is exactly the
identity, on the full tensor fiber rather than only on a quotient. -/
theorem primitiveFullOperator_reference
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hfit : ∀ i j p, p ∈ tsupport (A.weight i) →
      (P i (chart (i : M) p)).ξ j = phaseDerivative (phi i j) (coordinateChart (i : M) p))
    (p : M) :
    A.primitiveFullOperator P (fun a => A.weight a.1) (A.curvedAtlasPhase phi) p =
      ContinuousLinearMap.id ℝ (CovariantTwoTensor p) := by
  apply completedPrimitiveOperator_eq_id
  intro B hB
  rw [finitePrimitiveOperator_apply,tensorSymmetrizer_eq_self hB,
    ← Finset.univ_product_univ,Finset.sum_product]
  have hi (i : A.centers) :
      (∑ j : Fin 3, ((A.weight i p)^2*A.primitiveCoefficientField P (i,j) p B) •
        (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p).smulRight
          (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p)) = (A.weight i p)^2 • B := by
    by_cases hw : A.weight i p = 0
    · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_smul,Finset.sum_const_zero]
    · rw [show (∑ j : Fin 3, ((A.weight i p)^2*A.primitiveCoefficientField P (i,j) p B) •
          (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p).smulRight
            (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p)) =
          (A.weight i p)^2 • (∑ j : Fin 3, A.primitiveCoefficientField P (i,j) p B •
            (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p).smulRight
              (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p)) by
            simp only [Finset.smul_sum,smul_smul]]
      rw [A.local_primitive_operator_decomposition P phi hphi houter hfit i
        (subset_tsupport _ hw) B hB]
  simp_rw [hi]
  rw [← Finset.sum_smul,A.partition p,one_smul]

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

variable [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_compact (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsCompact (circularDiskClosure p r) :=
  (circularCoordinateRegion_compact p r).image_of_continuousOn
    ((coordinateChart p).continuousOn_symm.mono hregion)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularDiskTopology
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentCircularRealization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite geometric iteration using independently chosen local
convex phases and one fixed background norm for all prefix bounds. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

omit [CompactSpace M] in
lemma circular_weight_support {B : SmoothingAtlas M} (r : B.centers → ℝ)
    (hreg : ∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target)
    (hnon : ∀ i p, 0 ≤ B.weight i p)
    (hpos : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i))
    (i : B.centers) : tsupport (B.weight i) ⊆ circularDiskClosure (i : M) (r i) := by
  apply closure_minimal _ (circularDiskClosure_compact (i : M) (r i) (hreg i)).isClosed
  intro p hp
  have hd := (hpos i p).mp (lt_of_le_of_ne (hnon i p) (Ne.symm hp))
  exact (circularDiskClosure_iff (i : M) (hreg i) p).mpr ⟨hd.1,hd.2.le⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ReferenceCircularOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected reference atlas supplies the actual identity operator,
smooth coefficient germs, and positive metric coefficients. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

omit [CompactSpace M] in
lemma supported (i : d.B.centers) :
    tsupport (d.B.weight i) ⊆ circularDiskClosure (i : M) (d.radius i) :=
  circular_weight_support d.radius d.region d.weight_nonneg d.weight_positive i

omit [CompactSpace M] in
lemma basis_covectors (i : d.B.centers) {p : M} (hp : p ∈ tsupport (d.B.weight i)) :
    (d.basis i (chart (i : M) p)).ξ =
      fun j => phaseDerivative (d.localPhases i j) (coordinateChart (i : M) p) :=
  centeredSpatialBasis_covectors _ _ _ _ _ (d.admissible i p (d.supported i hp))

omit [CompactSpace M] in
lemma operator_identity (p : M) :
    d.B.primitiveFullOperator d.basis (fun a => d.B.weight a.1) d.globalPhases p =
      ContinuousLinearMap.id ℝ (CovariantTwoTensor p) :=
  d.B.primitiveFullOperator_reference d.basis d.localPhases
    (fun _ _ => centeredConvexPhase_smooth _ _ _) d.outer
    (fun i _ _p hp => congrFun (d.basis_covectors i hp) _) p

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorMask
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inactive primitive entries may be replaced before estimating the
finite operator; their cutoff is exactly zero. -/
noncomputable section
open Set
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.maskFiberNormed
local instance maskFiberSpace_r1e7d08_1 : NormedSpace ℝ TensorFiber := inferInstance
lemma completedPrimitiveOperator_mask
    (q : ι → TensorFiber →L[ℝ] ℝ) (w : ι → ℝ)
    (v v₀ : ι → Plane →L[ℝ] ℝ) (S : Set ι) [DecidablePred (· ∈ S)]
    (hz : ∀ a, a ∉ S → w a = 0) :
    completedPrimitiveOperator q w v =
      completedPrimitiveOperator (fun a => if a ∈ S then q a else 0) w
        (fun a => if a ∈ S then v a else v₀ a) := by
  apply ContinuousLinearMap.ext
  intro H
  simp only [completedPrimitiveOperator_apply,finitePrimitiveOperator_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S
  · simp only [ha,ite_true, if_true]
  · simp only [ha,ite_false, if_false,hz a ha,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed active-chart coordinate data represent the genuine inverse and
amplitude, while vanishing cutoff terms eliminate the other charts. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDataDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDataFiberSpace
local instance coordinateDataDualSmul_r1e7d08_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDataFiberNormed
local instance coordinateDataSectionNormed_r1e7d08_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordinateDataSectionSpace_r1e7d08_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma primitiveCoordinateData_operator
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (u : ∀ p : M, CovariantTwoTensor p) (i : B.centers)
    (S : Set (B.centers × Fin 3)) {p : M} (hp : p ∈ (chart (i : M)).source)
    (hz : ∀ a ∉ S, psi a p = 0) :
    primitiveDataOperator (B.primitiveCoordinateData P psi phi u i S (chart (i : M) p)).1 =
      B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p) := by
  classical
  rw [B.primitiveFullOperator_frame P psi phi i hp,
    completedPrimitiveOperator_mask _ _ _ (fun _ => 0) S hz]
  unfold primitiveCoordinateData primitiveDataOperator
  rw [(chart (i : M)).left_inv hp]
  simp only [coefficientFrameRead,(chart (i : M)).left_inv hp]
  congr 1
  funext a
  split_ifs with ha
  · exact (B.covectorFrame_mfderiv (phi a) (hphi a) i hp).symm
  · rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ReferenceCoordinateData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size, identity and positivity of the fixed reference data in any active
chart. The constants precede every independent radius and phase choice. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refDataFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refDataDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refDataFiberNormed
local instance refDataDualSpace_r1e7d08_1 : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance refDataDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace ReferenceCircularAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refDataFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refDataDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refDataFiberNormed
local instance refDataDualSpace_r1e7d08_2 : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance refDataDualSmul_r1e7d08_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance refDataSectionNormed_r1e7d08_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance refDataSectionSpace_r1e7d08_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma coordinateReference_identity_oai (i : d.B.centers) {p : M}
    (hp : p ∈ tsupport (d.B.weight i)) :
    primitiveDataOperator (d.coordinateReference i p).1 = ContinuousLinearMap.id ℝ TensorFiber := by
  classical
  unfold coordinateReference
  rw [d.B.primitiveCoordinateData_operator d.basis (fun a => d.B.weight a.1) d.globalPhases
    (fun a => d.B.curvedAtlasPhase_smooth d.localPhases
      (fun _ _ => PhaseGeometry.centeredConvexPhase_smooth _ _ _) a)
    gref.inner i {a | p ∈ tsupport (d.B.weight a.1)} (d.B.weight_support i hp)
    (fun a ha => image_eq_zero_of_notMem_tsupport ha),d.operator_identity]
  apply ContinuousLinearMap.ext
  intro H
  change (d.B.tensorTriv i).continuousLinearMapAt ℝ p ((d.B.tensorTriv i).symmL ℝ p H) = H
  exact (d.B.tensorTriv i).continuousLinearMapAt_symmL (R := ℝ)
    (d.B.tensorTriv_domain i (d.B.weight_support i hp)) H

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference_identity_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference_identity_oai.{u_1}
