-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:51.554641+00:00
-- url     : https://prove2.me/submissions/48e7b875-9775-4489-aed1-eea5ee09e6c8

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
local instance frameBoundSectionNormed_r8e0706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameBoundSectionSpace_r8e0706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] [T2Space M] in
lemma coefficientFrame_coordChange
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source) :
    B.coefficientFrame P i a p =
      ((P a.1 (chart (a.1 : M) p)).Q a.2).comp (fiberToThree.comp
        ((B.tensorTriv i).coordChangeL ℝ (B.tensorTriv a.1) p : TensorFiber →L[ℝ] TensorFiber)) := by
  apply ContinuousLinearMap.ext
  intro H
  change (P a.1 (chart (a.1 : M) p)).Q a.2
      (fiberToThree ((B.tensorTriv a.1).continuousLinearMapAt ℝ p
        ((B.tensorTriv i).symmL ℝ p H))) = _
  rw [(B.tensorTriv a.1).continuousLinearMapAt_apply_of_mem ℝ (B.tensorTriv_domain a.1 ha),
    (B.tensorTriv i).symmL_apply (R := ℝ) (B.tensorTriv_domain i hi),
    ← (B.tensorTriv i).coordChangeL_apply (R := ℝ) (B.tensorTriv a.1)
      ⟨B.tensorTriv_domain i hi,B.tensorTriv_domain a.1 ha⟩]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoefficientCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-derivative bounds for coefficient functionals in each overlapping
primitive chart, fixed before choosing any independent phases or radii. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberNormed
local instance coefficientReadDerivativeNormed_r8e0706_1 : NormedAddCommGroup
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeSpace_r8e0706_1 : NormedSpace ℝ
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadPairNormed_r8e0706_1 : NormedAddCommGroup
    ((TensorFiber →L[ℝ] ℝ) × (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ)) := inferInstance
local instance coefficientReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberNormed
local instance coefficientReadDerivativeNormed_r8e0706_2 : NormedAddCommGroup
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeSpace_r8e0706_2 : NormedSpace ℝ
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadPairNormed_r8e0706_2 : NormedAddCommGroup
    ((TensorFiber →L[ℝ] ℝ) × (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ)) := inferInstance
local instance coefficientReadDualSmul_r8e0706_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

local instance coefficientReadSectionNormed_r8e0706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coefficientReadSectionSpace_r8e0706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma coefficientFrame_smoothAt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source)
    (hQ : ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] ℝ) ∞ (B.coefficientFrame P i a) p := by
  have hq := hQ.contMDiffAt.comp p
    ((chart_smooth (a.1 : M) p ha).contMDiffAt ((chart (a.1 : M)).open_source.mem_nhds ha))
  have hT := (contMDiffOn_coordChangeL (IB := planeModel) (n := ∞)
    (B.tensorTriv i) (B.tensorTriv a.1)).contMDiffAt
    ((B.tensorTriv i).open_baseSet.inter (B.tensorTriv a.1).open_baseSet |>.mem_nhds
      ⟨B.tensorTriv_domain i hi,B.tensorTriv_domain a.1 ha⟩)
  have hconst : ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] PhaseMean.Tensor) ∞
      (fun _ : M => fiberToThree) p := contMDiffAt_const
  apply (hq.clm_comp (hconst.clm_comp hT)).congr_of_eventuallyEq
  filter_upwards [((chart (i : M)).open_source.inter (chart (a.1 : M)).open_source).mem_nhds
    ⟨hi,ha⟩] with q hq
  exact B.coefficientFrame_coordChange P i a hq.1 hq.2

omit [CompactSpace M] in
lemma coefficientFrameRead_smoothAt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source)
    (hQ : ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ContDiffAt ℝ ∞ (B.coefficientFrameRead P i a) (chart (i : M) p) := by
  have hx := (chart (i : M)).map_source hi
  have hsym := ((chart_symm_smooth (i : M)) _ hx).contMDiffAt
    ((chart (i : M)).open_target.mem_nhds hx)
  have hout : ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] ℝ) ∞
      (B.coefficientFrame P i a) ((chart (i : M)).symm (chart (i : M) p)) := by
    rw [(chart (i : M)).left_inv hi]
    exact B.coefficientFrame_smoothAt P i a hi ha hQ
  have h := hout.comp (chart (i : M) p) hsym
  exact h.contDiffAt

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCovectorFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact parameter bounds for the actual circular phase differentials,
including their first spatial derivatives. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

omit [CompactSpace M] [T2Space M] in
lemma phaseCovectorRead_smoothOn (i : B.centers) (phi : M → ℝ)
    (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi) :
    ContDiffOn ℝ ∞ (B.phaseCovectorRead i phi) (chart (i : M)).target := by
  have h := (hphi.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  exact (h.fderiv_of_isOpen (chart (i : M)).open_target (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiffOn_const

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorFrameReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
local instance tensorReadBoundsSectionNormed_r8e0706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorReadBoundsSectionSpace_r8e0706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorFrameRead_smoothOn (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiffOn ℝ ∞ (B.tensorFrameRead i u) (chart (i : M)).target := by
  have h := (B.bundleComponent_smooth_on B.tensorTriv B.tensorTriv_domain i hu).comp
    (chart_symm_smooth (i : M)) (fun _ hx => (chart (i : M)).map_target hx)
  exact h.contDiffOn

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveDataC1
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First derivatives of finite primitive data are bounded componentwise. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataCovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataCovectorSpace
local instance finiteDataFiberT2 : T2Space TensorFiber := inferInstance
local instance finiteDataDualT2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance finiteDataCovectorT2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]
local instance finiteDataNormed_r8e0706_1 : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataSpace
local instance finiteDataT2 : T2Space (PrimitiveAmplitudeData ι) := inferInstance

theorem primitive_data_fderiv_bound
    (q : ι → JetPolynomial.Base → TensorFiber →L[ℝ] ℝ)
    (w : ι → JetPolynomial.Base → ℝ)
    (v : ι → JetPolynomial.Base → Plane →L[ℝ] ℝ)
    (H : JetPolynomial.Base → TensorFiber) (x : JetPolynomial.Base)
    (hq : ∀ a, DifferentiableAt ℝ (q a) x)
    (hw : ∀ a, DifferentiableAt ℝ (w a) x)
    (hv : ∀ a, DifferentiableAt ℝ (v a) x) (hH : DifferentiableAt ℝ H x)
    {D : ℝ} (hD : 0 ≤ D)
    (hbq : ∀ a, ‖fderiv ℝ (q a) x‖ ≤ D)
    (hbw : ∀ a, ‖fderiv ℝ (w a) x‖ ≤ D)
    (hbv : ∀ a, ‖fderiv ℝ (v a) x‖ ≤ D) (hbH : ‖fderiv ℝ H x‖ ≤ D) :
    ‖fderiv ℝ (fun y => (((((fun a => q a y),fun a => w a y),fun a => v a y),H y) :
      PrimitiveAmplitudeData ι)) x‖ ≤ D := by
  have hq' := hasFDerivAt_pi.mpr (fun a => (hq a).hasFDerivAt)
  have hw' := hasFDerivAt_pi.mpr (fun a => (hw a).hasFDerivAt)
  have hv' := hasFDerivAt_pi.mpr (fun a => (hv a).hasFDerivAt)
  have he := ((hq'.prodMk hw').prodMk hv').prodMk hH.hasFDerivAt
  change ‖fderiv ℝ (fun y => ((((fun a => q a y),fun a => w a y),fun a => v a y),H y)) x‖ ≤ D
  rw [he.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro y
  have hqy : ‖fun a => fderiv ℝ (q a) x y‖ ≤ D*‖y‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hD (norm_nonneg y))).mpr
      (fun a => ((fderiv ℝ (q a) x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hbq a) (norm_nonneg y)))
  have hwy : ‖fun a => fderiv ℝ (w a) x y‖ ≤ D*‖y‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hD (norm_nonneg y))).mpr
      (fun a => ((fderiv ℝ (w a) x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hbw a) (norm_nonneg y)))
  have hvy : ‖fun a => fderiv ℝ (v a) x y‖ ≤ D*‖y‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hD (norm_nonneg y))).mpr
      (fun a => ((fderiv ℝ (v a) x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hbv a) (norm_nonneg y)))
  have hHy := ((fderiv ℝ H x).le_opNorm y).trans (mul_le_mul_of_nonneg_right hbH (norm_nonneg y))
  exact max_le (max_le (max_le hqy hwy) hvy) hHy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-derivative control of the actual amplitude from its finite active
chart data. The data bounds involve only first jets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorSpace
local instance coordDerivFiberT2_r8e0706_1 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2_r8e0706_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2_r8e0706_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorSpace
local instance coordDerivFiberT2_r8e0706_2 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2_r8e0706_2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2_r8e0706_2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance coordDerivDualAdd_r8e0706_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSmul
variable (B : SmoothingAtlas M)

local instance coordDerivSectionNormed_r8e0706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordDerivSectionSpace_r8e0706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance coordDerivDataNormed_r8e0706_1 : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coordDerivDataSpace
local instance coordDerivDataT2_r8e0706_1 : T2Space (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
local instance coordDerivDataDualNormed_r8e0706_1 : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3) →L[ℝ] ℝ) := inferInstance
local instance coordDerivDataDualSpace_r8e0706_1 : NormedSpace ℝ (PrimitiveAmplitudeData (B.centers × Fin 3) →L[ℝ] ℝ) := inferInstance
theorem primitiveCoordinateData_fderiv_bound_oai
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hQ : ∀ (a : B.centers × Fin 3) (p : M), p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (i : B.centers) {p : M} (hp : p ∈ tsupport (B.weight i))
    {D : ℝ} (hD : 0 ≤ D)
    (hbq : ∀ a, p ∈ tsupport (B.weight a.1) →
      ‖fderiv ℝ (B.coefficientFrameRead P i a) (chart (i : M) p)‖ ≤ D)
    (hbw : ∀ a, ‖fderiv ℝ (psi a ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D)
    (hbv : ∀ a, p ∈ tsupport (B.weight a.1) →
      ‖fderiv ℝ (B.phaseCovectorRead i (phi a)) (chart (i : M) p)‖ ≤ D)
    (hbH : ‖fderiv ℝ (B.tensorFrameRead i u) (chart (i : M) p)‖ ≤ D) :
    ‖fderiv ℝ (B.primitiveCoordinateData P psi phi u i
      {a | p ∈ tsupport (B.weight a.1)}) (chart (i : M) p)‖ ≤ D := by
  classical
  let x := chart (i : M) p
  let q := fun (a : B.centers × Fin 3) (y : JetPolynomial.Base) => if p ∈ tsupport (B.weight a.1) then B.coefficientFrameRead P i a y else 0
  let w := fun a => psi a ∘ (chart (i : M)).symm
  let v := fun (a : B.centers × Fin 3) (y : JetPolynomial.Base) => if p ∈ tsupport (B.weight a.1) then B.phaseCovectorRead i (phi a) y else 0
  have hs := B.weight_support i hp
  have ht := (chart (i : M)).map_source hs
  have hq (a : B.centers × Fin 3) : DifferentiableAt ℝ (q a) x := by
    dsimp only [q]
    split_ifs with ha
    · exact (B.coefficientFrameRead_smoothAt P i a hs (B.weight_support a.1 ha)
        (hQ a p ha)).differentiableAt (by simp)
    · exact differentiableAt_const _
  have hw (a : B.centers × Fin 3) : DifferentiableAt ℝ (w a) x :=
    (((hpsi a).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn.contDiffAt
      ((chart (i : M)).open_target.mem_nhds ht)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hv (a : B.centers × Fin 3) : DifferentiableAt ℝ (v a) x := by
    dsimp only [v]
    split_ifs with ha
    · exact ((B.phaseCovectorRead_smoothOn i (phi a) (hphi a)).contDiffAt
        ((chart (i : M)).open_target.mem_nhds ht)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · exact differentiableAt_const _
  have hH := ((B.tensorFrameRead_smoothOn i u hu).contDiffAt
    ((chart (i : M)).open_target.mem_nhds ht)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply primitive_data_fderiv_bound q w v (B.tensorFrameRead i u) x hq hw hv hH hD
  · intro a
    dsimp only [q]
    split_ifs with ha
    · exact hbq a ha
    · simpa only [fderiv_const_apply,norm_zero] using hD
  · exact hbw
  · intro a
    dsimp only [v]
    split_ifs with ha
    · exact hbv a ha
    · simpa only [fderiv_const_apply,norm_zero] using hD
  · exact hbH

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound_oai.{u_1}
