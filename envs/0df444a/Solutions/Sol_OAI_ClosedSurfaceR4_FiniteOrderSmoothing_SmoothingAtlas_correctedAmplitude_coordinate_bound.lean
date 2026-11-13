-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedAmplitude_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:40:00.002708+00:00
-- url     : https://prove2.me/submissions/d8715fbe-69b1-42fe-907d-aba2666e0bf9

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
local instance primitiveInverseFiberSpace_rf1d185_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveInverseFiberComplete_rf1d185_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualSmul
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseFiberGroup
lemma finitePrimitiveOperator_apply (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    finitePrimitiveOperator q psi xi B =
      ∑ i, ((psi i)^2*q i (tensorSymmetrizer B)) • ((xi i).smulRight (xi i)) := by
  simp only [finitePrimitiveOperator,sum_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,smul_smul]

lemma completedPrimitiveOperator_apply (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    completedPrimitiveOperator q psi xi B =
      finitePrimitiveOperator q psi xi B+B-tensorSymmetrizer B := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorOperatorFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tensor operators and their inverses in a fixed primitive frame. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorFrameDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorFrameFiberSpace
local instance operatorFrameDualSmul_rf1d185_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorFrameFiberNormed
local instance operatorFrameSectionNormed_rf1d185_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance operatorFrameSectionSpace_rf1d185_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorOperatorFrame_inverse_apply (i : B.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source)
    (T : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (H : CovariantTwoTensor p) :
    (B.tensorOperatorFrame i p T).inverse ((B.tensorTriv i).continuousLinearMapAt ℝ p H) =
      (B.tensorTriv i).continuousLinearMapAt ℝ p (T.inverse H) := by
  let e := (B.tensorTriv i).continuousLinearEquivAt ℝ p (B.tensorTriv_domain i hp)
  have he : B.tensorOperatorFrame i p T =
      (e : CovariantTwoTensor p →L[ℝ] TensorFiber).comp
        (T.comp (e.symm : TensorFiber →L[ℝ] CovariantTwoTensor p)) := by
    simp only [e,Trivialization.coe_continuousLinearEquivAt_eq',Trivialization.symm_continuousLinearEquivAt_eq']
    rfl
  have hec : (e : CovariantTwoTensor p →L[ℝ] TensorFiber) =
      (B.tensorTriv i).continuousLinearMapAt ℝ p :=
    Trivialization.coe_continuousLinearEquivAt_eq' _ _
  rw [he, ← hec]
  change ((e : CovariantTwoTensor p →L[ℝ] TensorFiber).comp
    (T.comp (e.symm : TensorFiber →L[ℝ] CovariantTwoTensor p))).inverse (e H) = e (T.inverse H)
  simp only [ContinuousLinearMap.inverse_equiv_comp,ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

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
local instance frameBoundSectionNormed_rf1d185_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameBoundSectionSpace_rf1d185_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance coefficientReadDerivativeNormed_rf1d185_1 : NormedAddCommGroup
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeSpace_rf1d185_1 : NormedSpace ℝ
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadPairNormed_rf1d185_1 : NormedAddCommGroup
    ((TensorFiber →L[ℝ] ℝ) × (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ)) := inferInstance
local instance coefficientReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberNormed
local instance coefficientReadDerivativeNormed_rf1d185_2 : NormedAddCommGroup
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeSpace_rf1d185_2 : NormedSpace ℝ
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadPairNormed_rf1d185_2 : NormedAddCommGroup
    ((TensorFiber →L[ℝ] ℝ) × (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ)) := inferInstance
local instance coefficientReadDualSmul_rf1d185_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

local instance coefficientReadSectionNormed_rf1d185_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coefficientReadSectionSpace_rf1d185_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorStability
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform stability of the finite primitive inverse when its coefficient
functionals, cutoffs and phase covectors all vary independently. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberSpace
local instance dataFiberComplete_rf1d185_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd
local instance dataDualSmul_rf1d185_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberGroup
lemma primitiveDataOperator_smooth :
    ContDiff ℝ ∞ (primitiveDataOperator (ι := ι)) := by
  have hs : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι =>
      finitePrimitiveOperator z.1.1 z.1.2 z.2) := by
    apply ContDiff.sum
    intro i _
    have hp : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι => z.1.2 i) :=
      (contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp contDiff_fst)
    have hv : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι => z.2 i) :=
      (contDiff_apply ℝ (Plane →L[ℝ] ℝ) i).comp contDiff_snd
    have hq : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι =>
        (z.1.1 i).comp tensorSymmetrizer) :=
      ((contDiff_apply ℝ (TensorFiber →L[ℝ] ℝ) i).comp
        (contDiff_fst.comp contDiff_fst)).clm_comp contDiff_const
    exact (hp.pow 2).smul (hq.smulRight (hv.smulRight hv))
  exact (hs.add contDiff_const).sub contDiff_const

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
local instance tensorReadBoundsSectionNormed_rf1d185_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorReadBoundsSectionSpace_rf1d185_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact C1 control of the actual inverse and square-root amplitude map.
The parameter bounds are fixed before a later family is composed with it. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberSpace
local instance amplitudeFiberComplete : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeDualAdd
local instance amplitudeDualSmul_rf1d185_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberGroup
lemma primitiveParameterInverse_smoothAt {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible) :
    ContDiffAt ℝ ∞ primitiveParameterInverse z :=
  hz.contDiffAt_map_inverse.comp z
    (primitiveDataOperator_smooth.contDiffAt.comp z contDiffAt_fst)

lemma primitiveParameterCoefficient_smoothAt (i : ι) {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible) :
    ContDiffAt ℝ ∞ (primitiveParameterCoefficient i) z := by
  have hq : ContDiff ℝ ∞ (fun w : PrimitiveAmplitudeData ι => w.1.1.1 i) := by
    exact (contDiff_apply ℝ (TensorFiber →L[ℝ] ℝ) i).comp
      (contDiff_fst.comp (contDiff_fst.comp contDiff_fst))
  exact hq.contDiffAt.clm_apply
    ((primitiveParameterInverse_smoothAt hz).clm_apply contDiffAt_snd)

lemma primitiveParameterAmplitude_smoothAt (i : ι) {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible)
    (hp : 0 < primitiveParameterCoefficient i z) :
    ContDiffAt ℝ ∞ (primitiveParameterAmplitude i) z := by
  have hw : ContDiff ℝ ∞ (fun w : PrimitiveAmplitudeData ι => w.1.1.2 i) := by
    exact (contDiff_apply ℝ ℝ i).comp
      (contDiff_snd.comp (contDiff_fst.comp contDiff_fst))
  exact hw.contDiffAt.mul ((Real.contDiffAt_sqrt hp.ne').comp z
    (primitiveParameterCoefficient_smoothAt i hz))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeChain
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary chain-rule estimate used for each actual amplitude chart. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainTensorDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainTensorDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainPlaneDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainPlaneDualSpace
local instance ampChainFiberT2_rf1d185_1 : T2Space TensorFiber := inferInstance
local instance ampChainTensorDualT2_rf1d185_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance ampChainPlaneDualT2_rf1d185_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainDataNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainDataSpace
local instance ampChainDataDualNormed_rf1d185_1 : NormedAddCommGroup (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance ampChainDataDualSpace_rf1d185_1 : NormedSpace ℝ (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance ampChainDataT2_rf1d185_1 : T2Space (PrimitiveAmplitudeData ι) := inferInstance
theorem primitive_amplitude_chain_bound (a : ι)
    (F : JetPolynomial.Base → PrimitiveAmplitudeData ι) (x : JetPolynomial.Base)
    (hF : ContDiffAt ℝ ∞ F x) (hi : (primitiveDataOperator (F x).1).IsInvertible)
    (hp : 0 < primitiveParameterCoefficient a (F x))
    {R D : ℝ} (hR : ‖fderiv ℝ (primitiveParameterAmplitude a) (F x)‖ ≤ R)
    (hD : ‖fderiv ℝ F x‖ ≤ D) :
    ‖fderiv ℝ (primitiveParameterAmplitude a ∘ F) x‖ ≤ R*D := by
  have ho := primitiveParameterAmplitude_smoothAt a hi hp
  have hRp : 0 ≤ R := (norm_nonneg (fderiv ℝ (primitiveParameterAmplitude a) (F x))).trans hR
  rw [fderiv_comp x (ho.differentiableAt (by simp)) (hF.differentiableAt (by simp))]
  calc
    _ ≤ ‖fderiv ℝ (primitiveParameterAmplitude a) (F x)‖*‖fderiv ℝ F x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ R*D := mul_le_mul hR hD (norm_nonneg _) hRp

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
local instance maskFiberSpace_rf1d185_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance coordinateDataDualSmul_rf1d185_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDataFiberNormed
local instance coordinateDataSectionNormed_rf1d185_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordinateDataSectionSpace_rf1d185_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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

omit [CompactSpace M] in
lemma coefficientFrame_inverse
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hp : p ∈ (chart (i : M)).source)
    (T : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (H : CovariantTwoTensor p) :
    B.coefficientFrame P i a p
      ((B.tensorOperatorFrame i p T).inverse ((B.tensorTriv i).continuousLinearMapAt ℝ p H)) =
      B.primitiveCoefficientField P a p (T.inverse H) := by
  rw [B.tensorOperatorFrame_inverse_apply i hp T H]
  change B.primitiveCoefficientField P a p
    ((B.tensorTriv i).symmL ℝ p ((B.tensorTriv i).continuousLinearMapAt ℝ p (T.inverse H))) = _
  erw [(B.tensorTriv i).symmL_continuousLinearMapAt (B.tensorTriv_domain i hp)]

omit [CompactSpace M] in
lemma primitiveCoordinateData_amplitude
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (u : ∀ p : M, CovariantTwoTensor p) (i : B.centers)
    (S : Set (B.centers × Fin 3)) (a : B.centers × Fin 3) (ha : a ∈ S)
    {p : M} (hp : p ∈ (chart (i : M)).source) (hz : ∀ b ∉ S, psi b p = 0) :
    primitiveParameterAmplitude a (B.primitiveCoordinateData P psi phi u i S (chart (i : M) p)) =
      B.correctedPrimitiveAmplitude P psi phi u a p := by
  classical
  unfold primitiveParameterAmplitude primitiveParameterCoefficient primitiveParameterInverse
  rw [B.primitiveCoordinateData_operator P psi phi hphi u i S hp hz]
  change psi a ((chart (i : M)).symm (chart (i : M) p)) *
    Real.sqrt ((if a ∈ S then B.coefficientFrameRead P i a (chart (i : M) p) else 0)
      ((B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p)).inverse
        ((B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm (chart (i : M) p))
          (u ((chart (i : M)).symm (chart (i : M) p)))))) = _
  rw [ite_eq_left ha,(chart (i : M)).left_inv hp]
  unfold coefficientFrameRead
  rw [(chart (i : M)).left_inv hp,B.coefficientFrame_inverse P i a hp]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateGerms
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite coordinate model agrees with the actual corrected amplitude
on a neighborhood, including at zero cutoff values. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateGermFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateGermDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateGermDualSpace
local instance coordinateGermDualAdd_rf1d185_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateGermDualSmul
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateGermFiberNormed
local instance coordinateGermSectionNormed_rf1d185_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordinateGermSectionSpace_rf1d185_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma primitiveCoordinateData_germ
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hs : ∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1))
    (u : ∀ p : M, CovariantTwoTensor p) (i : B.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) (a : B.centers × Fin 3)
    (ha : p ∈ tsupport (B.weight a.1)) :
    let S : Set (B.centers × Fin 3) := {b | p ∈ tsupport (B.weight b.1)}
    (fun y => primitiveParameterAmplitude a (B.primitiveCoordinateData P psi phi u i S y)) =ᶠ[𝓝 (chart (i : M) p)]
      (B.correctedPrimitiveAmplitude P psi phi u a ∘ (chart (i : M)).symm) := by
  classical
  dsimp only
  have hz : ∀ᶠ q in 𝓝 p, ∀ b : B.centers × Fin 3,
      p ∉ tsupport (B.weight b.1) → psi b q = 0 := by
    apply Filter.eventually_all.mpr
    intro b
    by_cases hb : p ∈ tsupport (B.weight b.1)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hb))
    · exact (notMem_tsupport_iff_eventuallyEq.mp (fun h => hb (hs b h))).mono (fun _ h _ => h)
  have hc : ContinuousAt (chart (i : M)).symm (chart (i : M) p) :=
    ((chart (i : M)).continuousOn_symm _ ((chart (i : M)).map_source hp)).continuousAt
      ((chart (i : M)).open_target.mem_nhds ((chart (i : M)).map_source hp))
  have hc' : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    simpa only [(chart (i : M)).left_inv hp] using hc.tendsto
  filter_upwards [hc'.eventually hz,
    (chart (i : M)).open_target.mem_nhds ((chart (i : M)).map_source hp)] with y hy hyT
  have hq := (chart (i : M)).map_target hyT
  have he := B.primitiveCoordinateData_amplitude P psi phi hphi u i
    {b | p ∈ tsupport (B.weight b.1)} a ha hq hy
  simpa only [(chart (i : M)).right_inv hyT,Function.comp_apply] using he

lemma primitiveCoordinateData_smoothAt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hQ : ∀ (a : B.centers × Fin 3) (p : M), p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (i : B.centers) {p : M} (hp : p ∈ tsupport (B.weight i)) :
    let S : Set (B.centers × Fin 3) := {b | p ∈ tsupport (B.weight b.1)}
    ContDiffAt ℝ ∞ (B.primitiveCoordinateData P psi phi u i S) (chart (i : M) p) := by
  classical
  dsimp only
  have hsource := B.weight_support i hp
  have htarget := (chart (i : M)).map_source hsource
  have hq (a : B.centers × Fin 3) : ContDiffAt ℝ ∞
      (fun y => if p ∈ tsupport (B.weight a.1) then B.coefficientFrameRead P i a y else 0)
      (chart (i : M) p) := by
    by_cases ha : p ∈ tsupport (B.weight a.1)
    · simp only [ite_eq_left ha]
      exact B.coefficientFrameRead_smoothAt P i a hsource (B.weight_support a.1 ha) (hQ a p ha)
    · simpa only [ite_eq_right ha] using (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : JetPolynomial.Base => (0 : TensorFiber →L[ℝ] ℝ)) (chart (i : M) p))
  have hw (a : B.centers × Fin 3) : ContDiffAt ℝ ∞
      (psi a ∘ (chart (i : M)).symm) (chart (i : M) p) :=
    ((hpsi a).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn.contDiffAt
      ((chart (i : M)).open_target.mem_nhds htarget)
  have hv (a : B.centers × Fin 3) : ContDiffAt ℝ ∞
      (fun y => if p ∈ tsupport (B.weight a.1) then B.phaseCovectorRead i (phi a) y else 0)
      (chart (i : M) p) := by
    by_cases ha : p ∈ tsupport (B.weight a.1)
    · simp only [ite_eq_left ha]
      exact (B.phaseCovectorRead_smoothOn i (phi a) (hphi a)).contDiffAt
        ((chart (i : M)).open_target.mem_nhds htarget)
    · simpa only [ite_eq_right ha] using (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : JetPolynomial.Base => (0 : Plane →L[ℝ] ℝ)) (chart (i : M) p))
  have hH := (B.tensorFrameRead_smoothOn i u hu).contDiffAt
    ((chart (i : M)).open_target.mem_nhds htarget)
  exact (((contDiffAt_pi.mpr hq).prodMk (contDiffAt_pi.mpr hw)).prodMk
    (contDiffAt_pi.mpr hv)).prodMk hH

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
local instance coordDerivFiberT2_rf1d185_1 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2_rf1d185_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2_rf1d185_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorSpace
local instance coordDerivFiberT2_rf1d185_2 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2_rf1d185_2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2_rf1d185_2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance coordDerivDualAdd_rf1d185_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSmul
variable (B : SmoothingAtlas M)

local instance coordDerivSectionNormed_rf1d185_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordDerivSectionSpace_rf1d185_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance coordDerivDataNormed_rf1d185_1 : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coordDerivDataSpace
local instance coordDerivDataT2_rf1d185_1 : T2Space (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
local instance coordDerivDataDualNormed_rf1d185_1 : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3) →L[ℝ] ℝ) := inferInstance
local instance coordDerivDataDualSpace_rf1d185_1 : NormedSpace ℝ (PrimitiveAmplitudeData (B.centers × Fin 3) →L[ℝ] ℝ) := inferInstance
theorem correctedAmplitude_coordinate_bound_oai
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hQ : ∀ (a : B.centers × Fin 3) (p : M), p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (hs : ∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (i : B.centers) {p : M} (hp : p ∈ tsupport (B.weight i))
    (a : B.centers × Fin 3) (ha : p ∈ tsupport (B.weight a.1))
    (R D : ℝ)
    (hdata : ‖fderiv ℝ (B.primitiveCoordinateData P psi phi u i
      {b | p ∈ tsupport (B.weight b.1)}) (chart (i : M) p)‖ ≤ D)
    (hparam : let z : PrimitiveAmplitudeData (B.centers × Fin 3) :=
        B.primitiveCoordinateData P psi phi u i {b | p ∈ tsupport (B.weight b.1)} (chart (i : M) p);
      (primitiveDataOperator z.1).IsInvertible ∧ 0 < primitiveParameterCoefficient a z ∧
        |primitiveParameterAmplitude a z| ≤ R ∧
        ‖fderiv ℝ (primitiveParameterAmplitude a) z‖ ≤ R) :
    |B.correctedPrimitiveAmplitude P psi phi u a p| ≤ R ∧
      ‖fderiv ℝ (B.correctedPrimitiveAmplitude P psi phi u a ∘ (chart (i : M)).symm)
        (chart (i : M) p)‖ ≤ R*D := by
  let F := B.primitiveCoordinateData P psi phi u i {b | p ∈ tsupport (B.weight b.1)}
  have hg := B.primitiveCoordinateData_germ P psi phi hphi hs u i (B.weight_support i hp) a ha
  have hv := hg.self_of_nhds
  simp only [Function.comp_apply,(chart (i : M)).left_inv (B.weight_support i hp)] at hv
  refine ⟨hv ▸ hparam.2.2.1,?_⟩
  have he := hg.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (primitiveParameterAmplitude a ∘ F) (chart (i : M) p) = _ at he
  rw [← he]
  exact primitive_amplitude_chain_bound a F (chart (i : M) p)
    (B.primitiveCoordinateData_smoothAt P psi phi hpsi hphi hQ u hu i hp)
    hparam.1 hparam.2.1 hparam.2.2.2 hdata

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedAmplitude_coordinate_bound_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedAmplitude_coordinate_bound_oai.{u_1}
