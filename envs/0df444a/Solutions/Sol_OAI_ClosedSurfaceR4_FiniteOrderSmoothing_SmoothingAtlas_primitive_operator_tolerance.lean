-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:37:13.458381+00:00
-- url     : https://prove2.me/submissions/1da17726-fb72-4e88-994a-70cfccfb536c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveFullOperator_frame

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
local instance primitiveInverseFiberSpace_r6f1dfc_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveInverseFiberComplete_r6f1dfc_1 : CompleteSpace TensorFiber := inferInstance
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
local instance dataFiberComplete_r6f1dfc_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd
local instance dataDualSmul_r6f1dfc_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FinitePrimitiveOperatorTolerance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform operator tolerance on bounded finite coefficient data. -/
noncomputable section
open Set
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorToleranceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorToleranceFiberSpace
theorem finite_primitive_operator_tolerance (D : ℝ) {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ z z' : PrimitiveOperatorData ι, ‖z‖ ≤ D → ‖z'-z‖ < eps →
        ‖primitiveDataOperator z'-primitiveDataOperator z‖ < eta := by
  have hc := (isCompact_closedBall (0 : PrimitiveOperatorData ι) (D+1)).uniformContinuousOn_of_continuous
    primitiveDataOperator_smooth.continuous.continuousOn
  obtain ⟨eps,heps,hnear⟩ := Metric.uniformContinuousOn_iff.mp hc eta heta
  refine ⟨min eps 1,lt_min heps zero_lt_one,min_le_right _ _,?_⟩
  intro z z' hz hdist
  have hzK : z ∈ Metric.closedBall 0 (D+1) := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    linarith
  have hzK' : z' ∈ Metric.closedBall 0 (D+1) := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    have hh : ‖z'-z‖ < 1 := hdist.trans_le (min_le_right _ _)
    calc
      ‖z'‖ ≤ ‖z'-z‖+‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ D+1 := by linarith
  simpa only [dist_eq_norm] using hnear z' hzK' z hzK
    (by simpa only [dist_eq_norm] using hdist.trans_le (min_le_left _ _))

end ClosedSurfaceR4.FiniteOrderSmoothing

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
local instance frameAlgebraSectionSpace_r6f1dfc_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance frameBoundSectionNormed_r6f1dfc_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameBoundSectionSpace_r6f1dfc_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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

omit [T2Space M] in
 theorem coefficientFrame_bound
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (hQ : ∀ (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i a p,
      p ∈ tsupport (B.weight i) → p ∈ tsupport (B.weight a.1) →
      ‖B.coefficientFrame P i a p‖ ≤ D := by
  have hbound (i : B.centers) (a : B.centers × Fin 3) :
      ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ tsupport (B.weight i) ∩ tsupport (B.weight a.1),
        ‖B.coefficientFrame P i a p‖ ≤ D := by
    let K := tsupport (B.weight i) ∩ tsupport (B.weight a.1)
    have hc : ContinuousOn (B.coefficientFrame P i a) K := by
      intro p hp
      have hi := B.weight_support i hp.1
      have ha := B.weight_support a.1 hp.2
      have hq := (hQ a p hp.2).contMDiffAt.comp p
        ((chart_smooth (a.1 : M) p ha).contMDiffAt ((chart (a.1 : M)).open_source.mem_nhds ha))
      have hT := (contMDiffOn_coordChangeL (IB := planeModel) (n := ∞) (B.tensorTriv i) (B.tensorTriv a.1)).contMDiffAt
        ((B.tensorTriv i).open_baseSet.inter (B.tensorTriv a.1).open_baseSet |>.mem_nhds
          ⟨B.tensorTriv_domain i hi,B.tensorTriv_domain a.1 ha⟩)
      have hconst : ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] PhaseMean.Tensor) ∞
          (fun _ : M => fiberToThree) p := contMDiffAt_const
      have hs : ContinuousWithinAt (fun q =>
          ((P a.1 (chart (a.1 : M) q)).Q a.2).comp (fiberToThree.comp
            ((B.tensorTriv i).coordChangeL ℝ (B.tensorTriv a.1) q : TensorFiber →L[ℝ] TensorFiber))) K p :=
        (hq.clm_comp (hconst.clm_comp hT)).continuousAt.continuousWithinAt
      apply hs.congr
      · intro q hq
        exact (B.coefficientFrame_coordChange P i a (B.weight_support i hq.1)
          (B.weight_support a.1 hq.2))
      · exact (B.coefficientFrame_coordChange P i a hi ha)
    obtain ⟨D,hD⟩ := ((isClosed_tsupport (B.weight i)).inter
      (isClosed_tsupport (B.weight a.1))).isCompact.exists_bound_of_continuousOn hc
    exact ⟨max 1 D,le_max_left _ _,fun p hp => (hD p hp).trans (le_max_right _ _)⟩
  choose D hD hb using fun k : B.centers × (B.centers × Fin 3) => hbound k.1 k.2
  refine ⟨1+∑ k, D k,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.univ) (fun k _ => (zero_le_one.trans (hD k)))
    linarith
  · intro i a p hi ha
    exact (hb (i,a) p ⟨hi,ha⟩).trans (by
      have := Finset.single_le_sum (fun k _ => zero_le_one.trans (hD k)) (Finset.mem_univ (i,a))
      linarith)

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
local instance maskFiberSpace_r6f1dfc_1 : NormedSpace ℝ TensorFiber := inferInstance
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ActualOperatorTolerance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent cutoff and phase perturbations give uniform control of
the actual operator in every chart of the fixed primitive atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualToleranceFiberSpace
local instance actualToleranceDualAdd_r6f1dfc_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualToleranceDualSmul_r6f1dfc_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualToleranceFiberNormed
local instance actualToleranceSectionNormed_r6f1dfc_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualToleranceSectionSpace_r6f1dfc_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem primitive_operator_tolerance_oai
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (hQ : ∀ (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (phi₀ : (B.centers × Fin 3) → M → ℝ)
    (hphi₀ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi₀ a))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ psi phi : (B.centers × Fin 3) → M → ℝ,
      (∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1)) →
      (∀ a p, |psi a p-B.weight a.1 p| < eps) →
      (∀ (i : B.centers) (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight i) → p ∈ tsupport (B.weight a.1) →
        ‖B.covectorFrame i p (B.primitivePhaseCovector phi a p)-
          B.covectorFrame i p (B.primitivePhaseCovector phi₀ a p)‖ < eps) →
      ∀ i p, p ∈ tsupport (B.weight i) →
        ‖B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p)-
          B.tensorOperatorFrame i p
            (B.primitiveFullOperator P (fun a => B.weight a.1) phi₀ p)‖ < eta := by
  classical
  obtain ⟨Dq,hDq,hq⟩ := B.coefficientFrame_bound P hQ
  choose Dv hDv hv using fun a => B.covectorFrame_bound (phi₀ a) (hphi₀ a)
  let D : ℝ := Dq+1+∑ a, Dv a
  have hDqD : Dq ≤ D := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun a _ => zero_le_one.trans (hDv a)); dsimp only [D] <;> linarith
  have hD1 : 1 ≤ D := by linarith
  have hDvD (a : B.centers × Fin 3) : Dv a ≤ D := by
    have := Finset.single_le_sum (fun a _ => zero_le_one.trans (hDv a)) (Finset.mem_univ a)
    dsimp only [D] <;> linarith
  obtain ⟨eps,heps,_,hnear⟩ := finite_primitive_operator_tolerance (ι := B.centers × Fin 3) D heta
  refine ⟨eps,heps,?_⟩
  intro psi phi hs hw hd i p hp
  let S : Set (B.centers × Fin 3) := {a | p ∈ tsupport (B.weight a.1)}
  let q := fun a => if a ∈ S then B.coefficientFrame P i a p else 0
  let v₀ := fun a => B.covectorFrame i p (B.primitivePhaseCovector phi₀ a p)
  let v := fun a => if a ∈ S then B.covectorFrame i p (B.primitivePhaseCovector phi a p) else v₀ a
  let z₀ : PrimitiveOperatorData (B.centers × Fin 3) := ((q,fun a => B.weight a.1 p),v₀)
  let z : PrimitiveOperatorData (B.centers × Fin 3) := ((q,fun a => psi a p),v)
  have hqD : ‖q‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hD1)).mpr
    intro a
    dsimp [q]
    split_ifs with ha
    · exact (hq i a p hp ha).trans hDqD
    · simpa only [norm_zero] using zero_le_one.trans hD1
  have hwD : ‖fun a : B.centers × Fin 3 => B.weight a.1 p‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hD1)).mpr
    intro a
    have hh := Finset.single_le_sum (fun b _ => sq_nonneg (B.weight b p)) (Finset.mem_univ a.1)
    rw [B.partition p] at hh
    have hh' : |B.weight a.1 p| ≤ 1 := by nlinarith [sq_abs (B.weight a.1 p),abs_nonneg (B.weight a.1 p)]
    exact (show ‖B.weight a.1 p‖ ≤ 1 by simpa only [Real.norm_eq_abs] using hh').trans hD1
  have hvD : ‖v₀‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hD1)).mpr
    intro a
    exact (hv a i p hp).trans (hDvD a)
  have hz₀ : ‖z₀‖ ≤ D := by
    exact max_le (max_le hqD hwD) hvD
  have hdist : ‖z-z₀‖ < eps := by
    change max (max ‖q-q‖ ‖(fun a => psi a p)-(fun a => B.weight a.1 p)‖) ‖v-v₀‖ < eps
    rw [sub_self,norm_zero]
    apply max_lt
    · apply max_lt heps
      apply (pi_norm_lt_iff heps).mpr
      intro a
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using hw a p
    · apply (pi_norm_lt_iff heps).mpr
      intro a
      dsimp [v]
      split_ifs with ha
      · exact hd i a p hp ha
      · simpa only [sub_self,norm_zero] using heps
  have hz := hnear z₀ z hz₀ hdist
  have hzero (a : B.centers × Fin 3) (ha : a ∉ S) : psi a p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => ha (hs a hh))
  have hzero₀ (a : B.centers × Fin 3) (ha : a ∉ S) : B.weight a.1 p = 0 :=
    image_eq_zero_of_notMem_tsupport ha
  rw [B.primitiveFullOperator_frame P psi phi i (B.weight_support i hp),
    B.primitiveFullOperator_frame P (fun a => B.weight a.1) phi₀ i (B.weight_support i hp)]
  rw [completedPrimitiveOperator_mask _ _ _ v₀ S hzero,
    completedPrimitiveOperator_mask _ _ _ v₀ S hzero₀]
  simpa only [primitiveDataOperator,z,z₀,v₀,v,q,ite_self] using hz

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance_oai.{u_1}
