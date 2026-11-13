-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_frame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:36:48.688139+00:00
-- url     : https://prove2.me/submissions/c490f57e-681f-444c-8b49-013916db5bbb

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011

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
local instance primitiveInverseFiberSpace_r6438cc_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveInverseFiberComplete_r6438cc_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseFiberGroup
lemma tensorSymmetrizer_apply (B : TensorFiber) (v w : Plane) :
    tensorSymmetrizer B v w = (B v w+B w v)/2 := by
  change (1/2 : ℝ)*(B v w+B w v) = (B v w+B w v)/2
  ring

variable {ι : Type*} [Fintype ι]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorConjugation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation of the finite primitive operator by tensor coordinates. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.conjugateFiberNormed
local instance conjugateFiberSpace_r6438cc_1 : NormedSpace ℝ TensorFiber := inferInstance
lemma completedPrimitiveOperator_conjugate (e f : TensorFiber →L[ℝ] TensorFiber)
    (q : ι → TensorFiber →L[ℝ] ℝ) (w : ι → ℝ)
    (v v' : ι → Plane →L[ℝ] ℝ)
    (hef : ∀ H, e (f H) = H)
    (hf : ∀ H, tensorSymmetrizer (f H) = f (tensorSymmetrizer H))
    (hv : ∀ a, e ((v a).smulRight (v a)) = (v' a).smulRight (v' a)) :
    e.comp ((completedPrimitiveOperator q w v).comp f) =
      completedPrimitiveOperator (fun a => (q a).comp f) w v' := by
  apply ContinuousLinearMap.ext
  intro H
  simp only [ContinuousLinearMap.comp_apply,completedPrimitiveOperator_apply,
    finitePrimitiveOperator_apply,map_sub,map_add,map_sum,map_smul,hf,hef,hv]

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
local instance frameAlgebraSectionSpace_r6438cc_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraSectionGroup
lemma tensor_frame_symmetrizer (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (H : TensorFiber) :
    (B.tensorTriv i).continuousLinearMapAt ℝ p (tensorSymmetrizer H) =
      tensorSymmetrizer ((B.tensorTriv i).continuousLinearMapAt ℝ p H) := by
  change B.bundleComponent B.tensorTriv i (fun _ => (show TensorFiber from tensorSymmetrizer H)) p =
    tensorSymmetrizer (B.bundleComponent B.tensorTriv i (fun _ => (show TensorFiber from H)) p)
  ext v w
  erw [B.tensorComponent_apply i _ hp,tensorSymmetrizer_apply,tensorSymmetrizer_apply,
    B.tensorComponent_apply i _ hp,B.tensorComponent_apply i _ hp]
  rfl

lemma tensor_inverse_frame_symmetrizer (i : B.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) (H : TensorFiber) :
    tensorSymmetrizer ((B.tensorTriv i).symmL ℝ p H) =
      (B.tensorTriv i).symmL ℝ p (tensorSymmetrizer H) := by
  have hd := B.tensorTriv_domain i hp
  have h := B.tensor_frame_symmetrizer i hp ((B.tensorTriv i).symmL ℝ p H)
  erw [(B.tensorTriv i).continuousLinearMapAt_symmL hd] at h
  have hh := congrArg ((B.tensorTriv i).symmL ℝ p) h
  erw [(B.tensorTriv i).symmL_continuousLinearMapAt hd] at hh
  exact hh

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

lemma primitiveFullOperator_frame_oai
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source) :
    B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p) =
      completedPrimitiveOperator (fun a => B.coefficientFrame P i a p)
        (fun a => psi a p) (fun a => B.covectorFrame i p (B.primitivePhaseCovector phi a p)) := by
  let e : TensorFiber →L[ℝ] TensorFiber := (B.tensorTriv i).continuousLinearMapAt ℝ p
  let f : TensorFiber →L[ℝ] TensorFiber := (B.tensorTriv i).symmL ℝ p
  have hef (H : TensorFiber) : e (f H) = H :=
    (B.tensorTriv i).continuousLinearMapAt_symmL (B.tensorTriv_domain i hp) H
  have hf (H : TensorFiber) : tensorSymmetrizer (f H) = f (tensorSymmetrizer H) :=
    B.tensor_inverse_frame_symmetrizer i hp H
  have hv (a : B.centers × Fin 3) :
      e ((B.primitivePhaseCovector phi a p).smulRight (B.primitivePhaseCovector phi a p)) =
        (B.covectorFrame i p (B.primitivePhaseCovector phi a p)).smulRight
          (B.covectorFrame i p (B.primitivePhaseCovector phi a p)) :=
    B.tensor_frame_square i hp _
  exact completedPrimitiveOperator_conjugate e f
    (fun a => B.primitiveCoefficientField P a p) (fun a => psi a p)
    (fun a => B.primitivePhaseCovector phi a p) _ hef hf hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_frame_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_frame_oai.{u_1}
