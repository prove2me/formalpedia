-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:27.084407+00:00
-- url     : https://prove2.me/submissions/1184e23d-ef12-4e97-af68-7aeba1164667

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveFullOperator_smooth

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorBundleInverse
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth pointwise inversion for the actual tensor bundle. This is the
local analytic operation used to correct a finite perturbed primitive sum. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inverseTensorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inverseTensorFiberSpace
local instance inverseTensorFiberComplete : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inverseTensorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inverseTensorDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inverseTensorSectionNormed
local instance inverseTensorSectionSpace_rf4c54e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
private lemma tensorEndomorphismCoordinates_smoothAt
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p : M)
    (hA : ContMDiffAt planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun x => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) x (A x)) p) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber) ∞
      (tensorEndomorphismCoordinates A p) p :=
  (contMDiffAt_hom_bundle
    (fun x => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) x (A x))).mp hA |>.2

private lemma tensorEndomorphismCoordinates_invertible
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p : M)
    (hinv : (A p).IsInvertible) : (tensorEndomorphismCoordinates A p p).IsInvertible := by
  unfold tensorEndomorphismCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' p)
    (FiberBundle.mem_baseSet_trivializationAt' p)]
  exact ContinuousLinearMap.isInvertible_equiv.comp
    (hinv.comp ContinuousLinearMap.isInvertible_equiv)

private lemma tensorEndomorphismCoordinates_inverse
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p : M) :
    (fun x => (tensorEndomorphismCoordinates A p x).inverse) =ᶠ[𝓝 p]
      tensorEndomorphismCoordinates (fun x => (A x).inverse) p := by
  filter_upwards [(trivializationAt TensorFiber (CovariantTwoTensor (M := M)) p).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' p)] with x hx
  unfold tensorEndomorphismCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hx hx,ContinuousLinearMap.inCoordinates_eq hx hx]
  simp only [ContinuousLinearMap.inverse_equiv_comp,ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm]
  rfl

private lemma tensorEndomorphismCoordinates_inverse_smoothAt
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p : M)
    (hA : ContMDiffAt planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun x => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) x (A x)) p)
    (hinv : (A p).IsInvertible) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber) ∞
      (tensorEndomorphismCoordinates (fun x => (A x).inverse) p) p := by
  have hc := tensorEndomorphismCoordinates_smoothAt A p hA
  have hi := tensorEndomorphismCoordinates_invertible A p hinv
  exact (hi.contDiffAt_map_inverse.contMDiffAt.comp p hc).congr_of_eventuallyEq
    (tensorEndomorphismCoordinates_inverse A p).symm

/-- A smooth invertible field of tensor endomorphisms sends a smooth target
section to a smooth inverse section. No global trivialization is chosen. -/
theorem tensorBundle_inverse_apply_smooth
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p)
    (hA : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (A p)))
    (hinv : ∀ p, (A p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p ((A p).inverse (u p))) := by
  intro p
  have hc := tensorEndomorphismCoordinates_inverse_smoothAt A p (hA p) (hinv p)
  exact ContMDiffAt.clm_apply_of_inCoordinates (b₁ := id) (b₂ := id)
    (ϕ := fun x => (A x).inverse) (v := u) hc (hu p) contMDiffAt_id

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
local instance atlasOperatorFiberComplete_rf4c54e_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberSpace
local instance atlasOperatorFiberComplete_rf4c54e_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionNormed
local instance atlasOperatorSectionSpace_rf4c54e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionGroup
/-- Smoothness is the ordinary smooth inverse theorem on the tensor bundle. -/
theorem correctedPrimitiveTensor_smooth
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (hoperator : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (A.primitiveFullOperator P psi phi p)))
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.correctedPrimitiveTensor P psi phi u p)) :=
  tensorBundle_inverse_apply_smooth _ hoperator hinv u hu

lemma correctedPrimitiveAmplitude_smooth
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (hoperator : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (A.primitiveFullOperator P psi phi p)))
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.correctedPrimitiveAmplitude P psi phi u a) := by
  have hu' := A.correctedPrimitiveTensor_smooth P psi phi hoperator hinv u hu
  apply contMDiff_of_tsupport
  intro p hp
  have hps : p ∈ tsupport (psi a) := tsupport_mul_subset_left hp
  have hpchart := hsupport a hps
  have hc := ((chart_smooth (a.1 : M)) p hpchart).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds hpchart)
  have hq := (hQ a p hps).contMDiffAt.comp p hc
  have hb := ((A.bundleComponent_smooth_on A.tensorTriv A.tensorTriv_domain a.1 hu') p hpchart).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds hpchart)
  have hf := (fiberToThree.contDiff (n := ∞)).contDiffAt.contMDiffAt.comp p hb
  have he := hq.clm_apply hf
  have hr := (Real.contDiffAt_sqrt (hpos a p hps).ne').contMDiffAt.comp p he
  exact (hpsi a p).mul hr

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorOperatorSmooth
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual finite primitive operator, derived from its
supported coefficients and the smooth phase differentials. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberSpace
local instance operatorSmoothFiberComplete_rf4c54e_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberSpace
local instance operatorSmoothFiberComplete_rf4c54e_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualSmul
variable (A : SmoothingAtlas M)


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothSectionNormed
local instance operatorSmoothSectionSpace_rf4c54e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothSectionGroup
/-- The corrected amplitudes are smooth from their genuine coefficient,
cutoff and phase data; no operator-smoothness hypothesis remains. -/
theorem correctedPrimitiveAmplitude_smooth_of_data_oai
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi phi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.correctedPrimitiveAmplitude P psi phi u a) :=
  A.correctedPrimitiveAmplitude_smooth P psi phi hpsi hsupport hQ
    (A.primitiveFullOperator_smooth P psi phi hpsi hphi hsupport hQ houter) hinv u hu hpos a

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data_oai.{u_1}
