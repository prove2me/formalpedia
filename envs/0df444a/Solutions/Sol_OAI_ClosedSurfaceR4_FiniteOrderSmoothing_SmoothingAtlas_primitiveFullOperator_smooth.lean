-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_smooth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:28.384795+00:00
-- url     : https://prove2.me/submissions/10fcb5cc-6004-4290-99f6-fe5a42db9748

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
local instance symmetryModelComplete_r8e710c_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r8e710c_2 : CompleteSpace TensorFiber := inferInstance
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

lemma tensorLocalize_flip (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p) :
    A.bundleLocalize A.tensorTriv i (fun p => tensorTranspose (u p)) =
      fun x => (A.bundleLocalize A.tensorTriv i u x).flip := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · unfold bundleLocalize localize
    rw [indicator_of_mem hx, indicator_of_mem hx,
      A.tensorComponent_flip i u ((chart (i : M)).map_target hx)]
    ext v w
    rfl
  · simp only [bundleLocalize, localize, indicator_of_notMem hx]
    rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasCorrectionLimit
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fixed-atlas correction bounds imply a smooth manifold limit
and convergence of the manifold differentials. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates
open ExactCorrection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- Every point is seen by at least one genuine partition weight. -/
lemma exists_weight_ne_zero (p : M) : ∃ i : A.centers, A.weight i p ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hp := A.partition p
  simp only [h,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hp
  norm_num at hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
local instance primitiveInverseFiberSpace_r8e710c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveInverseFiberComplete_r8e710c_1 : CompleteSpace TensorFiber := inferInstance
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorOperatorSmooth
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
local instance operatorSmoothFiberComplete_r8e710c_1 : CompleteSpace TensorFiber := inferInstance
private lemma completedPrimitiveOperator_rankOne {ι : Type*} [Fintype ι]
    (q : ι → TensorFiber →L[ℝ] ℝ) (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ)
    (B : TensorFiber) :
    completedPrimitiveOperator q psi xi B =
      (∑ a, ((psi a)^2 * q a (tensorSymmetrizer B)) • (xi a).smulRight (xi a)) +
        (B - tensorSymmetrizer B) := by
  rw [completedPrimitiveOperator_apply,finitePrimitiveOperator_apply]
  abel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothSectionNormed
local instance operatorSmoothSectionSpace_r8e710c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothSectionGroup
omit [CompactSpace M] [IsManifold planeModel ∞ M] in
private lemma smooth_clm_of_evaluation {F : M → TensorFiber →L[ℝ] TensorFiber} {p : M}
    (h : ∀ v, ContMDiffAt planeModel 𝓘(ℝ,TensorFiber) ∞ (fun x => F x v) p) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber) ∞ F p := by
  let d := Module.finrank ℝ TensorFiber
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : TensorFiber ≃L[ℝ] TensorFiber)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp F, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.contMDiffAt.comp p
    (contMDiffAt_pi_space.mpr fun i => h _)

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberSpace
local instance operatorSmoothFiberComplete_r8e710c_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothSectionNormed
local instance operatorSmoothSectionSpace_r8e710c_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothSectionGroup
omit [CompactSpace M] in
/-- Testing a field on smooth sections suffices for smoothness of the
endomorphism field. The atlas cutoffs provide the local constant frames. -/
theorem tensorOperator_smooth_of_apply
    (L : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hL : ∀ u : ∀ p : M, CovariantTwoTensor p,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (L p (u p)))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (L p)) := by
  intro p
  obtain ⟨i,hi⟩ := A.exists_weight_ne_zero p
  have hp := subset_tsupport _ hi
  have hpS := A.weight_support i hp
  let e := A.tensorTriv i
  let eL := e.continuousLinearMap (RingHom.id ℝ) e
  have he : p ∈ e.baseSet := A.tensorTriv_domain i hpS
  apply (eL.contMDiffAt_section_iff (show p ∈ eL.baseSet from ⟨he,he⟩)).mpr
  apply smooth_clm_of_evaluation
  intro v
  let u := A.bundleRestore A.tensorTriv i (fun _ => v)
  have hu := A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i
    (contDiff_const : ContDiff ℝ ∞ (fun _ : JetPolynomial.Base => v))
  have hLu := (A.bundleComponent_smooth_on A.tensorTriv A.tensorTriv_domain i (hL u hu)
    p hpS).contMDiffAt ((chart (i : M)).open_source.mem_nhds hpS)
  apply hLu.congr_of_eventuallyEq
  filter_upwards [houter i p hp, (chart (i : M)).open_source.mem_nhds hpS] with x hx hxS
  simp only [eL, Trivialization.continuousLinearMap_apply]
  change e.continuousLinearMapAt ℝ x (L x (e.symmL ℝ x v)) =
    e.continuousLinearMapAt ℝ x (L x (u x))
  congr 2
  change e.symmL ℝ x v = A.outer i x • e.symmL ℝ x v
  rw [hx,one_smul]

include A in
/-- Transposition and symmetrization are smooth operations on genuine tensor
sections, with no symmetry assumption on the input. -/
lemma tensorSymmetrizer_smooth (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (show CovariantTwoTensor p from tensorSymmetrizer (u p))) := by
  have ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (tensorTranspose (u p))) := by
    have henc := A.tensorEncode_smooth hu
    have hflip : ContDiff ℝ ∞ (fun y => A.tensorEncode (fun p => tensorTranspose (u p)) y) := by
      apply contDiff_pi.mpr
      intro i
      have h := (ContinuousLinearMap.flipₗᵢ ℝ Plane Plane ℝ).toContinuousLinearMap.contDiff.comp
        (contDiff_pi.mp henc i)
      simpa only [tensorEncode,A.tensorLocalize_flip,Function.comp_def] using! h
    simpa only [A.tensorDecode_encode] using A.tensorDecode_smooth hflip
  change ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
    (fun p => TotalSpace.mk' TensorFiber p ((1 / 2 : ℝ) • (u p + tensorTranspose (u p))))
  exact (hu.add_section ht).const_smul_section (a := (1 / 2 : ℝ))

omit [CompactSpace M] in
/-- The cutoff absorbs all coefficient chart boundaries. -/
lemma supportedPrimitiveCoefficient_smooth
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞
      (fun p => (psi a p)^2 * A.primitiveCoefficientField P a p (u p)) := by
  apply contMDiff_of_tsupport
  intro p hp
  have hp2 : p ∈ tsupport (fun x => (psi a x)^2) := tsupport_mul_subset_left hp
  have hps : p ∈ tsupport (psi a) := by
    apply (closure_mono (show Function.support (fun x => (psi a x)^2) ⊆
      Function.support (psi a) from ?_)) hp2
    intro x hx
    exact fun hz => hx (by simp [hz])
  have hpchart := hsupport a hps
  have hc := ((chart_smooth (a.1 : M)) p hpchart).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds hpchart)
  have hq := (hQ a p hps).contMDiffAt.comp p hc
  have hb := ((A.bundleComponent_smooth_on A.tensorTriv A.tensorTriv_domain a.1 hu) p hpchart).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds hpchart)
  have hf := (fiberToThree.contDiff (n := ∞)).contDiffAt.contMDiffAt.comp p hb
  exact ((hpsi a p).pow 2).mul (hq.clm_apply hf)

/-- Smoothness of the actual independent-cutoff correction operator follows
from the smooth input coefficients and phases. -/
theorem primitiveFullOperator_smooth_oai
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi phi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (A.primitiveFullOperator P psi phi p)) := by
  apply A.tensorOperator_smooth_of_apply _ houter
  intro u hu
  have hs := A.tensorSymmetrizer_smooth u hu
  have hfinite : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p
        (show CovariantTwoTensor p from
          ∑ a : A.centers × Fin 3, ((psi a p)^2 * A.primitiveCoefficientField P a p
            (tensorSymmetrizer (u p))) • (A.primitivePhaseCovector phi a p).smulRight
              (A.primitivePhaseCovector phi a p))) := by
    apply ContMDiff.sum_section
    intro a _
    exact (A.supportedPrimitiveCoefficient_smooth P psi hpsi hsupport hQ _ hs a).smul_section
      (A.phaseDifferentialSquare_smooth (phi a) (hphi a))
  have h := hfinite.add_section (hu.sub_section hs)
  have he (p : M) : A.primitiveFullOperator P psi phi p (u p) =
      (show CovariantTwoTensor p from ∑ a : A.centers × Fin 3,
        ((psi a p)^2 * A.primitiveCoefficientField P a p (tensorSymmetrizer (u p))) •
          (A.primitivePhaseCovector phi a p).smulRight (A.primitivePhaseCovector phi a p)) +
            (u p - (show CovariantTwoTensor p from tensorSymmetrizer (u p))) := by
    exact completedPrimitiveOperator_rankOne (fun a => A.primitiveCoefficientField P a p)
      (fun a => psi a p) (fun a => A.primitivePhaseCovector phi a p) (u p)
  simpa only [he,Pi.add_apply,Pi.sub_apply] using! h


end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_smooth_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_smooth_oai.{u_1}
