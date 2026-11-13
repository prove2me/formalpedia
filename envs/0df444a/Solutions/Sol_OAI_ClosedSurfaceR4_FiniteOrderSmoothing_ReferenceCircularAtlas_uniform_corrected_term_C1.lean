-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:14.726192+00:00
-- url     : https://prove2.me/submissions/b6f7ed4e-9d25-4b26-819c-3a88dd68074f

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
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_uniform_actual_amplitude_C1
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_cubic_remainder_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitive_term_background_C1_bound

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

end ClosedSurfaceR4.WeightedEstimates

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_smul (p : M) (ψ : M → ℝ) (a : ℝ) (f : M → V) :
    localize p ψ (a • f) = a • localize p ψ f := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_smul, mul_comm]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and elementary norm operations for actual global metric tensors. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualSmul
variable (A : SmoothingAtlas M)
include A

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberSpace
local instance metricBoundSectionNormed_rdb3aff_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_rdb3aff_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_add {T S : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hS : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (S p)))
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbT : A.TensorWeightedBound s m C T) (hbS : A.TensorWeightedBound s m D S) :
    A.TensorWeightedBound s m (C+D) (T+S) := by
  intro i
  change WeightedEstimates.WeightedBound univ s m (C+D) (A.bundleLocalize A.tensorTriv i (T+S))
  rw [A.bundleLocalize_add]
  exact (hbT i).add uniqueDiffOn_univ hs
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT).contDiffOn
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hS).contDiffOn (hbS i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasTensorTransition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tensor transitions between independent smoothing atlases. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
open PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberSpace
local instance crossTransitionDualSmul_rdb3aff_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

variable [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberNormed
local instance crossTransitionSectionNormed_rdb3aff_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTransitionSectionSpace_rdb3aff_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma cross_pairSupport_compact (i : A.centers) (j : B.centers) :
    IsCompact (A.cross_pairSupport B i j) :=
  ((isClosed_tsupport (A.weight i)).inter (isClosed_tsupport (B.outer j))).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (fun _ hx => A.weight_support i hx.1))

omit [CompactSpace M] in
lemma cross_pairSupport_transition (i : A.centers) (j : B.centers) :
    A.cross_pairSupport B i j ⊆ (transition (i : M) (j : M)).source := by
  rintro x ⟨p,⟨hp,hq⟩,rfl⟩
  have hp' := A.weight_support i hp
  refine ⟨(chart (i : M)).map_source hp',?_⟩
  change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
  rw [(chart (i : M)).left_inv hp']
  exact B.outer_support j hq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasTensorBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tensor bounds persist when the finite correction atlas changes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundDualSmul
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundFiberSpace
local instance crossTensorBoundSectionNormed_rdb3aff_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTensorBoundSectionSpace_rdb3aff_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma cross_tensor_localize_restore_bound (i : B.centers) (j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h →
      WeightedEstimates.WeightedBound univ s m C h →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (B.bundleLocalize B.tensorTriv i (A.bundleRestore A.tensorTriv j h)) := by
  let L : Base → TensorFiber →L[ℝ] TensorFiber := fun x =>
    (A.tensorTriv j).coordChangeL ℝ (B.tensorTriv i) ((chart (i : M)).symm x)
  have hL : ContDiffOn ℝ ∞ L (transition (i : M) (j : M)).source := by
    apply ContMDiffOn.contDiffOn
    apply (contMDiffOn_coordChangeL (A.tensorTriv j) (B.tensorTriv i)).comp
      ((chart_symm_smooth (i : M)).mono (fun _ hx => hx.1))
    intro x hx
    have hj : (chart (i : M)).symm x ∈ (chart (j : M)).source := hx.2
    exact ⟨A.tensorTriv_domain j hj,B.tensorTriv_domain i ((chart (i : M)).map_target hx.1)⟩
  have heq (h : Base → TensorFiber) :
      B.bundleLocalize B.tensorTriv i (A.bundleRestore A.tensorTriv j h) =
        fun x => localize (i : M) (B.weight i) (A.outer j) x •
          L x (h (transition (i : M) (j : M) x)) := by
    funext x
    by_cases hi : x ∈ (chart (i : M)).target
    · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
      · have hbi := B.tensorTriv_domain i ((chart (i : M)).map_target hi)
        have hbj := A.tensorTriv_domain j hj
        simp only [bundleLocalize,bundleComponent,localize,indicator_of_mem hi,
          bundleRestore,map_smul]
        rw [(B.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ hbi,
          (A.tensorTriv j).symmL_apply (R := ℝ) hbj,
          ← (A.tensorTriv j).coordChangeL_apply (R := ℝ) (B.tensorTriv i) ⟨hbj,hbi⟩,smul_smul]
        rfl
      · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hj (A.outer_support j hh))
        simp only [bundleLocalize,bundleComponent,localize,indicator_of_mem hi,
          bundleRestore,hz,zero_smul,map_zero,smul_zero]
    · simp only [bundleLocalize,localize,indicator_of_notMem hi,zero_smul]
  obtain ⟨D,hD,hd⟩ := compact_localized_clm_composition_bound
    (transition (i : M) (j : M)).open_source (B.cross_pairSupport_compact A i j)
    (B.cross_pairSupport_transition A i j)
    (localize_smooth (i : M) (B.weight_smooth i) (B.weight_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (B.weight_support i) (A.outer j))
    hL (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro h s C hs hs1 hC hh hb
  rw [heq]
  exact hd h s C hs hs1 hC hh hb

theorem tensorWeightedBound_change_atlas (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ p : M, CovariantTwoTensor p) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      A.TensorWeightedBound s m C u → B.TensorWeightedBound s m (D*C) u := by
  classical
  choose D hD hd using fun (i : B.centers) (j : A.centers) =>
    A.cross_tensor_localize_restore_bound B i j m
  refine ⟨∑ i : B.centers,∑ j : A.centers,D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)),?_⟩
  intro u s C hs hs1 hC hu hb i
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j*C)
    (fun j => B.bundleLocalize B.tensorTriv i
      (A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u)))
    (fun j _ => (B.bundleLocalize_smooth B.tensorTriv B.tensorTriv_domain i
      (A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain j
        (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain j hu))).contDiffOn)
    (fun j _ => hd i j _ s C hs hs1 hC
      (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain j hu) (hb j))
  have he : B.bundleLocalize B.tensorTriv i u = fun x => ∑ j : A.centers,
      B.bundleLocalize B.tensorTriv i
        (A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u)) x := by
    have hu' : u = (fun p => ∑ j : A.centers,
        A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u) p) :=
      (funext (A.bundle_sum_restore_localize A.tensorTriv A.tensorTriv_domain u)).symm
    conv_lhs => rw [hu']
    exact B.bundleLocalize_sum B.tensorTriv Finset.univ i _
  change WeightedEstimates.WeightedBound univ s m _ (B.bundleLocalize B.tensorTriv i u)
  rw [he]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasQuadraticResidual
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero-phase residual of the actual charted free family. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasSectionNormed
local instance quadraticAtlasSectionSpace_rdb3aff_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_const_smul
    {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ}
    (hb : A.TensorWeightedBound s m C u) (a : ℝ) :
    A.TensorWeightedBound s m (|a| * C) (a • u) := by
  intro i
  have hb' := (hb i).const_smul uniqueDiffOn_univ
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu).contDiffOn a
  change _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (|a| * C) (A.bundleLocalize A.tensorTriv i (a • u))
  rw [A.bundleLocalize_smul]
  exact hb'

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactParameterC1
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact C1 bounds for a smooth parameter family and its spatial slices. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {P X V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compact_parameter_C1 {A : Set P} {K : Set X} (hA : IsCompact A) (hK : IsCompact K)
    {F : P × X → V} (hF : ∀ z ∈ A ×ˢ K, ContDiffAt ℝ ∞ F z) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ a ∈ A, ∀ x ∈ K,
      ‖F (a,x)‖ ≤ D ∧ ‖fderiv ℝ (fun y => F (a,y)) x‖ ≤ D := by
  have hc : ContinuousOn (fun z => (F z,fderiv ℝ F z)) (A ×ˢ K) := by
    intro z hz
    exact ((hF z hz).continuousAt.prodMk ((hF z hz).continuousAt_fderiv (by simp))).continuousWithinAt
  obtain ⟨C,hC⟩ := (hA.prod hK).exists_bound_of_continuousOn hc
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro a ha x hx
  have hb := (hC (a,x) ⟨ha,hx⟩).trans (le_max_right 1 C)
  have hv := (norm_fst_le (F (a,x),fderiv ℝ F (a,x))).trans hb
  have hd := (norm_snd_le (F (a,x),fderiv ℝ F (a,x))).trans hb
  refine ⟨hv,?_⟩
  have hpair : HasFDerivAt (fun y : X => (a,y)) (ContinuousLinearMap.inr ℝ P X) x :=
    (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
  have he := ((hF (a,x) ⟨ha,hx⟩).differentiableAt (by simp)).hasFDerivAt.comp x hpair
  change ‖fderiv ℝ (F ∘ Prod.mk a) x‖ ≤ max 1 C
  rw [he.fderiv]
  calc
    _ ≤ ‖fderiv ℝ F (a,x)‖*‖ContinuousLinearMap.inr ℝ P X‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ F (a,x)‖*1 := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inr_le_one ℝ P X) (norm_nonneg _)
    _ ≤ max 1 C := by simpa only [mul_one] using hd

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

omit [CompactSpace M] [T2Space M] in
lemma circularCovectorJoint_smoothOn (i j : B.centers) (L : ℝ) :
    ContDiffOn ℝ ∞ (B.circularCovectorJoint i j L)
      (univ ×ˢ (chart (j : M)).target) := by
  have h0 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i 0 L)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have h1 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i (1,0) 0)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have h2 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i (0,1) 0)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have he1 : ContDiff ℝ ∞ (fun z : Base × JetPolynomial.Base => z.1.1) := contDiff_fst.fst
  have he2 : ContDiff ℝ ∞ (fun z : Base × JetPolynomial.Base => z.1.2) := contDiff_fst.snd
  exact (h0.add (he1.contDiffOn.smul h1)).add (he2.contDiffOn.smul h2)

omit [CompactSpace M] [T2Space M] in
lemma circularCovectorJoint_eq (i j : B.centers) (ell : Base) (L : ℝ)
    {y : JetPolynomial.Base} (hy : y ∈ (chart (j : M)).target) :
    B.phaseCovectorRead j (B.circularPhase i ell L) y = B.circularCovectorJoint i j L (ell,y) := by
  let p := (chart (j : M)).symm y
  have hp : p ∈ (chart (j : M)).source := (chart (j : M)).map_target hy
  have hpy : chart (j : M) p = y := (chart (j : M)).right_inv hy
  have h := B.circularPhase_mfderiv_sub i ell 0 L p
  have hh := congrArg (fun v : Plane →L[ℝ] ℝ => B.covectorFrame j p v) h
  unfold covectorFrame at hh
  erw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.smul_comp] at hh
  change B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
      B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i 0 L) p) =
    (ell.1-0) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)+
    (ell.2-0) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p) at hh
  rw [B.covectorFrame_mfderiv _ (B.circularPhase_smooth i ell L) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i 0 L) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i (1,0) 0) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i (0,1) 0) j hp,hpy] at hh
  change B.phaseCovectorRead j (B.circularPhase i ell L) y-
      B.phaseCovectorRead j (B.circularPhase i 0 L) y =
    (ell.1-0) • B.phaseCovectorRead j (B.circularPhase i (1,0) 0) y+
    (ell.2-0) • B.phaseCovectorRead j (B.circularPhase i (0,1) 0) y at hh
  simp only [sub_zero] at hh
  have hh' := congrArg (fun v => v+B.phaseCovectorRead j (B.circularPhase i 0 L) y) hh
  rw [sub_add_cancel] at hh'
  rw [hh']
  unfold circularCovectorJoint
  abel

omit [T2Space M] in
theorem circular_covector_parameter_bound (i j : B.centers) (L : ℝ)
    {P : Set Base} (hP : IsCompact P) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ ell ∈ P, ∀ y ∈ (B.chartWeightCompact j : Set JetPolynomial.Base),
      ‖B.phaseCovectorRead j (B.circularPhase i ell L) y‖ ≤ D ∧
      ‖fderiv ℝ (B.phaseCovectorRead j (B.circularPhase i ell L)) y‖ ≤ D := by
  have hK := (B.chartWeightCompact j).isCompact
  have hsub : (B.chartWeightCompact j : Set JetPolynomial.Base) ⊆ (chart (j : M)).target := by
    rintro y ⟨p,hp,rfl⟩
    exact (chart (j : M)).map_source (B.weight_support j hp)
  have hj := B.circularCovectorJoint_smoothOn i j L
  obtain ⟨D,hD,hbound⟩ := compact_parameter_C1 hP hK
    (fun z hz => hj.contDiffAt ((isOpen_univ.prod (chart (j : M)).open_target).mem_nhds
      ⟨mem_univ _,hsub hz.2⟩))
  refine ⟨D,hD,?_⟩
  intro ell hell y hy
  have he : B.phaseCovectorRead j (B.circularPhase i ell L) =ᶠ[𝓝 y]
      (fun x => B.circularCovectorJoint i j L (ell,x)) := by
    filter_upwards [(chart (j : M)).open_target.mem_nhds (hsub hy)] with x hx
    exact B.circularCovectorJoint_eq i j ell L hx
  rw [he.self_of_nhds,he.fderiv_eq]
  exact hbound ell hell y hy

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InitialInputBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite initial input estimates for the scalar-contracted map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance initialBoundFiberNormed_rdb3aff_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_rdb3aff_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd_rdb3aff_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_rdb3aff_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialBoundSectionNormed_rdb3aff_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_rdb3aff_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma space_smul_contMDiff {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    ContMDiff planeModel spaceModel ∞ (a • F) :=
  (a • ContinuousLinearMap.id ℝ Space).contDiff.contMDiff.comp hF

namespace SmoothingAtlas
local instance initialBoundFiberNormed_rdb3aff_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_rdb3aff_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd_rdb3aff_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_rdb3aff_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance initialBoundSectionNormed_rdb3aff_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_rdb3aff_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma weightedBound_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C : ℝ} {m : ℕ}
    (hb : A.WeightedBound s m C F) (a : ℝ) :
    A.WeightedBound s m (|a| * C) (a • F) := by
  intro i
  rw [localize_smul]
  exact (hb i).const_smul uniqueDiffOn_univ
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn a

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformMetricPathBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-order metric bounds fixed before finite spherical modifications. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberSpace
local instance pathBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberSpace
local instance pathBoundSectionNormed_rdb3aff_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance pathBoundSectionSpace_rdb3aff_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma exists_tensorWeighted_bound (m : ℕ) {T : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p))) :
    ∃ C : ℝ, 0 ≤ C ∧ A.TensorWeightedBound 1 m C T := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT)
    (localize_compact (i : M) (A.weight_support i) (A.bundleComponent A.tensorTriv i T)) m
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun i => ?_⟩
  exact (hb i).mono_const (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

lemma uniform_induced_tensor_bound {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F : M → Space, ContMDiff planeModel spaceModel ∞ F →
      A.WeightedBound 1 (m+1) C F → A.TensorWeightedBound 1 m D (inducedTensor F) := by
  obtain ⟨D,hD,hbound⟩ := A.global_cubic_remainder_bound m 0 C le_rfl hC
  refine ⟨D,hD,fun F hF hb => ?_⟩
  have hz : A.WeightedBound 1 (m+1) (0*(1*1)) (0 : M → Space) := by
    intro i
    simp only [zero_mul]
    change WeightedEstimates.WeightedBound univ 1 (m+1) 0 (localize (i : M) (A.weight i) 0)
    have he : localize (i : M) (A.weight i) (0 : M → Space) = 0 := by
      funext x
      by_cases hx : x ∈ (chart (i : M)).target <;> simp [localize,hx]
    rw [he]
    exact weightedBound_zero univ 1 (m+1)
  have ht := hbound 1 1 zero_lt_one le_rfl zero_le_one le_rfl 0 F
    contMDiff_const hF hz (by simpa only [one_pow,mul_one] using hb)
  have he : linearMetricTensor (0 : M → Space) F = 0 := by
    funext p
    ext v w
    change inner ℝ (show Space from mfderiv planeModel spaceModel (0 : M → Space) p v)
        (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        (show Space from mfderiv planeModel spaceModel (0 : M → Space) p w) = 0
    have hd : (mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p :
        TangentSpace planeModel p →L[ℝ] Space) = 0 := mfderiv_const
    change inner ℝ ((mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p) v)
        (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        ((mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p) w) = 0
    rw [hd]
    change inner ℝ (0 : Space) (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (0 : Space) = 0
    rw [inner_zero_left,inner_zero_right,add_zero]
  simpa only [he,zero_add,one_pow,div_one,mul_one] using ht

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ReferencePhaseC1
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed first-jet budget for every phase in the reference parameter balls. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem perturbed_phase_C1_bound : ∃ D : ℝ, 1 ≤ D ∧
    ∀ ell : d.B.centers → Fin 3 → SmallModes.Base,
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ ≤ 1) →
      ∀ (i : d.B.centers) (a : d.B.centers × Fin 3) p,
      p ∈ tsupport (d.B.weight i) →
        ‖d.B.phaseCovectorRead i (d.perturbedPhases ell a) (chart (i : M) p)‖ ≤ D ∧
        ‖fderiv ℝ (d.B.phaseCovectorRead i (d.perturbedPhases ell a)) (chart (i : M) p)‖ ≤ D := by
  classical
  choose D hD hbound using fun k : d.B.centers × (d.B.centers × Fin 3) =>
    d.B.circular_covector_parameter_bound k.2.1 k.1 (d.L k.2.1)
      (isCompact_closedBall ((d.P k.2.1).ξ k.2.2) 1)
  let E := 1+∑ k, D k
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun k _ => zero_le_one.trans (hD k))
  refine ⟨E,by dsimp only [E] <;> linarith,?_⟩
  intro ell hell i a p hp
  have he : ell a.1 a.2 ∈ Metric.closedBall ((d.P a.1).ξ a.2) 1 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hell a.1 a.2
  have h := hbound (i,a) (ell a.1 a.2) he (chart (i : M) p) ⟨p,hp,rfl⟩
  have hle : D (i,a) ≤ E := by
    have hh := Finset.single_le_sum (fun k _ => zero_le_one.trans (hD k)) (Finset.mem_univ (i,a))
    dsimp only [E] <;> linarith
  exact ⟨h.1.trans hle,h.2.trans hle⟩

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformRemainderBound
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed C2 budget for starting maps gives one C1 remainder bound in
any fixed primitive atlas, before choosing finite modifications. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance remainderBoundFiberNormed_rdb3aff_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance remainderBoundFiberSpace_rdb3aff_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance remainderBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
local instance remainderBoundFiberNormed_rdb3aff_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance remainderBoundFiberSpace_rdb3aff_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance remainderBoundDualSmul_rdb3aff_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.remainderBoundSectionNormed
local instance remainderBoundSectionSpace_rdb3aff_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_remainder_C1_bound (g : SmoothMetric M) (r : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 2 D G → B.TensorWeightedBound 1 1 U (g.inner-inducedTensor (r • G)) := by
  obtain ⟨U,hU,hinduced⟩ := A.uniform_induced_tensor_bound (mul_nonneg (abs_nonneg r) hD) 1
  obtain ⟨E,hE,hmetric⟩ := A.exists_tensorWeighted_bound 1 g.contMDiff
  obtain ⟨T,hT,hchange⟩ := A.tensorWeightedBound_change_atlas B 1
  refine ⟨T*(E+U),mul_nonneg hT (add_nonneg hE hU),?_⟩
  intro G hG hbound
  have hscaled := space_smul_contMDiff hG r
  have hmap := A.weightedBound_const_smul hG hbound r
  have hi := hinduced (r • G) hscaled hmap
  have hsmooth := A.inducedTensor_smooth hscaled
  have hneg : A.TensorWeightedBound 1 1 U (-inducedTensor (r • G)) := by
    simpa only [neg_one_smul,abs_neg,abs_one,one_mul] using
      A.tensorWeightedBound_const_smul hsmooth hi (-1)
  have hsum := A.tensorWeightedBound_add g.contMDiff hsmooth.neg_section zero_le_one hmetric hneg
  apply hchange (g.inner-inducedTensor (r • G)) 1 (E+U) zero_lt_one le_rfl
    (add_nonneg hE hU) (g.contMDiff.sub_section hsmooth)
  simpa only [sub_eq_add_neg] using hsum

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformCorrectedTermC1
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform background C1 bound for every actual corrected primitive term.
The bound is chosen before the cycle count and before the finite-point map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance uniformTermFiberNormed_rdb3aff_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformTermFiberSpace_rdb3aff_1 : NormedSpace ℝ TensorFiber := inferInstance
theorem uniform_corrected_term_C1_oai {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) {D : ℝ} (hD : 0 ≤ D) :
    ∃ pt wt mt : ℝ, 0 < pt ∧ 0 < wt ∧ 0 < mt ∧
      ∀ Dw : ℝ, 0 ≤ Dw → ∃ E : ℝ, 0 ≤ E ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < pt) →
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < wt) →
      (∀ a, d.B.WeightedBound 1 1 Dw (psi a)) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mt (G-F) → A.WeightedBound 1 2 D G →
      ∀ f : SmoothPrimitiveFamily (d.B.centers × Fin 3) (g.inner-inducedTensor (r • G)),
      f.phase = d.perturbedPhases ell →
      f.amplitude = d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
        (g.inner-inducedTensor (r • G)) →
      ∀ a, A.TensorWeightedBound 1 1 E (f.term a) := by
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hamp⟩ := d.uniform_actual_amplitude_C1 hF r href
  obtain ⟨Du,hDu,hu⟩ := A.uniform_remainder_C1_bound d.B g r hD
  obtain ⟨V,hV,hv⟩ := d.perturbed_phase_C1_bound
  refine ⟨min pt 1,wt,mt,lt_min hpt zero_lt_one,hwt,hmt,?_⟩
  intro Dw hDw
  obtain ⟨R,hR,hampBound⟩ := hamp Dw Du hDw hDu
  let T := max R V
  have hT : 0 ≤ T := (zero_le_one.trans hR).trans (le_max_left _ _)
  obtain ⟨E,hE,hterm⟩ := d.B.primitive_term_background_C1_bound A hT
  refine ⟨E,hE,?_⟩
  intro ell psi hell hpsi hs hclose hbpsi G hG hnear hGbound f hfphase hfamp a
  have hampa := hampBound ell psi (fun i j => (hell i j).trans_le (min_le_left _ _))
    hpsi hs hclose hbpsi G hG hnear (hu G hG hGbound)
  apply hterm (f.amplitude a) (f.phase a) (f.smoothAmplitude a) (f.smoothPhase a)
  · intro i p hp
    rw [hfamp]
    have h := hampa i a p hp
    exact ⟨h.1.trans (le_max_left _ _),h.2.trans (le_max_left _ _)⟩
  · intro i y hy
    obtain ⟨p,hp,rfl⟩ := hy
    rw [hfphase]
    have h := hv ell (fun i j => (hell i j).le.trans (min_le_right _ _)) i a p hp
    exact ⟨h.1.trans (le_max_right _ _),h.2.trans (le_max_right _ _)⟩

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1_oai.{u_1}
