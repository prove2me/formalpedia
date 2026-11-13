-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.metric_frame_tolerance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:39:30.732271+00:00
-- url     : https://prove2.me/submissions/9d12d514-4b73-404a-84d0-b48b93de897c

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_induced_metric_difference_bound

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
local instance coordinateFiberSpace_rcdf05a_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance chartReadSectionNormed_rcdf05a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_rcdf05a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalizationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed C2 atlas budget for radial normalization. A smooth extension
through zero is used only outside the region contributing to localization. -/
noncomputable section
open Set Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma exists_weighted_bound (m : ℕ) {H : M → Space}
    (hH : ContMDiff planeModel spaceModel ∞ H) :
    ∃ C : ℝ, 0 ≤ C ∧ A.WeightedBound 1 m C H := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hH)
    (localize_compact (i : M) (A.weight_support i) H) m
  exact ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),fun i =>
    (hb i).mono_const (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
local instance crossTransitionDualSmul_rcdf05a_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

variable [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberNormed
local instance crossTransitionSectionNormed_rcdf05a_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTransitionSectionSpace_rcdf05a_1 (p : M) :
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
local instance crossTensorBoundSectionNormed_rcdf05a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTensorBoundSectionSpace_rcdf05a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteScalarBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ClosedSurfaceR4

lemma finite_positive_lower {ι : Type*} [Finite ι] {f : ι → ℝ}
    (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  let := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i by
    obtain ⟨δ,hδ,h⟩ := this Finset.univ
    exact ⟨δ,hδ,fun i => h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ,hδ,h⟩ := ih
    refine ⟨min (f i) δ,lt_min (hf i) hδ,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (h j hj)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_IndependentTensorReadTolerance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small background-atlas norm gives small tensor readings in each
fixed primitive chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.readToleranceFiberSpace
local instance readToleranceDualAdd_rcdf05a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.readToleranceDualSmul
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.readToleranceFiberNormed
local instance readToleranceSectionNormed_rcdf05a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance readToleranceSectionSpace_rcdf05a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem tensor_read_tolerance {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ u : ∀ p : M, CovariantTwoTensor p,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      A.TensorWeightedBound 1 0 eps u →
      ∀ (i : B.centers) (y : JetPolynomial.Base), ‖B.tensorChartRead i u y‖ < eta := by
  obtain ⟨D,hD,hchange⟩ := A.tensorWeightedBound_change_atlas B 0
  choose E hE hread using fun i : B.centers => B.tensorChartRead_bound i 0
  obtain ⟨eps,heps,hle⟩ := finite_positive_lower (fun i : B.centers =>
    (show 0 < eta/(2*(E i*D+1)) by have := hE i; positivity))
  refine ⟨eps,heps,?_⟩
  intro u hu hb i y
  have hB := hchange u 1 eps zero_lt_one le_rfl heps.le hu hb
  have hh := (hread i u 1 (D*eps) zero_lt_one le_rfl (mul_nonneg hD heps.le) hu hB).norm_le
    (mem_univ y)
  have hEi := hE i
  have hd := (le_div_iff₀ (show 0 < 2*(E i*D+1) by positivity)).mp (hle i)
  have he : 0 ≤ E i*D := mul_nonneg (hE i) hD
  have hstrict : E i*(D*eps) < eta := by nlinarith
  exact hh.trans_lt hstrict

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
local instance quadraticAtlasSectionSpace_rcdf05a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledInitialMap
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial contraction of an approximate immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberNormed
local instance initialSectionNormed_rcdf05a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialSectionSpace_rcdf05a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma inducedTensor_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    inducedTensor (a • F) = a^2 • inducedTensor F := by
  funext p
  ext v w
  have hd : (mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) =
      a • (mfderiv planeModel spaceModel F p : Plane →L[ℝ] Space) :=
    const_smul_mfderiv ((hF p).mdifferentiableAt (by simp)) a
  change inner ℝ ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) v)
    ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) w) =
    a^2*inner ℝ (mfderiv planeModel spaceModel F p v) (mfderiv planeModel spaceModel F p w)
  have hv := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from v)) hd
  have hw := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from w)) hd
  change (mfderiv planeModel spaceModel (a • F) p v : Space) =
    a • (mfderiv planeModel spaceModel F p v : Space) at hv
  change (mfderiv planeModel spaceModel (a • F) p w : Space) =
    a • (mfderiv planeModel spaceModel F p w : Space) at hw
  calc
    _ = inner ℝ (a • (mfderiv planeModel spaceModel F p v : Space))
        (a • (mfderiv planeModel spaceModel F p w : Space)) :=
      congrArg₂ (fun x y : Space => inner ℝ x y) hv hw
    _ = _ := by rw [real_inner_smul_left,real_inner_smul_right]; ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_InducedMetricReadTolerance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-point C1 accuracy makes the actual scaled metric arbitrarily
close to its fixed reference in every primitive chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem induced_metric_read_tolerance {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ) {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 1 eps (G-F) →
      ∀ (i : B.centers) (y : JetPolynomial.Base),
        ‖B.tensorChartRead i (inducedTensor (r • G)-inducedTensor (r • F)) y‖ < eta := by
  obtain ⟨C,hC,hFb⟩ := A.exists_weighted_bound 1 hF
  obtain ⟨E,hE,hmetric⟩ := A.induced_metric_difference_bound 0
  obtain ⟨delta,hdelta,hread⟩ := A.tensor_read_tolerance B heta
  let K := r^2*E*(C+1)
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  let eps := min 1 (delta/(K+1))
  have heps : 0 < eps := lt_min zero_lt_one (div_pos hdelta (by linarith))
  have hKe : K*eps ≤ delta := by
    have hh := (le_div_iff₀ (by linarith : 0 < K+1)).mp (min_le_right 1 (delta/(K+1)))
    nlinarith
  refine ⟨eps,heps,?_⟩
  intro G hG hclose i y
  have hGb : A.WeightedBound 1 1 (C+1) G := by
    have hh := A.weightedBound_add hF (hG.sub hF) zero_le_one hFb hclose
    have heq : F+(G-F) = G := by abel
    change A.WeightedBound 1 1 (C+eps) (F+(G-F)) at hh
    rw [heq] at hh
    exact fun i => (hh i).mono_const (by have hh : eps ≤ 1 := min_le_left _ _; linarith)
  have hFb' : A.WeightedBound 1 1 (C+1) F := fun i => (hFb i).mono_const (by linarith)
  have hb := hmetric (C+1) eps (by linarith) heps.le F G hF hG hFb' hGb hclose
  have hs := A.tensorWeightedBound_const_smul
    ((A.inducedTensor_smooth hG).sub_section (A.inducedTensor_smooth hF)) hb (r^2)
  have heq : inducedTensor (r • G)-inducedTensor (r • F) =
      r^2 • (inducedTensor G-inducedTensor F) := by
    rw [inducedTensor_const_smul hG r,inducedTensor_const_smul hF r]
    funext p
    ext v w
    change r^2*inducedTensor G p v w-r^2*inducedTensor F p v w =
      r^2*(inducedTensor G p v w-inducedTensor F p v w)
    ring
  have hb' : A.TensorWeightedBound 1 0 delta (inducedTensor (r • G)-inducedTensor (r • F)) := by
    rw [heq]
    intro a
    apply (hs a).mono_const
    rw [abs_of_nonneg (sq_nonneg r)]
    calc
      r^2*(E*(C+1)*eps) = K*eps := by dsimp [K] <;> ring
      _ ≤ delta := hKe
  have hGs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hFs : ContMDiff planeModel spaceModel ∞ (r • F) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hF
  exact hread _ ((A.inducedTensor_smooth hGs).sub_section (A.inducedTensor_smooth hFs)) hb' i y

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
local instance refMetricDualSmul_rcdf05a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricSectionNormed
local instance refMetricSectionSpace_rcdf05a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
namespace ReferenceCircularAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricFiberSpace
local instance refMetricDualSmul_rcdf05a_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refMetricSectionNormed
local instance refMetricSectionSpace_rcdf05a_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem metric_frame_tolerance_oai {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 1 eps (G-F) →
      ∀ i p, p ∈ tsupport (d.B.weight i) →
        ‖(d.B.tensorTriv i).continuousLinearMapAt ℝ p
          ((g.inner-inducedTensor (r • G)) p)-d.chartReference i (chart (i : M) p)‖ < eta := by
  obtain ⟨eps,heps,hnear⟩ := A.induced_metric_read_tolerance d.B hF r
    (div_pos heta (show 0 < ‖fiberFromThree‖+1 by positivity))
  refine ⟨eps,heps,?_⟩
  intro G hG hb i p hp
  have hsym : ∀ p v w, (g.inner-inducedTensor (r • G)) p v w =
      (g.inner-inducedTensor (r • G)) p w v := by
    intro p v w
    change g.inner p v w-inner ℝ (mfderiv planeModel spaceModel (r • G) p v)
      (mfderiv planeModel spaceModel (r • G) p w) =
      g.inner p w v-inner ℝ (mfderiv planeModel spaceModel (r • G) p w)
      (mfderiv planeModel spaceModel (r • G) p v)
    rw [g.symm,real_inner_comm]
  rw [d.B.tensor_frame_read i _ hsym hp]
  change ‖fiberFromThree (d.B.tensorChartRead i (g.inner-inducedTensor (r • G)) (chart (i : M) p))-
    fiberFromThree (d.B.tensorChartRead i gref.inner (chart (i : M) p))‖ < eta
  rw [← map_sub]
  have hread : d.B.tensorChartRead i (g.inner-inducedTensor (r • G)) (chart (i : M) p)-
      d.B.tensorChartRead i gref.inner (chart (i : M) p) =
      -d.B.tensorChartRead i (inducedTensor (r • G)-inducedTensor (r • F)) (chart (i : M) p) := by
    rw [href]
    simp only [d.B.tensorChartRead_on_weight i _ hp, SmoothingAtlas.bundleComponent,
      Pi.sub_apply,map_sub]
    abel
  rw [hread,map_neg,norm_neg]
  have h := (fiberFromThree.le_opNorm
    (d.B.tensorChartRead i (inducedTensor (r • G)-inducedTensor (r • F)) (chart (i : M) p)))
  have hn := hnear G hG hb i (chart (i : M) p)
  have hmul : ‖fiberFromThree‖ * ‖d.B.tensorChartRead i
      (inducedTensor (r • G)-inducedTensor (r • F)) (chart (i : M) p)‖ < eta := by
    have he := (lt_div_iff₀ (show 0 < ‖fiberFromThree‖+1 by positivity)).mp hn
    nlinarith [norm_nonneg (d.B.tensorChartRead i
      (inducedTensor (r • G)-inducedTensor (r • F)) (chart (i : M) p))]
  exact h.trans_lt hmul

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.metric_frame_tolerance_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.metric_frame_tolerance_oai.{u_1}
