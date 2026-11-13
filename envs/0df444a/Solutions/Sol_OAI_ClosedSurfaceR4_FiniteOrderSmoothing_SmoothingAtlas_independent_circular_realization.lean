-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:55.912456+00:00
-- url     : https://prove2.me/submissions/515edca3-9385-4e7c-a19a-65b3046ab20a

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CircularPrimitiveFamily_realize_sequence

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
local instance metricBoundSectionNormed_r4293de_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_r4293de_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance quadraticAtlasSectionSpace_r4293de_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPrimitiveFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite smooth primitive families and their partial-cycle metrics.
Different cycles may use different supports and phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothPrimitiveFamily
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyDualSmul
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familySectionNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyFiberNormed
local instance familySectionSpace_r4293de_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma cycleMetric_lower (A : SmoothingAtlas M) (g : SmoothMetric M)
    (N c : ℕ) (s : Finset ι) (p : M) (v : TangentSpace planeModel p) :
    g.inner p v v ≤ (d.cycleMetric A g N c s).inner p v v :=
  le_add_of_nonneg_right (d.cycleTensor_nonneg N c s p v)

end SmoothPrimitiveFamily

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCycleAssembly
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-cycle identities for independently chosen primitive families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance assemblyFiberNormed_r4293de_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance assemblyFiberSpace_r4293de_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance assemblyDualAdd_r4293de_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance assemblyDualSmul_r4293de_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

local instance assemblySectionNormed_r4293de_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance assemblySectionSpace_r4293de_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleAmplitude_square (N : ℕ) (a : ι) (p : M) :
    (d.cycleAmplitude N a p)^2 = (N : ℝ)⁻¹*(d.amplitude a p)^2 := by
  rw [cycleAmplitude,div_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  exact div_eq_inv_mul _ _

end ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPrefixMetrics
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered prefix metrics of a finite circular family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

local instance prefixFiberNormed_r4293de_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance prefixFiberSpace_r4293de_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prefixDualAdd
local instance prefixDualSmul_r4293de_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance prefixSectionNormed_r4293de_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance prefixSectionSpace_r4293de_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] [T2Space M] in
lemma metric_eq_of_inner_eq {g h : SmoothMetric M} (he : g.inner = h.inner) : g = h := by
  cases g
  cases h
  cases he
  rfl

namespace CircularPrimitiveFamily
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prefixDualAdd
local instance prefixFiberNormed_r4293de_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance prefixFiberSpace_r4293de_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance prefixDualSmul_r4293de_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {B : SmoothingAtlas M} {N : ℕ} (d : CircularPrimitiveFamily B (Fin N))

lemma prefixIndices_zero : prefixIndices (0 : Fin (N+1)) = ∅ := by
  ext a
  simp [prefixIndices]

lemma prefixIndices_last : prefixIndices (Fin.last N) = Finset.univ := by
  ext a
  simp [prefixIndices]

lemma prefixIndices_step (a : Fin N) : prefixIndices a.succ = insert a (prefixIndices a.castSucc) := by
  ext b
  simp only [prefixIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Fin.val_succ,Fin.val_castSucc]
  constructor
  · intro h
    by_cases he : b = a
    · exact Or.inl he
    · exact Or.inr (by have hn : b.val ≠ a.val := fun h => he (Fin.ext h); omega)
  · intro h
    rcases h with rfl | h <;> omega

lemma not_mem_prefixIndices (a : Fin N) : a ∉ prefixIndices a.castSucc := by
  simp [prefixIndices]

local instance prefixSectionNormed_r4293de_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance prefixSectionSpace_r4293de_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [T2Space M] in
lemma prefixMetric_inner (g : SmoothMetric M) (k : Fin (N+1)) :
    (d.prefixMetric g k).inner = g.inner +
      (fun p => ∑ a ∈ prefixIndices k, (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p) := by
  funext p
  change g.inner p + (d.smoothFamily.cycleTensor 1 0 (prefixIndices k) p) = _
  simp [SmoothPrimitiveFamily.cycleTensor,SmoothPrimitiveFamily.term,smoothFamily]

omit [T2Space M] in
lemma prefixMetric_zero (g : SmoothMetric M) : d.prefixMetric g 0 = g := by
  apply metric_eq_of_inner_eq
  rw [d.prefixMetric_inner,prefixIndices_zero]
  funext p
  simp

omit [T2Space M] in
lemma prefixMetric_step (g : SmoothMetric M) (a : Fin N) :
    (d.prefixMetric g a.succ).inner = (d.prefixMetric g a.castSucc).inner +
      (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p) := by
  rw [d.prefixMetric_inner,d.prefixMetric_inner,prefixIndices_step]
  funext p
  simp only [Pi.add_apply,Finset.sum_insert (not_mem_prefixIndices a)]
  abel

omit [T2Space M] in
lemma prefixMetric_last (g : SmoothMetric M) :
    (d.prefixMetric g (Fin.last N)).inner = g.inner+d.totalTensor := by
  rw [d.prefixMetric_inner,prefixIndices_last]
  rfl

 theorem realize_total (g h : SmoothMetric M)
    (htarget : h.inner = g.inner+d.totalTensor)
    (hconvex : ∀ a : Fin N, d.ConvexMetric (d.prefixMetric g a.castSucc) a)
    {F : M → Space} (n : PreferredNormal F) (hF : IsSmoothIsometricImmersion M g F)
    (data : MetricGoodPhaseData g F)
    (hgeom : FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) := by
  have hstart : d.prefixMetric g 0 = g := d.prefixMetric_zero g
  have hend : d.prefixMetric g (Fin.last N) = h :=
    metric_eq_of_inner_eq ((d.prefixMetric_last g).trans htarget.symm)
  have hF' : IsSmoothIsometricImmersion M (d.prefixMetric g 0) F := by rwa [hstart]
  have hdata : MetricGoodPhaseData (d.prefixMetric g 0) F := by rwa [hstart]
  obtain ⟨W,hW,hgood,_⟩ := realize_sequence N d (d.prefixMetric g)
    (d.prefixMetric_step g) hconvex F n hF' hdata hgeom
  rw [hend] at hW hgood
  exact ⟨W,hW,hgood⟩

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteCycleOrder
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered prefixes of a finite sequence of primitive cycles. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma finite_cycle_order {m j j' k k' : ℕ} (hj : j < m) (hj' : j' < m) :
    j'+m*k' < j+m*k ↔ k' < k ∨ k' = k ∧ j' < j := by
  by_cases hk : k' < k
  · have hb := Nat.mul_le_mul_left m hk
    simp only [Nat.mul_succ] at hb
    constructor
    · exact fun _ => Or.inl hk
    · intro _
      nlinarith
  by_cases he : k' = k
  · subst k'
    simp only [lt_self_iff_false,false_or,true_and]
    omega
  · have hk' : k < k' := by omega
    have hb := Nat.mul_le_mul_left m hk'
    simp only [Nat.mul_succ] at hb
    constructor
    · intro h
      exfalso
      nlinarith
    · rintro (h | ⟨h,_⟩) <;> contradiction

 theorem finite_cycle_prefix_sum {V : Type*} [AddCommMonoid V] {N m : ℕ}
    (T : Fin N → Fin m → V) (u : V) (hsum : ∀ k, ∑ j, T k j = u)
    (k : Fin N) (j : Fin m) :
    (∑ a ∈ CircularPrimitiveFamily.prefixIndices
        ((finProdFinEquiv (k,j)).castSucc),
      T a.divNat a.modNat) =
      k.val • u + ∑ b ∈ CircularPrimitiveFamily.prefixIndices j.castSucc, T k b := by
  classical
  have horder (k' : Fin N) (j' : Fin m) :
      (finProdFinEquiv (k',j')).val < (finProdFinEquiv (k,j)).val ↔
        k'.val < k.val ∨ k' = k ∧ j'.val < j.val := by
    change j'.val+m*k'.val < j.val+m*k.val ↔ _
    rw [Fin.ext_iff]
    exact finite_cycle_order j.isLt j'.isLt
  have hprefix : (∑ a ∈ CircularPrimitiveFamily.prefixIndices
        ((finProdFinEquiv (k,j)).castSucc), T a.divNat a.modNat) =
      ∑ k' : Fin N, ∑ j' : Fin m,
        if k'.val < k.val ∨ k' = k ∧ j'.val < j.val then T k' j' else 0 := by
    rw [CircularPrimitiveFamily.prefixIndices,Finset.sum_filter]
    rw [← Equiv.sum_comp finProdFinEquiv]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k' _
    apply Finset.sum_congr rfl
    intro j' _
    have hinv : (finProdFinEquiv (k',j')).divNat = k' ∧
        (finProdFinEquiv (k',j')).modNat = j' := by
      exact Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k',j'))
    simp only [Fin.val_castSucc,horder,hinv.1,hinv.2]
  rw [hprefix]
  have hinner (k' : Fin N) :
      (∑ j' : Fin m, if k'.val < k.val ∨ k' = k ∧ j'.val < j.val then T k' j' else 0) =
      (if k'.val < k.val then u else 0) +
        (if k' = k then ∑ b ∈ CircularPrimitiveFamily.prefixIndices j.castSucc, T k b else 0) := by
    by_cases hk : k'.val < k.val
    · have hne : k' ≠ k := by intro h; subst k'; omega
      simp [hk,hne,hsum]
    · by_cases he : k' = k
      · subst k'
        simp [CircularPrimitiveFamily.prefixIndices,Finset.sum_filter]
      · simp [hk,he]
  simp_rw [hinner]
  rw [Finset.sum_add_distrib]
  have hcount : (∑ k' : Fin N, if k'.val < k.val then u else 0) = k.val • u := by
    rw [← Finset.sum_filter,Finset.sum_const]
    congr 1
    have hf : Finset.univ.filter (fun k' : Fin N => k'.val < k.val) = Finset.Iio k := by
      ext a
      simp
    rw [hf,Fin.card_Iio]
  rw [hcount]
  simp

theorem finite_cycle_total_sum {V : Type*} [AddCommMonoid V] {N m : ℕ}
    (T : Fin N → Fin m → V) (u : V) (hsum : ∀ k, ∑ j, T k j = u) :
    (∑ a : Fin (N*m), T a.divNat a.modNat) = N • u := by
  rw [← Equiv.sum_comp finProdFinEquiv,Fintype.sum_prod_type]
  have hinv (k : Fin N) (j : Fin m) :
      (finProdFinEquiv (k,j)).divNat = k ∧ (finProdFinEquiv (k,j)).modNat = j :=
    Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k,j))
  simp_rw [(hinv _ _).1,(hinv _ _).2,hsum]
  simp

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularCycleMetrics
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered prefix metrics of a finite circular family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance flatCycleFiberNormed_r4293de_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance flatCycleFiberSpace_r4293de_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance flatCycleDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace CircularPrimitiveFamily
local instance flatCycleFiberNormed_r4293de_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance flatCycleFiberSpace_r4293de_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance flatCycleDualSmul_r4293de_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {B : SmoothingAtlas M} {N m : ℕ}
    (d : CircularPrimitiveFamily B (Fin (N*m)))
    {u : ∀ p : M, CovariantTwoTensor p}
    (f : Fin N → SmoothPrimitiveFamily (Fin m) u)
    (ha : ∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p)
    (hp : ∀ a, d.phase a = (f a.divNat).phase a.modNat)

include f ha hp

local instance flatCycleSectionNormed_r4293de_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance flatCycleSectionSpace_r4293de_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] [T2Space M] in
lemma flat_cycle_term (a : Fin (N*m)) (p : M) :
    (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p =
      (N : ℝ)⁻¹ • (f a.divNat).term a.modNat p := by
  rw [ha,hp,SmoothPrimitiveFamily.cycleAmplitude_square]
  simp only [SmoothPrimitiveFamily.term,smul_smul]

omit [T2Space M] in
lemma prefixMetric_cycle (g : SmoothMetric M) (k : Fin N) (j : Fin m) :
    d.prefixMetric g (finProdFinEquiv (k,j)).castSucc =
      (f k).cycleMetric B g N k.val (prefixIndices j.castSucc) := by
  apply metric_eq_of_inner_eq
  rw [d.prefixMetric_inner]
  funext p
  change g.inner p + _ = g.inner p + (f k).cycleTensor N k.val (prefixIndices j.castSucc) p
  congr 1
  simp_rw [d.flat_cycle_term f ha hp]
  rw [← Finset.smul_sum]
  rw [finite_cycle_prefix_sum (fun a b => (f a).term b p) (u p)
    (fun a => (f a).sum_eq p) k j]
  rw [smul_add,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  change ((N : ℝ)⁻¹ * (k.val : ℝ)) • u p + _ = _
  rw [mul_comm]
  rfl

omit [CompactSpace M] [T2Space M] in
lemma totalTensor_cycle (hN : 0 < N) : d.totalTensor = u := by
  funext p
  change (∑ a, (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p) = u p
  simp_rw [d.flat_cycle_term f ha hp]
  rw [← Finset.smul_sum,finite_cycle_total_sum (fun a b => (f a).term b p) (u p)
    (fun a => (f a).sum_eq p),← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hN)),one_smul]

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCycleBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed cycle count controls all partial metrics. The estimates allow
a different exact primitive decomposition in every cycle. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleBoundFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleBoundDualAdd
local instance cycleBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
namespace SmoothPrimitiveFamily
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleBoundDualAdd
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u) (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleBoundFiberSpace
local instance cycleBoundSectionNormed_r4293de_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleBoundSectionSpace_r4293de_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma partial_tensor_bound {D : ℝ} (hD : 0 ≤ D) (m : ℕ)
    (hb : ∀ a, A.TensorWeightedBound 1 m D (d.term a)) (s : Finset ι) :
    A.TensorWeightedBound 1 m ((Fintype.card ι : ℝ)*D) (fun p => ∑ a ∈ s, d.term a p) := by
  classical
  intro i
  change WeightedEstimates.WeightedBound univ 1 m _
    (A.bundleLocalize A.tensorTriv i (fun p => ∑ a ∈ s, d.term a p))
  rw [A.bundleLocalize_sum]
  have hh := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ zero_le_one s
    (fun _ : ι => D) (fun a => A.bundleLocalize A.tensorTriv i (d.term a))
    (fun a _ => (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i (d.term_smooth A a)).contDiffOn)
    (fun a _ => hb a i)
  apply hh.mono_const
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ s) hD

lemma scaled_partial_tensor_bound {D : ℝ} (hD : 0 ≤ D) (m : ℕ)
    (hb : ∀ a, A.TensorWeightedBound 1 m D (d.term a)) (N : ℕ) (s : Finset ι) :
    A.TensorWeightedBound 1 m ((Fintype.card ι : ℝ)*D/(N : ℝ))
      ((N : ℝ)⁻¹ • (fun p => ∑ a ∈ s, d.term a p)) := by
  have hh := A.tensorWeightedBound_const_smul
    (ContMDiff.sum_section (fun a _ => d.term_smooth A a))
    (d.partial_tensor_bound A hD m hb s) (N : ℝ)⁻¹
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  ring

lemma cycleMetric_bound {D C : ℝ} (hD : 0 ≤ D) (m : ℕ)
    (hb : ∀ a, A.TensorWeightedBound 1 m D (d.term a))
    (g : SmoothMetric M) (N c : ℕ) (s : Finset ι)
    (hpath : A.TensorWeightedBound 1 m C (g.inner+((c : ℝ)/(N : ℝ)) • u)) :
    A.TensorWeightedBound 1 m (C+(Fintype.card ι : ℝ)*D/(N : ℝ))
      (d.cycleMetric A g N c s).inner := by
  have hsmooth := g.contMDiff.add_section
    ((d.tensor_smooth A).const_smul_section (a := (c : ℝ)/(N : ℝ)))
  have hss : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p ((N : ℝ)⁻¹ • ∑ a ∈ s, d.term a p)) :=
    (ContMDiff.sum_section (fun a _ => d.term_smooth A a)).const_smul_section
  have hh := A.tensorWeightedBound_add hsmooth hss zero_le_one hpath
    (d.scaled_partial_tensor_bound A hD m hb N s)
  have he : (d.cycleMetric A g N c s).inner =
      (g.inner+((c : ℝ)/(N : ℝ)) • u)+(N : ℝ)⁻¹ • (fun p => ∑ a ∈ s, d.term a p) := by
    funext p
    change g.inner p+(((c : ℝ)/(N : ℝ)) • u p+(N : ℝ)⁻¹ • ∑ a ∈ s, d.term a p) = _
    exact (add_assoc _ _ _).symm
  rw [he]
  exact hh

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma exists_cycle_count (D : ℝ) :
    ∃ N : ℕ, 0 < N ∧ (Fintype.card ι : ℝ)*D/(N : ℝ) ≤ 1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((Fintype.card ι : ℝ)*D))
  have hN0 : (0 : ℝ) < N := (le_max_left _ _).trans_lt hN
  refine ⟨N,by exact_mod_cast hN0,?_⟩
  exact (div_le_one hN0).mpr ((le_max_right _ _).trans hN.le)

end SmoothPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentPrefixBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for ordered prefixes in the original atlas, independently of
the atlas that describes the geometric primitive disks. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem independent_prefix_bounds (m : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ N : ℕ, 0 < N ∧ ∀ (B : SmoothingAtlas M) (g g₀ : SmoothMetric M)
      (c C : ℝ), (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) →
      ∀ (u : ∀ p : M, CovariantTwoTensor p)
        (f : Fin N → SmoothPrimitiveFamily (Fin m) u),
      (∀ k a, A.TensorWeightedBound 1 1 D ((f k).term a)) →
      (∀ k : Fin N, A.TensorWeightedBound 1 1 C (g₀.inner+((k.val : ℝ)/(N : ℝ)) • u)) →
      ∀ d : CircularPrimitiveFamily B (Fin (N*m)),
      (∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) →
      (∀ a, d.phase a = (f a.divNat).phase a.modNat) →
      ∀ a : Fin (N*m), A.TensorWeightedBound 1 1 (C+1) (d.prefixMetric g₀ a.castSucc).inner ∧
        ∀ p v, c*g.inner p v v ≤ (d.prefixMetric g₀ a.castSucc).inner p v v := by
  obtain ⟨N,hN,hcount⟩ := SmoothPrimitiveFamily.exists_cycle_count (ι := Fin m) D
  refine ⟨N,hN,?_⟩
  intro B g g₀ c C hlower u f hb hpath d ha hp a
  obtain ⟨⟨k,j⟩,rfl⟩ := finProdFinEquiv.surjective a
  rw [d.prefixMetric_cycle f ha hp g₀ k j]
  have he : (f k).cycleMetric B g₀ N k.val (CircularPrimitiveFamily.prefixIndices j.castSucc) =
      (f k).cycleMetric A g₀ N k.val (CircularPrimitiveFamily.prefixIndices j.castSucc) :=
    metric_eq_of_inner_eq rfl
  rw [he]
  refine ⟨?_,?_⟩
  · have hh := (f k).cycleMetric_bound A hD 1 (hb k) g₀ N k.val
      (CircularPrimitiveFamily.prefixIndices j.castSucc) (hpath k)
    intro i
    apply (hh i).mono_const
    simpa only [Fintype.card_fin] using add_le_add_right hcount C
  · intro p v
    exact (hlower p v).trans ((f k).cycleMetric_lower A g₀ N k.val
      (CircularPrimitiveFamily.prefixIndices j.castSucc) p v)

end SmoothingAtlas
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

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem independent_circular_realization_oai (g : SmoothMetric M) (c C : ℝ)
    (B : SmoothingAtlas M) (r L K : B.centers → ℝ)
    (hL : ∀ i, 0 < L i)
    (hreg : ∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target)
    (hnon : ∀ i p, 0 ≤ B.weight i p)
    (hpos : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i))
    (hphase : ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 (C+1) h.inner →
      (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
      ∀ (i : B.centers) (q : M), q ∈ circularDiskClosure (i : M) (r i) →
        ∀ ell : Base, ‖ell‖ ≤ K i → ∀ v : Base,
          (L i/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
            (centeredConvexPhase ell (L i) (coordinateChart (i : M) i))
            (coordinateChart (i : M) q) v v)
    (m : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ N : ℕ, 0 < N ∧ ∀ g₀ : SmoothMetric M,
      (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) →
      ∀ (u : ∀ p : M, CovariantTwoTensor p)
        (f : Fin N → SmoothPrimitiveFamily (Fin m) u),
      (∀ k a, A.TensorWeightedBound 1 1 D ((f k).term a)) →
      (∀ k : Fin N, A.TensorWeightedBound 1 1 C (g₀.inner+((k.val : ℝ)/(N : ℝ)) • u)) →
      ∀ d : CircularPrimitiveFamily B (Fin (N*m)),
      (∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) →
      (∀ a, d.phase a = (f a.divNat).phase a.modNat) →
      (∀ a, d.convexPart a = L (d.curves a).index) →
      (∀ a, ‖d.linearPart a‖ ≤ K (d.curves a).index) →
      ∀ h : SmoothMetric M, h.inner = g₀.inner+u →
      ∀ (F : M → Space) (n : PreferredNormal F), IsSmoothIsometricImmersion M g₀ F →
        MetricGoodPhaseData g₀ F →
        FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
      ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) := by
  obtain ⟨N,hN,hbounds⟩ := A.independent_prefix_bounds m D hD
  refine ⟨N,hN,?_⟩
  intro g₀ hlower u f hb hpath d ha hp hpart hell h htarget F n hF data hgeom
  have hcv (a : Fin (N*m)) : d.ConvexMetric (d.prefixMetric g₀ a.castSucc) a := by
    intro q hq _hqrad v hv
    obtain ⟨hbound,hlow⟩ := hbounds B g g₀ c C hlower u f hb hpath d ha hp a
    have hqc := circular_weight_support r hreg hnon hpos (d.curves a).index hq
    have he := hphase _ hbound hlow (d.curves a).index q hqc (d.linearPart a) (hell a) v
    rw [hpart]
    have hs : 0 < v.1^2+v.2^2 := by
      by_contra hn
      have h1 : v.1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg v.2])
      have h2 : v.2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg v.1])
      exact hv (Prod.ext h1 h2)
    exact (mul_pos (half_pos (hL _)) hs).trans_le he
  apply d.realize_total g₀ h _ hcv n hF data hgeom
  rw [d.totalTensor_cycle f ha hp hN]
  exact htarget

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization_oai.{u_1}
