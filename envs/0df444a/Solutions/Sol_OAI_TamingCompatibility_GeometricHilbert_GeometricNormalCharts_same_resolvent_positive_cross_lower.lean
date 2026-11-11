-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_positive_cross_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:02:14.731229+00:00
-- url     : https://prove2.me/submissions/1e0473ae-e3b6-45ec-9efc-da7c8fd12ee8

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc032
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_gammaNormalWedge_angular
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_wedge_kernel

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FourthMomentKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Bundle Set TopologicalSpace
lemma bundle_totalSpace_secondCountable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [SecondCountableTopology B] [SecondCountableTopology F] (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] :
    SecondCountableTopology (TotalSpace F E) := by
  let e : B → Trivialization F (π F E) := fun b => trivializationAt F E b
  obtain ⟨s,hsc,hs⟩ := isOpen_iUnion_countable (fun b => (e b).baseSet) (fun b => (e b).open_baseSet)
  have hcover : (⋃ b : B, (e b).baseSet) = univ := by
    apply eq_univ_iff_forall.mpr
    intro b
    exact mem_iUnion.mpr ⟨b,mem_baseSet_trivializationAt F E b⟩
  rw [hcover] at hs
  let := hsc.to_subtype
  let U : s → Set (TotalSpace F E) := fun b => (e b.val).source
  have (b : s) : SecondCountableTopology (U b) :=
    (e b.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := U) (fun b => (e b.val).open_source)
  apply eq_univ_iff_forall.mpr
  intro v
  have hv : v.proj ∈ ⋃ b ∈ s, (e b).baseSet := hs.symm ▸ mem_univ _
  obtain ⟨b,hb,hv⟩ := mem_iUnion₂.mp hv
  exact mem_iUnion.mpr ⟨⟨b,hb⟩,(e b).mem_source.mpr hv⟩
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [SecondCountableTopology X]
lemma unitSecondCountable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    SecondCountableTopology (MetricUnit g) := by
  have : SecondCountableTopology (TangentBundle Model X) :=
    bundle_totalSpace_secondCountable (TangentSpace Model : X → Type)
  exact TopologicalSpace.Subtype.secondCountableTopology {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1}
end TamingCompatibility

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Set Metric
open scoped ContDiff
variable {P V W A B : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma linear_bound_on_tube (F : P × V → W) (K : Set P) (hK : IsCompact K)
    {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖ := by
  have hpc : ContinuousOn (dpos F) (K ×ˢ closedBall (0 : V) r) :=
    fun x hx => ((dpos_contDiffAt F x (hF x hx)).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn hpc
  refine ⟨max C 0,le_max_right _ _,fun p hp z hz => ?_⟩
  have hd (u : V) (hu : u ∈ closedBall (0 : V) r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) ⟨hp,hu⟩).differentiableAt (by simp)
  have hb (u : V) (hu : u ∈ closedBall (0 : V) r) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ max C 0 := by
    rw [←dpos_eq_at F p u (hd u hu)]
    exact (hC (p,u) ⟨hp,hu⟩).trans (le_max_left _ _)
  simpa using (convex_closedBall (0 : V) r).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u hu).comp u ((differentiableAt_const p).prodMk differentiableAt_id)) hb
    (show (0 : V) ∈ closedBall 0 r by simpa using hr)
    (show z ∈ closedBall 0 r by simpa using hz)

end TamingCompatibility.GeometricHilbert.UniformJets

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {E F W : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup W]
attribute [local instance] Classical.propDecidable

lemma support_push_subset (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hf : Function.support f ⊆ K) : Function.support (push C f) ⊆ C '' K := by
  intro y hy
  have ht : y ∈ C.target := by
    by_contra h
    exact hy (by simp [push,h])
  refine ⟨C.symm y,hf ?_,C.right_inv ht⟩
  simpa [Function.mem_support,push,ht] using hy

lemma tsupport_push_subset (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hK : IsCompact K) (hKC : K ⊆ C.source) (hf : Function.support f ⊆ K) :
    tsupport (push C f) ⊆ C '' K :=
  closure_minimal (support_push_subset C f K hf)
    (hK.image_of_continuousOn (C.continuousOn.mono hKC)).isClosed

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPatch
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedSpace
lemma leadingCoordinate_support (ψ χ : Space → ℝ) (t : ℝ) :
    Function.support (leadingCoordinate J α ht p D g B ψ χ t) ⊆
      Function.support ψ ×ˢ Function.support χ := by
  intro x hx
  constructor
  · intro h
    apply hx
    apply ContinuousLinearMap.ext
    intro u
    simp only [leadingCoordinate,smul_apply,h,zero_apply]
    simp
  · intro h
    apply hx
    apply ContinuousLinearMap.ext
    intro u
    simp only [leadingCoordinate,smul_apply,h,zero_apply]
    simp

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixGaussian
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixGaussianMetricNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixGaussianMetricNormedSpace
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)

include hg hB

lemma normalMap_compact_bound (K : Set Space) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ‖normalMap g B q z - q‖ ≤ C*‖z‖ := by
  obtain ⟨C,hC,hb⟩ := linear_bound_on_tube (fun x : Space × Space => normalMap g B x.1 x.2)
    K hK hr (fun _ _ => (normalMap_joint g B hg hB).contDiffAt)
  refine ⟨C+1,by linarith,fun q hq z hz => ?_⟩
  have hh : ‖normalMap g B q z - q‖ ≤ C*‖z‖ := by
    simpa only [normalMap_zero] using hb q hq z hz
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z))

attribute [local irreducible] normalGauge normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPartition
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldLocalization
open Set ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_bounds (p : A.centers) (q : Space) :
    0 ≤ coordinatePartition A p q ∧ coordinatePartition A p q ≤ 1 := by
  by_cases hq : q ∈ (extChartAt Model p.val).target
  · simp only [coordinatePartition,Set.indicator_of_mem hq]
    exact ⟨A.partition.nonneg _ _,A.partition.le_one _ _⟩
  · simp only [coordinatePartition,Set.indicator_of_notMem hq,le_refl,zero_le_one,and_self]

end TamingCompatibility.ManifoldLocalization

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAtlasPatches
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r04ad9c_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r04ad9c_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma normalCutoff_tsupport : tsupport (D.normalCutoff : Space → ℝ) ⊆ Metric.closedBall (0 : Space) D.radius := by
  rw [D.normalCutoff.tsupport_eq]
  apply Metric.closedBall_subset_closedBall
  change D.radius/2 ≤ D.radius
  linarith [D.radius_pos]

end ParametrixData

variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r04ad9c_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r04ad9c_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hD in
lemma coordinatePartition_centerSupport (p : A.centers) :
    tsupport (coordinatePartition A p) ⊆ Metric.closedBall (extChartAt Model p.val p.val) (D p).radius := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := coordinatePartition_tsupport A p hq
  exact Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos])
    ((D p).source_image_subset ⟨x,hD p hx,rfl⟩)

include hD in
lemma partition_patch_support (p : A.centers) :
    Function.support (coordinatePartition A p) ×ˢ tsupport ((D p).normalCutoff : Space → ℝ) ⊆
      (D p).normalCompact :=
  Set.prod_mono ((subset_tsupport _).trans (coordinatePartition_centerSupport J α ht A D hD p))
    (D p).normalCutoff_tsupport

include hD in
lemma partitionLeading_tsupport (p : A.centers) (t : ℝ) :
    tsupport (partitionLeading J α ht A D p t) ⊆ (D p).physicalCompact := by
  apply KernelExtension.tsupport_push_subset _ _ _ (D p).normalCompact_compact (D p).normalCompact_source
  exact (leadingCoordinate_support J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    _ _ t).trans ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans
      (partition_patch_support J α ht A D hD p))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraBounds
open _root_.MeasureTheory Set Metric
open scoped Topology
variable {X B : Type*} [PseudoMetricSpace X]

lemma weight_one_le (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    1 ≤ weight N t x y := by
  apply one_le_pow₀
  have := div_nonneg (dist_nonneg (x := x) (y := y)) (Real.sqrt_pos.2 ht).le
  linarith

lemma weight_pos (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    0 < weight N t x y := lt_of_lt_of_le zero_lt_one (weight_one_le N ht x y)

end TamingCompatibility.GeometricHilbert.VolterraBounds

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma evaluationVector_continuous : Continuous (C.evaluationVector g) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.evaluation_continuous g)).clm_apply continuous_const

lemma evaluationVector_integrable (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    Integrable (C.evaluationVector g) μ :=
  (C.evaluationVector_continuous g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma wedgeKernel_continuous : Continuous (fun p : MetricUnit g × MetricUnit g => C.wedgeKernel g p.1 p.2) :=
  ((C.evaluationVector_continuous g).comp continuous_fst).inner
    ((l2Star A J α hs ht).continuous.comp ((C.evaluationVector_continuous g).comp continuous_snd))

lemma regularize_wedge (μ ν : Measure (MetricUnit g)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪C.regularize g μ,l2Star A J α hs ht (C.regularize g ν)⟫ =
      ∫ u, ∫ v, C.wedgeKernel g u v ∂ν ∂μ := by
  have hν := C.evaluationVector_integrable g ν
  have hμ := C.evaluationVector_integrable g μ
  rw [regularize,regularize,← (l2Star A J α hs ht).integral_comp_comm hν]
  have hi : Integrable (fun v => l2Star A J α hs ht (C.evaluationVector g v)) ν :=
    (l2Star A J α hs ht).integrable_comp hν
  have hp := (innerSL ℝ (∫ v, l2Star A J α hs ht (C.evaluationVector g v) ∂ν)).integral_comp_comm hμ
  simp only [innerSL_apply_apply] at hp
  rw [real_inner_comm,← hp]
  apply integral_congr_ae
  filter_upwards [] with u
  have h := (innerSL ℝ (C.evaluationVector g u)).integral_comp_comm hi
  simpa only [innerSL_apply_apply,wedgeKernel,real_inner_comm] using h.symm

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricDistance
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.RiemannianChartDistance
open Bundle Manifold Set Metric _root_.MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) 1 X]
  [RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
  ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.RiemannianChartDistance.inverseChartNormedAddCommGroup
lemma chart_segment_bound (p : X) (K : Set E) (hconv : Convex ℝ K)
    (hK : K ⊆ (extChartAt 𝓘(ℝ,E) p).target) (C : ℝ≥0)
    (hC : ∀ z ∈ K, ‖mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm z‖ₑ ≤ C)
    {q r : E} (hq : q ∈ K) (hr : r ∈ K) :
    riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm q)
      ((extChartAt 𝓘(ℝ,E) p).symm r) ≤ C*edist q r := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) q r
  let γ := (extChartAt 𝓘(ℝ,E) p).symm ∘ η
  have hη : Icc 0 1 ⊆ η ⁻¹' K := by
    rw [← image_subset_iff,ContinuousAffineMap.coe_lineMap_eq,← segment_eq_image_lineMap]
    exact hconv.segment_subset hq hr
  have hηs : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 η (Icc 0 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact η.contDiff.contDiffOn
  have hb : riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm q)
      ((extChartAt 𝓘(ℝ,E) p).symm r) ≤ pathELength 𝓘(ℝ,E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm p).comp hηs (hη.trans (preimage_mono hK))
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  apply hb.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have he : mfderiv[Icc 0 1] γ t =
      (mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hK (hη ht))
    · exact hηs.mdifferentiableOn one_ne_zero t ht
    · exact (hη.trans (preimage_mono hK)).trans (preimage_mono (extChartAt_target_subset_range p))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hev : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congrArg (fun L => L 1) he
  rw [hev]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  apply mul_le_mul (hC (η t) (hη ht))
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl
  · exact bot_le
  · exact bot_le

end TamingCompatibility.RiemannianChartDistance

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms ManifoldVolume Set Filter Metric
open scoped Manifold ContDiff Topology NNReal ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
include hs in
lemma chartMetric_norm_continuousOn (p : X) :
    ContinuousOn (fun z => ‖chartMetric J α p z‖) (extChartAt Model p).target := by
  let : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hh : ContinuousOn (chartMetric J α p) (extChartAt Model p).target :=
    ((hs.invariantPart J).metricCoords J p).continuousOn
  exact (continuous_norm : Continuous (norm : (Space →L[ℝ] Space →L[ℝ] ℝ) → ℝ)).comp_continuousOn hh

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
  TamingCompatibility.RiemannianChartDistance.inverseChartNormedAddCommGroup

lemma inverseChart_opNorm (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨(hermitianMetric J α hs ht).toRiemannianMetric⟩
    ‖mfderivWithin Model Model (extChartAt Model p).symm (Set.range Model) z‖ ≤ Real.sqrt ‖chartMetric J α p z‖ := by
  dsimp only
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨(hermitianMetric J α hs ht).toRiemannianMetric⟩
  rw [show Set.range Model = univ by simp [Model],mfderivWithin_univ]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  have he : ‖mfderiv Model Model (extChartAt Model p).symm z u‖^2 = chartMetric J α p z u u := by
    exact (real_inner_self_eq_norm_sq _).symm.trans
      (chartMetric_derivative J α p hz u u).symm
  have hb : chartMetric J α p z u u ≤ ‖chartMetric J α p z‖*‖u‖^2 := by
    calc
      _ ≤ ‖chartMetric J α p z u u‖ := le_abs_self _
      _ ≤ ‖chartMetric J α p z‖*‖u‖*‖u‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mp
  rw [mul_pow,Real.sq_sqrt (norm_nonneg (chartMetric J α p z))]
  exact he.trans_le hb

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma chartInverse_locallyLipschitz (p : X) :
    let := geometricMetricSpace J α hs ht
    LocallyLipschitzOn (extChartAt Model p).target (extChartAt Model p).symm := by
  dsimp only
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let := geometricMetricSpace J α hs ht
  intro z hz
  have hc : ContinuousAt (fun y => ‖chartMetric J α p y‖) z :=
    (chartMetric_norm_continuousOn J α hs p).continuousAt
      ((isOpen_extChartAt_target p).mem_nhds hz)
  let C := Real.sqrt (‖chartMetric J α p z‖+1)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hn : {y | ‖chartMetric J α p y‖ < ‖chartMetric J α p z‖+1} ∈ 𝓝 z :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((isOpen_extChartAt_target p).mem_nhds hz) hn)
  refine ⟨⟨C,hC⟩,Metric.ball z r,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr),?_⟩
  intro q hq y hy
  change hermitianEDist J α hs ht _ _ ≤ _
  apply RiemannianChartDistance.chart_segment_bound p _ (convex_ball z r)
    (fun _ h => (hrsub h).1) ⟨C,hC⟩ ?_ hq hy
  intro w hw
  have hb := (inverseChart_opNorm J α hs ht p (hrsub hw).1).trans
    (Real.sqrt_le_sqrt (le_of_lt (hrsub hw).2))
  exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp hb)

lemma chartInverse_compact_lipschitz (p : X) (K : Set Space)
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt Model p).target) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ≥0, LipschitzOnWith C (extChartAt Model p).symm K := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    ((chartInverse_locallyLipschitz J α hs ht p).mono hKt)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PhysicalUnitProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms Set
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

lemma physicalProfile_unit_pair_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) =>
      physicalProfile J α hs ht r vu.1.val.proj vu.2.val.proj) := by
  let := geometricMetricSpace J α hs ht
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have h₁ : Continuous (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) => vu.1.val.proj) :=
    hp.comp continuous_fst
  have h₂ : Continuous (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) => vu.2.val.proj) :=
    hp.comp continuous_snd
  change Continuous (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) =>
    ((1+dist vu.1.val.proj vu.2.val.proj/r)⁻¹)^6)
  exact ((continuous_const.add ((h₁.dist h₂).div_const r)).inv₀
    (fun vu => (show 0 < 1+dist vu.1.val.proj vu.2.val.proj/r by positivity).ne')).pow 6
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
open Set _root_.MeasureTheory
namespace TamingCompatibility
lemma continuous_double_integral_lower
    {Y Z : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopologyEither Y Z]
    (ν : Measure Y) (μ : Measure Z) [IsFiniteMeasure ν] [IsProbabilityMeasure μ]
    (p k : Y × Z → ℝ) (hp : Continuous p) (hk : Continuous k)
    (C B : ℝ) (h : ∀ y z, -C*p (y,z)-B ≤ k (y,z)) :
    -C*(∫ y, ∫ z, p (y,z) ∂μ ∂ν)-B*ν.real univ ≤ ∫ y, ∫ z, k (y,z) ∂μ ∂ν := by
  have hi : Integrable p (ν.prod μ) := hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hki : Integrable k (ν.prod μ) := hk.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh (y : Y) : -C*(∫ z, p (y,z) ∂μ)-B ≤ ∫ z, k (y,z) ∂μ := by
    have hpi : Integrable (fun z => p (y,z)) μ :=
      (hp.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hki : Integrable (fun z => k (y,z)) μ :=
      (hk.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hh := integral_mono ((hpi.const_mul (-C)).sub (integrable_const B)) hki (h y)
    simp only [Pi.sub_apply] at hh
    simpa only [integral_sub (hpi.const_mul (-C)) (integrable_const B),integral_const_mul,
      integral_const,probReal_univ,one_smul] using hh
  have hh' := integral_mono ((hi.integral_prod_left.const_mul (-C)).sub (integrable_const B))
    hki.integral_prod_left hh
  simp only [Pi.sub_apply] at hh'
  simpa only [integral_sub (hi.integral_prod_left.const_mul (-C)) (integrable_const B),integral_const_mul,
    integral_const,smul_eq_mul,mul_comm (ν.real univ)] using hh'
end TamingCompatibility

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization _root_.MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable [T2Space X]
variable {A J α hs ht D hD}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma heatEvaluation_continuous : Continuous (C.heatEvaluation g) :=
  (C.evaluation_continuous g).clm_comp continuous_const

lemma heatEvaluationVector_continuous : Continuous (C.heatEvaluationVector g) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.heatEvaluation_continuous g)).clm_apply continuous_const

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelGammaBounds
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open _root_.MeasureTheory Set

lemma rapidConstant_pos {c : ℝ} (hc : 0 < c) (N : ℕ) :
    0 < rapidConstant c N := by
  unfold rapidConstant
  positivity

lemma moment_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s^n * Real.exp (-(b*s))) (Ioi 0) := by
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)

lemma moment_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ s : ℝ in Ioi 0, s^n * Real.exp (-(b*s))) = moment n b := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1)
    (by positivity) hb
  simp_rw [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  have he : (n:ℝ)+1 = ((n+1:ℕ):ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast] at h
  exact h

lemma moment_pos (n : ℕ) {b : ℝ} (hb : 0 < b) : 0 < moment n b := by
  unfold moment
  positivity

lemma profile_nonneg (n : ℕ) (c a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ profile n c a s := by
  unfold profile
  positivity

lemma gaussian_exponent_split {c a s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    -s - c*a^2/s ≤ -(s/2) - 2*(min (1/2) c)*a := by
  let k := min (1/2 : ℝ) c
  have hk : 0 ≤ k := le_of_lt (lt_min (by norm_num) hc)
  have hk₁ : k ≤ 1/2 := min_le_left _ _
  have hk₂ : k ≤ c := min_le_right _ _
  have hsq := mul_nonneg hk (sq_nonneg (s-a))
  have ht := mul_nonneg (sub_nonneg.mpr hk₁) (sq_nonneg s)
  have hu := mul_nonneg (sub_nonneg.mpr hk₂) (sq_nonneg a)
  have h : 2*k*a*s ≤ s^2/2+c*a^2 := by nlinarith
  have hd := (div_le_div_of_nonneg_right h hs.le)
  have he : (2*k*a*s)/s = 2*k*a := by field_simp
  have he' : (s^2/2+c*a^2)/s = s/2+c*a^2/s := by field_simp
  rw [he,he'] at hd
  change -s-c*a^2/s ≤ -(s/2)-2*k*a
  linarith

lemma profile_le_exp (n : ℕ) {c a s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    profile n c a s ≤
      (s^n * Real.exp (-((1/2)*s))) * Real.exp (-(2*min (1/2) c)*a) := by
  unfold profile
  have h := Real.exp_le_exp.mpr (gaussian_exponent_split (a := a) hc hs)
  have he : Real.exp (-s) * Real.exp (-c*a^2/s) = Real.exp (-s-c*a^2/s) := by
    rw [← Real.exp_add]; congr 1; ring
  have he' : Real.exp (-(s/2)-2*min (1/2) c*a) =
      Real.exp (-((1/2)*s)) * Real.exp (-(2*min (1/2) c)*a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← he,he'] at h
  have hp := mul_le_mul_of_nonneg_left h (pow_nonneg hs.le n)
  nlinarith only [hp]

lemma profile_integrable (n : ℕ) {c a : ℝ} (hc : 0 < c) :
    IntegrableOn (profile n c a) (Ioi 0) := by
  apply ((moment_integrable n (by norm_num : (0:ℝ)<1/2)).mul_const
    (Real.exp (-(2*min (1/2) c)*a))).mono' (by
      unfold profile
      exact (by fun_prop : Measurable _).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg _ _ _ hs.le)]
  exact profile_le_exp n hc hs

lemma truncatedProfile_nonneg (n : ℕ) (c a T : ℝ) :
    0 ≤ truncatedProfile n c a T := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact profile_nonneg n c a hs.1.le

lemma leadingConstant_pos (N : ℕ) : 0 < leadingConstant N := by
  unfold leadingConstant
  have := moment_pos 3 (by norm_num : (0:ℝ)<1/2)
  have := rapidConstant_pos (by norm_num : (0:ℝ)<1/2) N
  positivity

lemma leading_nonneg (r t₀ d : ℝ) : 0 ≤ leading r t₀ d := by
  unfold leading
  exact mul_nonneg (by positivity) (truncatedProfile_nonneg _ _ _ _)

lemma gammaTail_le {T : ℝ} (hT : 0 ≤ T) :
    gammaTail T ≤ moment 5 (1/2) * Real.exp (-(T/2)) := by
  have hi := (moment_integrable 5 (by norm_num : (0:ℝ)<1)).mono_set
    (show Ioi T ⊆ Ioi (0:ℝ) from fun _ hs => hT.trans_lt hs)
  have hj := (moment_integrable 5 (by norm_num : (0:ℝ)<1/2)).mono_set
    (show Ioi T ⊆ Ioi (0:ℝ) from fun _ hs => hT.trans_lt hs)
  calc
    gammaTail T ≤ ∫ s : ℝ in Ioi T, (s^5 * Real.exp (-((1/2)*s))) * Real.exp (-(T/2)) := by
      apply integral_mono_ae (by simpa only [IntegrableOn, mul_comm, one_mul, mul_one] using hi)
        (hj.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have he : Real.exp (-s) ≤ Real.exp (-((1/2)*s)) * Real.exp (-(T/2)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [show T < s from hs])
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right he (pow_nonneg (hT.trans hs.le) 5)
    _ ≤ ∫ s : ℝ in Ioi 0, (s^5 * Real.exp (-((1/2)*s))) * Real.exp (-(T/2)) := by
      apply setIntegral_mono_set ((moment_integrable 5 (by norm_num : (0:ℝ)<1/2)).mul_const _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        positivity
      · exact Filter.Eventually.of_forall (fun _ hs => hT.trans_lt hs)
    _ = moment 5 (1/2) * Real.exp (-(T/2)) := by
      rw [integral_mul_const, moment_integral 5 (by norm_num : (0:ℝ)<1/2)]

lemma exp_neg_le_power {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.exp (-a) ≤ (n.factorial : ℝ) / a^n := by
  apply (le_div_iff₀ (pow_pos ha n)).mpr
  have h := (div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)).mp
    (Real.pow_div_factorial_le_exp a ha.le n)
  calc
    Real.exp (-a) * a^n ≤ Real.exp (-a) * ((n.factorial : ℝ)*Real.exp a) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using h) (Real.exp_pos _).le
    _ = (n.factorial : ℝ) := by rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

lemma gammaTail_small_scale (M : ℕ) {t₀ r : ℝ} (ht₀ : 0 < t₀) (hr : 0 < r) :
    gammaTail (t₀/r^2) ≤
      (moment 5 (1/2) * (M.factorial : ℝ) * (2/t₀)^M) * r^(2*M) := by
  have h := (gammaTail_le (div_nonneg ht₀.le (sq_nonneg r))).trans
    (mul_le_mul_of_nonneg_left
      (exp_neg_le_power (show 0 < t₀/r^2/2 by positivity) M)
      (moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le)
  calc
    _ ≤ moment 5 (1/2) * ((M.factorial : ℝ) / (t₀/r^2/2)^M) := h
    _ = _ := by
      rw [div_pow, div_pow, pow_mul, div_pow]
      field_simp

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set _root_.MeasureTheory

lemma flat_gamma_integrand {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : FlatHeat.V) :
    hodgeGammaWeight s * FlatHeat.heat (r^2*s) z =
      (4*Real.pi)⁻¹^2 * (r⁻¹)^4 * profile 3 (1/4) (‖z‖/r) s := by
  have hexp : -‖z‖^2/(4*(r^2*s)) = -(1/4 : ℝ)*(‖z‖/r)^2/s := by ring
  unfold hodgeGammaWeight FlatHeat.heat profile
  rw [hexp]
  have hcoef : s^5*(4*Real.pi*(r^2*s))⁻¹^2 = (4*Real.pi)⁻¹^2*(r⁻¹)^4*s^3 := by
    field_simp [Real.pi_ne_zero,hr.ne',hs.ne']
  calc
    _ = (s^5*(4*Real.pi*(r^2*s))⁻¹^2)*Real.exp (-s)*Real.exp (-(1/4 : ℝ)*(‖z‖/r)^2/s) := by ring
    _ = _ := by rw [hcoef]; ring

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaLinearTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open _root_.MeasureTheory
variable {ι E F : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
namespace TamingCompatibility.KernelTransfer

omit [CompleteSpace E] [CompleteSpace F] in
lemma sandwich_integrable {μ : Measure ι} {K : ι → E →L[ℝ] E} (hK : Integrable K μ)
    (L : E →L[ℝ] F) (R : F →L[ℝ] E) :
    Integrable (fun s => L ∘L K s ∘L R) μ :=
  (sandwich L R).integrable_comp hK

lemma integral_sandwich {μ : Measure ι} {K : ι → E →L[ℝ] E} (hK : Integrable K μ)
    (L : E →L[ℝ] F) (R : F →L[ℝ] E) :
    (∫ s, L ∘L K s ∘L R ∂μ) = L ∘L (∫ s, K s ∂μ) ∘L R :=
  (sandwich L R).integral_comp_comm hK
end TamingCompatibility.KernelTransfer

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol NormalJets NormalMetricCalculus Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma leadingCoordinate_gamma_integrable {r : ℝ} (hr : 0 < r) (T : ℝ)
    (ψ χ : Space → ℝ) (q z : Space) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      leadingCoordinate J α ht p D g B ψ χ (r^2*s) (q,z)) (Ioc 0 (T/r^2)) := by
  have hi := (HodgeKernelBounds.profile_integrable 3 (a := ‖z‖/r)
    (by norm_num : (0:ℝ)<1/4)).mono_set (Ioc_subset_Ioi_self : Ioc 0 (T/r^2) ⊆ Ioi 0)
  have hh : IntegrableOn (fun s : ℝ => hodgeGammaWeight s * FlatHeat.heat (r^2*s) z)
      (Ioc 0 (T/r^2)) := by
    apply (hi.const_mul ((4*Real.pi)⁻¹^2*(r⁻¹)^4)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (HodgeKernelBounds.flat_gamma_integrand hr hs.1 z).symm
  apply ((hh.const_mul (ψ q*χ z)).smul_const (normalGauge J α ht p D g B (q,z))).congr
  filter_upwards [] with s
  simp only [leadingCoordinate,smul_smul]
  congr 1
  ring

lemma leadingPatch_gamma_integrable (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    {r : ℝ} (hr : 0 < r) (T : ℝ) (ψ χ : Space → ℝ) (x : Space × Space) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ (r^2*s) x) (Ioc 0 (T/r^2)) := by
  classical
  by_cases hx : x ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).target
  · simpa only [leadingPatch,KernelExtension.push,ite_eq_left hx] using
      leadingCoordinate_gamma_integrable J α ht p D g B hr T ψ χ
        ((geometricNormalChart g B hg hB q₀ Bq hBq).symm x).1
        ((geometricNormalChart g B hg hB q₀ Bq hBq).symm x).2
  · apply (integrableOn_const (C := (0 : UnitaryFrame.W →L[ℝ] UnitaryFrame.W))
      (hs := (measure_Ioc_lt_top (μ := volume) (a := (0:ℝ)) (b := T/r^2)).ne)).congr
    filter_upwards [] with s
    apply ContinuousLinearMap.ext
    intro w
    simp [leadingPatch,KernelExtension.push,hx]

variable [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

omit [CompactSpace X] [T2Space X] in
lemma partitionLeading_gamma_integrable {r : ℝ} (hr : 0 < r) (T : ℝ)
    (p : A.centers) (x : Space × Space) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      partitionLeading J α ht A E p (r^2*s) x) (Ioc 0 (T/r^2)) :=
  leadingPatch_gamma_integrable J α ht p.val (E p).chart (E p).metricExtension
    (E p).frameExtension (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
    (E p).centerFrame (E p).centerFrame_eq hr T (coordinatePartition A p) (E p).normalCutoff x

omit [CompactSpace X] [T2Space X] in
lemma leadingMatrix_gamma_integrable {r : ℝ} (hr : 0 < r) (T : ℝ)
    (p : A.centers) (x : Space × Space) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      leadingMatrix J α ht A E p (r^2*s) x) (Ioc 0 (T/r^2)) := by
  have h := KernelTransfer.sandwich_integrable
    (partitionLeading_gamma_integrable J α ht A E hr T p x)
    (coordinateEncode J α ht A E p x.2) (coordinateDecode J α ht A E p x.1)
  change Integrable _ (volume.restrict (Ioc 0 (T/r^2)))
  simpa only [leadingMatrix,coordinateMatrix,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp] using h

omit [CompactSpace X] [T2Space X] in
lemma leadingMatrix_gamma {r : ℝ} (hr : 0 < r) (T : ℝ)
    (p : A.centers) (x : Space × Space) :
    (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
      leadingMatrix J α ht A E p (r^2*s) x) =
        coordinateMatrix J α ht A E p
          (fun x => (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
            partitionLeading J α ht A E p (r^2*s) x)) x := by
  have h := KernelTransfer.integral_sandwich
    (partitionLeading_gamma_integrable J α ht A E hr T p x)
    (coordinateEncode J α ht A E p x.2) (coordinateDecode J α ht A E p x.1)
  simp only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp] at h ⊢
  simp only [leadingMatrix,coordinateMatrix,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp,h]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
open _root_.MeasureTheory Set
open scoped Manifold
namespace TamingCompatibility.ManifoldKernelExtension
variable {E X G I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace I]

lemma push_smul (p : X) (c : ℝ) (f : E × E → G) (x : X × X) :
    push p (fun z => c • f z) x = c • push p f x := by
  classical
  unfold push
  split_ifs <;> simp

omit [NormedSpace ℝ G] in
lemma push_integrable {μ : Measure I} (p : X) (K : I → E × E → G)
    (hK : ∀ z, Integrable (fun s => K s z) μ) (x : X × X) :
    Integrable (fun s => push p (K s) x) μ := by
  classical
  by_cases hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source ×ˢ (extChartAt 𝓘(ℝ,E) p).source
  · simpa only [push,ite_eq_left hx] using hK (extChartAt 𝓘(ℝ,E) p x.1,extChartAt 𝓘(ℝ,E) p x.2)
  · simp only [push,ite_eq_right hx]
    exact integrable_zero _ _ _

lemma integral_push [CompleteSpace G] {μ : Measure I} (p : X) (K : I → E × E → G)
    (x : X × X) :
    (∫ s, push p (K s) x ∂μ) = push p (fun z => ∫ s, K s z ∂μ) x := by
  classical
  by_cases hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source ×ˢ (extChartAt 𝓘(ℝ,E) p).source
  · simp only [push,ite_eq_left hx]
  · simp only [push,ite_eq_right hx,integral_zero]
end TamingCompatibility.ManifoldKernelExtension

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

variable (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
include hE in
omit [T2Space X] in
lemma gammaPartitionLeading_support (T r : ℝ) (p : A.centers) :
    Function.support (gammaPartitionLeading J α ht A E T r p) ⊆ (E p).physicalCompact := by
  intro z hz
  by_contra h
  apply hz
  have he (s : ℝ) : partitionLeading J α ht A E p (r^2*s) z = 0 :=
    Function.notMem_support.mp (fun hz' => h
      (partitionLeading_tsupport J α ht A E hE p (r^2*s) (subset_tsupport _ hz')))
  have hz0 (s : ℝ) : hodgeGammaWeight s • partitionLeading J α ht A E p (r^2*s) z = 0 := by
    rw [he]
    ext w
    simp
  unfold gammaPartitionLeading
  simp only [hz0,integral_zero]
  ext w
  simp

omit [CompactSpace X] [T2Space X] in
lemma globalLeading_gamma_sum {r : ℝ} (hr : 0 < r) (T : ℝ) (x y : X) :
    HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y =
      ∑ p : A.centers, ManifoldKernelExtension.push p.val
        (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)) (y,x) := by
  classical
  have hi (p : A.centers) : IntegrableOn
      (fun s : ℝ => hodgeGammaWeight s • ManifoldKernelExtension.push p.val
        (leadingMatrix J α ht A E p (r^2*s)) (y,x)) (Ioc 0 (T/r^2)) := by
    change Integrable _ (volume.restrict (Ioc 0 (T/r^2)))
    simpa only [ManifoldKernelExtension.push_smul] using
      ManifoldKernelExtension.push_integrable p.val
        (fun s z => hodgeGammaWeight s • leadingMatrix J α ht A E p (r^2*s) z)
        (fun z => leadingMatrix_gamma_integrable J α ht A E hr T p z) (y,x)
  have he : (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s • globalLeading J α ht A E (r^2*s) x y) =
      ∫ s : ℝ in Ioc 0 (T/r^2), ∑ p : A.centers, hodgeGammaWeight s •
        ManifoldKernelExtension.push p.val (leadingMatrix J α ht A E p (r^2*s)) (y,x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [globalLeading,assemble,ite_eq_left (mul_pos (sq_pos_of_pos hr) hs.1),Finset.smul_sum]
  unfold HodgeKernelBounds.gammaKernel
  rw [he,integral_finsetSum _ (fun p _ => hi p),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [← ManifoldKernelExtension.push_smul]
  rw [ManifoldKernelExtension.integral_push,← ManifoldKernelExtension.push_smul]
  apply congrArg (fun K => ManifoldKernelExtension.push p.val K (y,x))
  funext z
  exact leadingMatrix_gamma J α ht A E hr T p z

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelChartGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization ManifoldKernelExtension Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal

lemma weight_of_dist_bound {Y : Type*} [PseudoMetricSpace Y] (n : ℕ)
    {t C r : ℝ} (ht : 0 < t) (hC : 1 ≤ C) (_hr : 0 ≤ r) (x y : Y)
    (hb : dist x y ≤ C*r) :
    VolterraBounds.weight n t x y ≤ C ^ n*(1+r/Real.sqrt t)^n := by
  unfold VolterraBounds.weight
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hh := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg t)
  rw [mul_div_assoc] at hh
  nlinarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

attribute [local irreducible] frameDecode unitFrameDirection

include hE in
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_direction (a : TwoForm X) (u : MetricUnit g) :
    framePairing A J α ht E a u.val.proj (unitFrameDirection A J α ht E g u) =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  have he := globalFrame_full_resolution J α ht A E hE a u.val.proj
  have hh := congrArg (fun b : MetricForms.Form Space 2 =>
    b ![u.val.2,J.endomorphism u.val.proj u.val.2]) he
  let v : A.centers → Fin 6 → MetricForms.Form Space 2 := fun p j =>
    globalFrame J α ht A E p j u.val.proj
  let c : A.centers → Fin 6 → ℝ := fun p j => (squareMass A u.val.proj)⁻¹ *
    GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) u.val.proj
  change (∑ p : A.centers, ∑ j : Fin 6, c p j • v p j)
    ![u.val.2,J.endomorphism u.val.proj u.val.2] =
    a u.val.proj ![u.val.2,J.endomorphism u.val.proj u.val.2] at hh
  simp only [ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul] at hh
  calc
    _ = ∑ p : A.centers, ∑ j : Fin 6,
        ((squareMass A u.val.proj)⁻¹ * GeometricAdjoint.pairing J α ht a
          (globalFrame J α ht A E p j) u.val.proj) *
          eval (globalFrame J α ht A E p j) u.val.proj u.val.2
            (J.endomorphism u.val.proj u.val.2) := by
      simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul,Finset.mul_sum,unitFrameDirection,mul_assoc]
    _ = _ := hh

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitDual_pairing (a : TwoForm X) (u : MetricUnit g) :
    GeometricAdjoint.pairing J α ht (unitDual A J α hs ht E hE g u).val a u.val.proj =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  rw [← framePairing_direction A J α ht E hE g a u,framePairing_apply]
  exact MetricForms.pairing_symm _ _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

include hs hE in
lemma unitFrameDirection_continuous : Continuous (unitFrameDirection A J α ht E g) := by
  apply continuous_pi
  intro i
  exact (unitEvaluation J g (globalFrame J α ht A E i.1 i.2)
    (globalFrame_smooth J α ht A E hE hs i.1 i.2)).continuous

lemma unitFrameFunctional_eq (u : MetricUnit g) :
    unitFrameFunctional A J α ht E g u =
      framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj := by
  unfold unitFrameFunctional framePairing
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  rw [unitDual_pairing A J α hs ht E hE g (globalFrame J α ht A E p j) u]
  rfl

include hs hE in
lemma unitFrameFunctional_continuous : Continuous (unitFrameFunctional A J α ht E g) := by
  have hb : Continuous (fun u : MetricUnit g => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  unfold unitFrameFunctional
  apply ((squareMass_inv_smooth A).continuous.comp hb).smul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply (p,j)).comp
    (unitFrameDirection_continuous A J α hs ht E hE g)).smul continuous_const

include hs hE in
lemma unitFrame_uniform : ∃ B : ℝ, 0 ≤ B ∧ ∀ u : MetricUnit g,
    ‖unitFrameDirection A J α ht E g u‖ ≤ B ∧ ‖unitFrameFunctional A J α ht E g u‖ ≤ B := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (unitFrameDirection_continuous A J α hs ht E hE g).continuousOn
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (unitFrameFunctional_continuous A J α hs ht E hE g).continuousOn
  refine ⟨max 0 (max B C),le_max_left _ _,fun u => ⟨?_,?_⟩⟩
  · exact (hB u (mem_univ _)).trans ((le_max_left B C).trans (le_max_right _ _))
  · exact (hC u (mem_univ _)).trans ((le_max_right B C).trans (le_max_right _ _))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

include hs hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma unitStarDirection_continuous : Continuous (unitStarDirection A J α ht E g) := by
  apply continuous_pi
  intro i
  exact (unitEvaluation J g (starTwo J α ht (globalFrame J α ht A E i.1 i.2))
    (starTwo_smooth J α hs ht (globalFrame_smooth J α ht A E hE hs i.1 i.2))).continuous

lemma unitDual_star_encode (u : MetricUnit g) :
    frameEncode J α ht A E u.val.proj
      ((preStar A J α hs ht (unitDual A J α hs ht E hE g u)).val u.val.proj) =
      unitStarDirection A J α ht E g u := by
  ext i
  rw [frameEncode_apply]
  change GeometricAdjoint.pairing J α ht
    (starTwo J α ht (unitDual A J α hs ht E hE g u).val)
    (globalFrame J α ht A E i.1 i.2) u.val.proj = _
  rw [hodgeStar_pairing]
  exact unitDual_pairing A J α hs ht E hE g
    (starTwo J α ht (globalFrame J α ht A E i.1 i.2)) u

lemma wedgeFrame_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ u v : MetricUnit g,
    ∀ K : FrameSpace A →L[ℝ] FrameSpace A,
    |framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj
      (K (frameEncode J α ht A E v.val.proj
        ((preStar A J α hs ht (unitDual A J α hs ht E hE g v)).val v.val.proj)))| ≤
        B * ‖K‖ := by
  obtain ⟨B,hB,hbound⟩ := unitFrame_uniform A J α hs ht E hE g
  obtain ⟨L,hL⟩ := isCompact_univ.exists_bound_of_continuousOn
    (unitStarDirection_continuous A J α hs ht E hE g).continuousOn
  let M := max 0 L
  have hM : 0 ≤ M := le_max_left _ _
  have hm (v : MetricUnit g) : ‖unitStarDirection A J α ht E g v‖ ≤ M :=
    (hL v (mem_univ _)).trans (le_max_right _ _)
  refine ⟨B*M,mul_nonneg hB hM,fun u v K => ?_⟩
  rw [unitDual_star_encode,← unitFrameFunctional_eq A J α hs ht E hE g]
  calc
    _ ≤ ‖unitFrameFunctional A J α ht E g u‖ * ‖K (unitStarDirection A J α ht E g v)‖ :=
      (unitFrameFunctional A J α ht E g u).le_opNorm _
    _ ≤ B * (‖K‖ * M) := mul_le_mul (hbound u).2
      ((K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hm v) (norm_nonneg _)))
      (norm_nonneg _) hB
    _ = B*M*‖K‖ := by ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {ρ : ℝ} {hρ : 0 < ρ} (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma gammaWedgeTailKernel_bound (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) :
    |C.gammaWedgeTailKernel g T hT r u v| ≤
      (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*
        ‖C.heatEvaluationVector g u‖*‖C.heatEvaluationVector g v‖ := by
  apply (abs_real_inner_le_norm _ _).trans
  have hh := mul_le_mul_of_nonneg_left
    (hodgeGammaShiftLinear_bound A J α hs ht D hD T hT r (2*ρ^2)
      (l2Star A J α hs ht (C.heatEvaluationVector g v)))
    (norm_nonneg (C.heatEvaluationVector g u))
  rw [l2Star_norm] at hh
  exact hh.trans_eq (by ring)

lemma gammaWedgeTailKernel_uniform (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, ∀ u v : MetricUnit g,
      |C.gammaWedgeTailKernel g T hT r u v| ≤ (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*B^2 := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (C.heatEvaluationVector_continuous g).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hb (u : MetricUnit g) : ‖C.heatEvaluationVector g u‖ ≤ M :=
    (hB u (mem_univ _)).trans (le_max_left _ _)
  refine ⟨M,hM,fun r u v => (C.gammaWedgeTailKernel_bound g T hT r u v).trans ?_⟩
  have htail : 0 ≤ HodgeKernelBounds.gammaTail (T/r^2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg ((div_nonneg hT (sq_nonneg r)).trans_lt hsp).le _)
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul (hb u) (hb v) (norm_nonneg _) hM)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/120) htail)
  simpa only [sq,mul_assoc] using hh

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma unitWedgeKernel_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ K : X → X → FrameSpace A →L[ℝ] FrameSpace A, ∀ u v : MetricUnit g,
      |unitWedgeKernel A J α ht E g K u v| ≤ B * ‖K u.val.proj v.val.proj‖ := by
  obtain ⟨B,hB,hbound⟩ := wedgeFrame_bound A J α hs ht E hE g
  refine ⟨B,hB,fun K u v => ?_⟩
  have h := hbound u v (K u.val.proj v.val.proj)
  rw [unitDual_star_encode,← unitFrameFunctional_eq A J α hs ht E hE g] at h
  exact h

include hE D hD in
lemma same_resolvent_wedge_quantitative (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T C : ℝ, ∃ hT : 0 < T, 0 ≤ C ∧ T ≤ 1 ∧
      (∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitWedgeKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| ≤ C/r^4 ∧
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitWedgeKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤ C/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ u v : MetricUnit g,
        S.wedgeKernel g u v =
          unitWedgeKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v +
          unitWedgeKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v +
          B.gammaWedgeTailKernel g T hT.le r u v := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,Q,hT,hT1,_,_,_,hbound,hker⟩ :=
    same_resolvent_wedge_kernel A J α hs ht E hE D hD n
  obtain ⟨B,hB,hscalar⟩ := unitWedgeKernel_bound A J α hs ht E hE g
  let a := (1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1)
  let b := (1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1)
  let C := max 0 (max (B*a) (B*b))
  have hCa : B*a ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCb : B*b ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T,C,hT,le_max_left _ _,hT1,?_,?_⟩
  · intro r hr u v
    have hw : 0 ≤ VolterraBounds.weight n (r^2) u.val.proj v.val.proj :=
      (VolterraBounds.weight_pos n (sq_pos_of_pos hr) _ _).le
    have htransfer (K : X → X → FrameSpace A →L[ℝ] FrameSpace A) (c : ℝ) (k : ℕ)
        (hk : VolterraBounds.weight n (r^2) u.val.proj v.val.proj * ‖K u.val.proj v.val.proj‖ ≤ c/r^k)
        (hc : B*c ≤ C) :
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitWedgeKernel A J α ht E g K u v| ≤ C/r^k := by
      calc
        _ ≤ VolterraBounds.weight n (r^2) u.val.proj v.val.proj * (B*‖K u.val.proj v.val.proj‖) :=
          mul_le_mul_of_nonneg_left (hscalar K u v) hw
        _ = B*(VolterraBounds.weight n (r^2) u.val.proj v.val.proj * ‖K u.val.proj v.val.proj‖) := by ring
        _ ≤ B*(c/r^k) := mul_le_mul_of_nonneg_left hk hB
        _ = (B*c)/r^k := by ring
        _ ≤ C/r^k := div_le_div_of_nonneg_right hc (pow_nonneg hr.le _)
    exact ⟨htransfer _ a 4 (hbound r hr u.val.proj v.val.proj).1 hCa,
      htransfer _ b 2 (hbound r hr u.val.proj v.val.proj).2 hCb⟩
  · intro r hr S ρ hρ R hρT u v
    have h := hker r hr S ρ hρ R hρT g u v
    rw [unitDual_star_encode,← unitFrameFunctional_eq A J α hs ht E hE g,
      _root_.add_apply,map_add] at h
    exact h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame Set
open scoped Manifold ContDiff Topology NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (E : ParametrixData J α ht p)

omit [SecondCountableTopology X] in
lemma normalMap_physical_distance :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z ∈ E.normalCompact,
      dist ((extChartAt Model p).symm (normalMap E.metricExtension E.frameExtension z.1 z.2))
        ((extChartAt Model p).symm z.1) ≤ C*‖z.2‖ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let L := Prod.fst '' E.physicalCompact ∪ Prod.snd '' E.physicalCompact
  have hL : IsCompact L := (E.physicalCompact_compact.image continuous_fst).union
    (E.physicalCompact_compact.image continuous_snd)
  have hLt : L ⊆ (extChartAt Model p).target := by
    rintro q (⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩)
    · exact E.chart.domain_subset (E.physicalCompact_domain hw).1
    · exact E.chart.domain_subset (E.physicalCompact_domain hw).2
  obtain ⟨C,hC⟩ := chartInverse_compact_lipschitz J α hs ht p L hL hLt
  obtain ⟨B,hB,hmap⟩ := normalMap_compact_bound E.metricExtension E.frameExtension
    E.metric_smooth E.frame_smooth (Metric.closedBall (extChartAt Model p p) E.radius)
    (isCompact_closedBall _ _) E.radius_pos.le
  refine ⟨max ((C:ℝ)*B) 1,le_max_right _ _,fun z hz => ?_⟩
  have hp : (z.1,normalMap E.metricExtension E.frameExtension z.1 z.2) ∈ E.physicalCompact :=
    ⟨z,hz,rfl⟩
  have hqL : z.1 ∈ L := Or.inl ⟨_,hp,rfl⟩
  have hyL : normalMap E.metricExtension E.frameExtension z.1 z.2 ∈ L := Or.inr ⟨_,hp,rfl⟩
  have hd := hC.dist_le_mul _ hyL _ hqL
  rw [dist_eq_norm] at hd
  calc
    _ ≤ (C:ℝ)*‖normalMap E.metricExtension E.frameExtension z.1 z.2-z.1‖ := hd
    _ ≤ (C:ℝ)*(B*‖z.2‖) := mul_le_mul_of_nonneg_left
      (hmap z.1 hz.1 z.2 (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2)) C.coe_nonneg
    _ ≤ max ((C:ℝ)*B) 1*‖z.2‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
lemma weighted_negative_lower {f W C L D : ℝ} (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hD : 0 < D) (hbound : W ≤ L*D) (hlower : -C/D ≤ f) : -(L*C) ≤ W*f := by
  calc
    -(L*C) = (L*D)*(-C/D) := by field_simp
    _ ≤ W*(-C/D) := mul_le_mul_of_nonpos_right hbound (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) hD.le)
    _ ≤ W*f := mul_le_mul_of_nonneg_left hlower hW

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma gammaNormalWedge_weighted_lower (p : A.centers) (N : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      -C/r^2 ≤ VolterraBounds.weight N (r^2) u.val.proj v.val.proj *
        unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
          (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
            (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
            (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,hC,hangular⟩ := gammaNormalWedge_angular A J α hs ht E hE p
  obtain ⟨L,hL,hdist⟩ := normalMap_physical_distance J α hs ht p.val (E p)
  have hLC := (HodgeKernelBounds.leadingConstant_pos (N+2)).le
  refine ⟨L^N*(C*HodgeKernelBounds.leadingConstant (N+2)),by positivity,?_⟩
  intro r hr T z hz u v hu hv
  obtain ⟨a,b,ha,hb,hbound⟩ := hangular N r hr T z hz u v hu hv
  have hp := (coordinatePartition_bounds A p z.1).1
  have hχ := (E p).normalCutoff.nonneg (x := z.2)
  have hlead := HodgeKernelBounds.leading_nonneg r T ‖z.2‖
  have hpositive : 0 ≤ (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*
      HodgeKernelBounds.leading r T ‖z.2‖)*
      ‖UnitaryFrame.line a-normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
        (UnitaryFrame.line b)‖^2 := by positivity
  have hlower : -((C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2)/(1+‖z.2‖/r)^N ≤
      unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
        (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
          (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
          (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by rw [neg_div]; linarith only [hbound,hpositive]
  have hd : dist u.val.proj v.val.proj ≤ L*‖z.2‖ := by rw [← hu,← hv]; exact hdist z hz
  have hw := weight_of_dist_bound N (sq_pos_of_pos hr) hL (norm_nonneg z.2) u.val.proj v.val.proj hd
  rw [Real.sqrt_sq hr.le] at hw
  have h := weighted_negative_lower (by positivity : 0 ≤ (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2)
    (VolterraBounds.weight_pos N (sq_pos_of_pos hr) u.val.proj v.val.proj).le
    (by positivity : 0 < (1+‖z.2‖/r)^N) hw hlower
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv,inv_pow]
  ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma gammaPatchWedge_weighted_lower (p : A.centers) (N : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      -C/r^2 ≤ VolterraBounds.weight N (r^2) u.val.proj v.val.proj *
        unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
          (ManifoldKernelExtension.push p.val
            (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p))
            (v.val.proj,u.val.proj) (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,hC,hbound⟩ := gammaNormalWedge_weighted_lower A J α hs ht E hE p N
  refine ⟨C,hC,fun r hr T u v => ?_⟩
  let e := extChartAt Model p.val
  have hneg : -C/r^2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) (sq_nonneg r)
  by_cases huv : (v.val.proj,u.val.proj) ∈ e.source ×ˢ e.source
  · dsimp only [e] at huv
    rw [ManifoldKernelExtension.push,ite_eq_left huv]
    by_cases hK : gammaPartitionLeading J α ht A E T r p (e v.val.proj,e u.val.proj) = 0
    · dsimp only [e] at hK
      simpa only [coordinateMatrix,hK,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,
        zero_apply,map_zero,mul_zero] using hneg
    · obtain ⟨z,hz,he⟩ := gammaPartitionLeading_support J α ht A E hE T r p hK
      have hq : z.1 = e v.val.proj := congrArg Prod.fst he
      have hy : normalMap (E p).metricExtension (E p).frameExtension z.1 z.2 = e u.val.proj := congrArg Prod.snd he
      have hu : e.symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj := by
        rw [hy,e.left_inv huv.2]
      have hv : e.symm z.1 = v.val.proj := by rw [hq,e.left_inv huv.1]
      have h := hbound r hr T z hz u v hu hv
      rw [hy,hq] at h
      exact h
  · dsimp only [e] at huv
    simpa only [ManifoldKernelExtension.push,ite_eq_right huv,zero_apply,map_zero,mul_zero] using hneg

include hE in
lemma globalLeadingWedge_weighted_lower (N : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      -C/r^2 ≤ VolterraBounds.weight N (r^2) u.val.proj v.val.proj *
        unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
          (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v := by
  classical
  dsimp only
  let := geometricMetricSpace J α hs ht
  choose C hC hb using fun p : A.centers => gammaPatchWedge_weighted_lower A J α hs ht E hE p N
  refine ⟨∑ p : A.centers, C p,Finset.sum_nonneg (fun p _ => hC p),fun r hr T u v => ?_⟩
  unfold unitWedgeKernel
  rw [globalLeading_gamma_sum J α ht A E hr T]
  simp only [sum_apply,map_sum,Finset.mul_sum]
  calc
    -(∑ p : A.centers, C p)/r^2 = ∑ p : A.centers, -C p/r^2 := by
      simp only [neg_div,Finset.sum_div,Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun p _ => hb p r hr T u v)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAngularPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma gammaWedgeTailKernel_rapid {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
      |C.gammaWedgeTailKernel g T hT.le r u v| ≤ B*r^(2*N) := by
  obtain ⟨M,hM,hb⟩ := C.gammaWedgeTailKernel_uniform g T hT.le
  let B := ((1/120 : ℝ)*HodgeKernelBounds.moment 5 (1/2)*(N.factorial : ℝ)*(2/T)^N)*M^2
  have hB : 0 ≤ B := by
    have hm := (HodgeKernelBounds.moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le
    dsimp [B]
    positivity
  refine ⟨B,hB,fun r hr u v => (hb r u v).trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (HodgeKernelBounds.gammaTail_small_scale N hT hr)
      (by norm_num : (0:ℝ)≤1/120)) (sq_nonneg M)
  exact hh.trans_eq (by dsimp [B] <;> ring)

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAngularPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hE in
lemma same_resolvent_wedge_point_lower (N M : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr),
        ∀ u v : MetricUnit (hermitianMetric J α hs ht),
        -(C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N-B*r^(2*M) ≤
          S.wedgeKernel (hermitianMetric J α hs ht) u v := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,C,hT,hC,_,herror,hker⟩ :=
    same_resolvent_wedge_quantitative A J α hs ht E hE D hD (hermitianMetric J α hs ht) N
  obtain ⟨L,hL,hlead⟩ := globalLeadingWedge_weighted_lower A J α hs ht E hE N
  let ρ := Real.sqrt T/2
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.mpr hT) (by norm_num)
  have hρT : 2*ρ^2 ≤ T := by
    have hsqrt := Real.sq_sqrt hT.le
    dsimp [ρ]
    nlinarith
  let R := hodgeSmoothingCover A J α hs ht D hD ρ hρ
  obtain ⟨B,hB,hBR⟩ := R.gammaWedgeTailKernel_rapid (hermitianMetric J α hs ht) hT M
  refine ⟨L+C,B,add_nonneg hL hC,hB,fun r hr S u v => ?_⟩
  have ha : 0 < 1+dist u.val.proj v.val.proj/r := by positivity
  have hw : VolterraBounds.weight N (r^2) u.val.proj v.val.proj =
      (1+dist u.val.proj v.val.proj/r)^N := by
    simp only [VolterraBounds.weight,Real.sqrt_sq_eq_abs,abs_of_pos hr]
  have hl := hlead r hr T u v
  rw [hw] at hl
  have hl' : -(L/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N ≤
      unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v := by
    rw [inv_pow,← div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos ha N)).mpr
    simpa only [neg_div,mul_comm] using hl
  have he := (herror r hr u v).2
  rw [hw] at he
  have he' : -(C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^N ≤
      unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v := by
    have habs : |unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤
        (C/r^2)/(1+dist u.val.proj v.val.proj/r)^N :=
      (le_div_iff₀ (pow_pos ha N)).mpr (by simpa only [mul_comm] using he)
    have hb := (neg_le_abs (unitWedgeKernel A J α ht E (hermitianMetric J α hs ht)
        (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v)).trans habs
    simp only [div_eq_mul_inv,inv_pow] at hb ⊢
    linarith
  have ht' := (neg_le_abs (R.gammaWedgeTailKernel (hermitianMetric J α hs ht) T hT.le r u v)).trans (hBR r hr u v)
  rw [hker r hr S ρ hρ R hρT u v]
  have hd : (L+C)/r^2 = L/r^2+C/r^2 := add_div _ _ _
  rw [hd]
  nlinarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePositiveCrossLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

lemma regularize_positive_cross_lower_of_point
    (μ ν : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr)
    (C B : ℝ)
    (hb : ∀ v u : MetricUnit (hermitianMetric J α hs ht),
      -C*(physicalProfile J α hs ht r v.val.proj u.val.proj/r^2)-B*r^2 ≤
        S.wedgeKernel (hermitianMetric J α hs ht) v u) :
    -C*(∫ v, physicalProfileMass J α hs ht μ r v.val.proj/r^2 ∂ν)-B*r^2*ν.real univ ≤
      ⟪S.regularize (hermitianMetric J α hs ht) μ,
        l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) ν)⟫ := by
  have hc := physicalProfile_unit_pair_continuous J α hs ht hr
  have hh := continuous_double_integral_lower ν μ
    (fun vu : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) => physicalProfile J α hs ht r vu.1.val.proj vu.2.val.proj/r^2)
    (fun vu => S.wedgeKernel (hermitianMetric J α hs ht) vu.1 vu.2) (hc.div_const _) (S.wedgeKernel_continuous (hermitianMetric J α hs ht)) C (B*r^2) hb
  simp_rw [integral_div] at hh
  rw [← S.regularize_wedge (hermitianMetric J α hs ht) ν μ] at hh
  rw [← l2Star_self_adjoint,real_inner_comm] at hh
  simpa only [physicalProfileMass,integral_div] using hh

include hE in
lemma same_resolvent_positive_cross_lower_oai :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (μ ν : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr),
      -C*(∫ v, physicalProfileMass J α hs ht μ r v.val.proj/r^2 ∂ν)-B*r^2*ν.real univ ≤
        ⟪S.regularize (hermitianMetric J α hs ht) μ,
          l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) ν)⟫ := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_wedge_point_lower A J α hs ht E hE D hD 6 1
  refine ⟨C,B,hC,hB,fun μ ν _ _ r hr S => ?_⟩
  apply regularize_positive_cross_lower_of_point A J α hs ht D hD μ ν r hr S C B
  intro v u
  have hh := hbound r hr S v u
  change -(C/r^2)*physicalProfile J α hs ht r v.val.proj u.val.proj-B*r^2 ≤ _ at hh
  convert hh using 1 <;> first | rfl | ring
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_positive_cross_lower_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_positive_cross_lower_oai.{u_1}
