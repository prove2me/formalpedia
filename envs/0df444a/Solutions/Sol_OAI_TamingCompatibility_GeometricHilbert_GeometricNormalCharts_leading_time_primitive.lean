-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:28.757325+00:00
-- url     : https://prove2.me/submissions/45f7ce54-332e-4082-b059-a0cf05b4d6e6

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc022
import Definitions.Def_OAIQ239Tc023
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalLeading_continuousAt
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalLeading_heatBound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalResidual_heatBound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_kernel_leading_pairing_initial
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_leadingKernelForm_weak_laplacian
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_residualPatch_joint_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_residualSlice_domain

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricTensor
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma coordinateJet_contDiff (G : MetricDerivative (V := V)) :
    ContDiff ℝ ∞ (coordinateJet G) := by
  exact contDiff_id.sub (((christoffel G).contDiff.comp contDiff_id).clm_apply
    contDiff_id |>.const_smul (1/2 : ℝ))

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_2
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_2
lemma normalMap_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : ContDiff ℝ ∞ (normalMap g B q) :=
  contDiff_const.add ((B q).contDiff.comp (coordinateJet_contDiff _))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalInverse
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedSpace
variable (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q = Bq)

lemma geometricNormalChart_symm_right {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q Bq hBq).target) :
    normalMap g B x.1 ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 := by
  have he := congrArg Prod.snd ((geometricNormalChart g B hg hB q Bq hBq).right_inv hx)
  change normalMap g B ((geometricNormalChart g B hg hB q Bq hBq).symm x).1
    ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 at he
  rw [geometricNormalChart_symm_fst g B hg hB q Bq hBq hx] at he
  exact he

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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

lemma push_apply (C : OpenPartialHomeomorph E F) (f : E → W) {x : E} (hx : x ∈ C.source) :
    push C f (C x) = f x := by
  simp [push,C.map_source hx,C.left_inv hx]

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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
lemma leadingPatch_apply (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source) :
    leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (x.1,normalMap g B x.1 x.2) =
      leadingCoordinate J α ht p D g B ψ χ t x :=
  KernelExtension.push_apply _ _ hx

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualFamily
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff RealInnerProductSpace
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

lemma cutoff_residual_eq_zero (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) {z : V} (hz : z ∉ tsupport χ) (q : P) (t : ℝ) :
    residual (fun y => CutoffFamilies.principal a χ (q,y))
      (fun y => CutoffFamilies.first a b χ (q,y))
      (fun y => CutoffFamilies.zero a b c χ (q,y)) t z = 0 := by
  have he : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  have hd : fderiv ℝ χ z = 0 := by simpa using he.fderiv_eq (𝕜 := ℝ)
  have hdd (v : V) : fderiv ℝ (fun y => fderiv ℝ χ y v) z = 0 := by
    have he' : (fun y => fderiv ℝ χ y v) =ᶠ[𝓝 z] 0 := by
      filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
      simpa using congrArg (fun C : V →L[ℝ] ℝ => C v) hy
    simpa using he'.fderiv_eq (𝕜 := ℝ)
  simp [residual,CutoffFamilies.principal,CutoffFamilies.first,CutoffFamilies.zero,
    cutoffPrincipal,cutoffFirst,cutoffZero,he.eq_of_nhds,hd,hdd]

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalGauge normalPrincipal gaugedFirst gaugedZero

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFamilyMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFamilyMetricTensorNormedSpace
lemma residualCoordinate_support (ψ χ : Space → ℝ) (t : ℝ) :
    Function.support (residualCoordinate J α ht p D g B ψ χ t) ⊆
      Function.support ψ ×ˢ tsupport χ := by
  classical
  intro x hx
  constructor
  · intro h
    apply hx
    simp only [residualCoordinate,h,zero_smul]
  · by_contra hz
    apply hx
    rw [residualCoordinate,NormalHeatResidual.cutoff_residual_eq_zero _ _ _ χ hz]
    simp

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAtlasPatches
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_rbfdd8d_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_rbfdd8d_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
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

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_rbfdd8d_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_rbfdd8d_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
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
lemma partitionResidual_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => partitionResidual J α ht A D p v.1 v.2) (t,y) :=
  residualPatch_joint_smooth J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension hs
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_smooth_compact A p).1 (D p).normalCutoff.contDiff
    (D p).normalCompact (D p).normalCompact_compact (partition_patch_support J α ht A D hD p)
    (D p).actualDomain (D p).tube htp y

include hD in
lemma partitionResidual_tsupport (p : A.centers) (t : ℝ) :
    tsupport (partitionResidual J α ht A D p t) ⊆ (D p).physicalCompact := by
  apply KernelExtension.tsupport_push_subset _ _ _ (D p).normalCompact_compact (D p).normalCompact_source
  exact (residualCoordinate_support J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    _ _ t).trans (partition_patch_support J α ht A D hD p)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixFormWeak
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_8_rbfdd8d_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_8_rbfdd8d_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma cutoff_weakSliceDomain {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius) :
    tsupport (E.normalCutoff : Space → ℝ) ⊆ E.weakSliceDomain q :=
  fun _ hz => E.tube ⟨hq,E.normalCutoff_tsupport hz⟩

lemma weakSliceDomain_actual {q z : Space} (hz : z ∈ E.weakSliceDomain q) :
    normalMap E.metricExtension E.frameExtension q z ∈ E.actualDomain := hz.2

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupMetricTensorSpace_9_rbfdd8d_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_9_rbfdd8d_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
omit [CompactSpace X] in
lemma leadingSlice_normal (p : A.centers) (q : Space) (t : ℝ) (u : W) {z : Space}
    (hz : (q,z) ∈ (E p).normalChart.source) :
    leadingSlice J α ht A E p q t u (normalMap (E p).metricExtension (E p).frameExtension q z) =
      normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension (q,z)
        ((E p).normalCutoff z • NormalHeatResidual.modelSection t (coordinatePartition A p q • u) z) := by
  unfold leadingSlice partitionLeading
  rw [leadingPatch_apply J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val) (E p).centerFrame
    (E p).centerFrame_eq (coordinatePartition A p) (E p).normalCutoff t hz]
  simp only [leadingCoordinate,smul_apply,NormalHeatResidual.modelSection,map_smul,smul_smul]
  congr 1
  ring

omit [CompactSpace X] in
lemma leadingSlice_tsupport (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (leadingSlice J α ht A E p q t u) ⊆
      normalMap (E p).metricExtension (E p).frameExtension q ''
        tsupport ((E p).normalCutoff : Space → ℝ) := by
  classical
  apply closure_minimal _
    (((E p).normalCutoff.hasCompactSupport).image
      (normalMap_contDiff (E p).metricExtension (E p).frameExtension q).continuous).isClosed
  intro y hy
  have htarget : (q,y) ∈ (E p).normalChart.target := by
    by_contra hn
    apply hy
    change (if (q,y) ∈ (E p).normalChart.target then
      leadingCoordinate J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
        (coordinatePartition A p) (E p).normalCutoff t ((E p).normalChart.symm (q,y)) else 0) u = 0
    rw [ite_eq_right hn,zero_apply]
  let z := ((E p).normalChart.symm (q,y)).2
  have hf : ((E p).normalChart.symm (q,y)).1 = q :=
    geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq htarget
  have hz : (q,z) ∈ (E p).normalChart.source := by
    have heq : (q,z) = (E p).normalChart.symm (q,y) := Prod.ext hf.symm rfl
    rw [heq]
    exact (E p).normalChart.map_target htarget
  have he : normalMap (E p).metricExtension (E p).frameExtension q z = y :=
    geometricNormalChart_symm_right (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq htarget
  refine ⟨z,?_,he⟩
  by_contra hn
  apply hy
  rw [← he,leadingSlice_normal J α ht A E p q t u hz,
    image_eq_zero_of_notMem_tsupport hn]
  simp

omit [CompactSpace X] in
lemma leadingSlice_domain (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) : tsupport (leadingSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  intro y hy
  obtain ⟨z,hz,rfl⟩ := leadingSlice_tsupport J α ht A E p q t u hy
  have hnormal : z ∈ (E p).weakSliceDomain q := (E p).cutoff_weakSliceDomain hq hz
  exact (E p).actual_subset ((E p).weakSliceDomain_actual hnormal)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchAllCenters
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [T2Space X] [CompactSpace X] in
lemma partitionLeading_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (y : Space) :
    partitionLeading J α ht A E p t (q,y) = 0 := by
  unfold partitionLeading leadingPatch KernelExtension.push
  split_ifs with hz
  · have hf := geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq hz
    simp only [leadingCoordinate,hf,hq,zero_mul]
    exact zero_smul ℝ (normalGauge J α ht p.val (E p).chart
      (E p).metricExtension (E p).frameExtension ((E p).normalChart.symm (q,y)))
  · rfl

omit [T2Space X] [CompactSpace X] in
lemma partitionResidual_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (y : Space) :
    partitionResidual J α ht A E p t (q,y) = 0 := by
  unfold partitionResidual residualPatch KernelExtension.push
  split_ifs with hz
  · have hf := geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq hz
    simp only [residualCoordinate,hf,hq,zero_smul]
  · rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCoordinateRetraction
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma coordinateEncode_smooth (hs : IsSmooth α) (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateEncode J α ht A D p) (D p).chart.domain := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_pi.mpr
  intro i
  exact (HodgeChart.rawVector_smooth J α ht p.val (D p).chart
    (globalFrame_smooth J α ht A D hD hs i.1 i.2)).inner ℝ contDiffOn_const

include hD in
lemma coordinateDecode_smooth (hs : IsSmooth α) (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateDecode J α ht A D p) (D p).chart.domain := by
  have hmass := (((squareMass_inv_smooth A).comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p.val)).contDiffOn).mono (D p).chart.domain_subset
  have hsum : ContDiffOn ℝ ∞ (fun q => ∑ i : A.centers × Fin 6,
      (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
        (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q))
      (D p).chart.domain := by
    apply ContDiffOn.sum
    intro i _
    exact contDiffOn_const.smulRight (HodgeChart.rawVector_smooth J α ht p.val (D p).chart
      (globalFrame_smooth J α ht A D hD hs i.1 i.2))
  exact hmass.smul hsum

omit [T2Space X] [CompactSpace X] in
lemma coordinateEncode_rawVector (p : A.centers) (a : TwoForm X) {q : Space}
    (hq : q ∈ (D p).chart.domain) :
    coordinateEncode J α ht A D p q (HodgeChart.rawVector J α ht p.val (D p).chart a q) =
      frameEncode J α ht A D ((extChartAt Model p.val).symm q) (a ((extChartAt Model p.val).symm q)) := by
  ext i
  change ⟪HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q,
    HodgeChart.rawVector J α ht p.val (D p).chart a q⟫ = _
  rw [real_inner_comm]
  unfold HodgeChart.rawVector
  rw [coordinates_pairing _ (by simp [Space]) _ ((D p).chart.frame_gram q hq),
    GeometricAdjoint.pairing_two_chart J α ht p.val a (globalFrame J α ht A D i.1 i.2)
      ((D p).chart.domain_subset hq)]
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGaussianSchur
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma coordinateMatrix_support (p : A.centers) (K : Space × Space → W →L[ℝ] W) :
    Function.support (coordinateMatrix J α ht A D p K) ⊆ Function.support K := by
  intro z hz hK
  apply hz
  simp only [coordinateMatrix,hK,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]

include hD in
lemma coordinateMatrix_joint_smooth (hs : IsSmooth α) (p : A.centers)
    (K : ℝ → Space × Space → W →L[ℝ] W)
    (hKs : ∀ t, Function.support (K t) ⊆ (D p).physicalCompact)
    {t : ℝ} {z : Space × Space}
    (hK : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z)) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => coordinateMatrix J α ht A D p (K v.1) v.2) (t,z) := by
  by_cases hz : z ∈ (D p).physicalCompact
  · have hd := (D p).physicalCompact_domain hz
    have he := ((coordinateEncode_smooth J α ht A D hD hs p) _ hd.2).contDiffAt
      ((D p).chart.domain_open.mem_nhds hd.2)
    have hd' := ((coordinateDecode_smooth J α ht A D hD hs p) _ hd.1).contDiffAt
      ((D p).chart.domain_open.mem_nhds hd.1)
    exact ((he.comp (t,z) contDiffAt_snd.snd).clm_comp hK).clm_comp
      (hd'.comp (t,z) contDiffAt_snd.fst)
  · apply contDiffAt_const.congr_of_eventuallyEq
    have hn : {v : ℝ × (Space × Space) | v.2 ∉ (D p).physicalCompact} ∈ 𝓝 (t,z) :=
      (continuous_snd : Continuous (Prod.snd : ℝ × (Space × Space) → Space × Space)).continuousAt (x := (t,z)) |>.preimage_mem_nhds
        ((D p).physicalCompact_compact.isClosed.isOpen_compl.mem_nhds hz)
    filter_upwards [hn] with v hv
    apply Function.notMem_support.mp
    exact fun h => hv (hKs v.1 (coordinateMatrix_support J α ht A D p (K v.1) h))

include hD in
lemma residualMatrix_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (z : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => residualMatrix J α ht A D p v.1 v.2) (t,z) :=
  coordinateMatrix_joint_smooth J α ht A D hD hs p _
    (fun t => (subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t))
    (partitionResidual_smooth J α ht A D hD hs p htp z)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldKernelExtension
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set Filter
open scoped Manifold Topology
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup G]
attribute [local instance] Classical.propDecidable
local notation "I" => 𝓘(ℝ,E)

lemma liftSet_source (p : X) (K : Set (E × E))
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    liftSet p K ⊆ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
  rintro x ⟨z,hz,rfl⟩
  exact ⟨(extChartAt I p).map_target (hK hz).1,(extChartAt I p).map_target (hK hz).2⟩

lemma liftSet_compact (p : X) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    IsCompact (liftSet p K) := by
  apply hc.image_of_continuousOn
  exact ((continuousOn_extChartAt_symm p).comp continuousOn_fst (fun z hz => (hK hz).1)).prodMk
    ((continuousOn_extChartAt_symm p).comp continuousOn_snd (fun z hz => (hK hz).2))

lemma support_push (p : X) (f : E × E → G) (K : Set (E × E))
    (hf : Function.support f ⊆ K) : Function.support (push p f) ⊆ liftSet p K := by
  intro x hx
  have hs : x ∈ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
    by_contra hh
    exact hx (by simp only [push,ite_eq_right hh])
  refine ⟨(extChartAt I p x.1,extChartAt I p x.2), hf ?_,?_⟩
  · simpa only [Function.mem_support,push,ite_eq_left hs] using hx
  · simp only [(extChartAt I p).left_inv hs.1,(extChartAt I p).left_inv hs.2]

variable [T2Space X]

lemma push_joint_continuousAt {P : Type*} [TopologicalSpace P]
    (p : X) (f : P → E × E → G) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target)
    (hf : ∀ t, Function.support (f t) ⊆ K) (t : P)
    (hcont : ∀ z, ContinuousAt (fun v : P × (E × E) => f v.1 v.2) (t,z)) (x : X × X) :
    ContinuousAt (fun v : P × (X × X) => push p (f v.1) v.2) (t,x) := by
  by_cases hx : x ∈ liftSet p K
  · have hsrc := liftSet_source p K hK hx
    have hco : ContinuousAt (fun y : X × X => (extChartAt I p y.1,extChartAt I p y.2)) x :=
      ((continuousAt_extChartAt' hsrc.1).comp continuousAt_fst).prodMk
        ((continuousAt_extChartAt' hsrc.2).comp continuousAt_snd)
    have he : (fun v : P × (X × X) => push p (f v.1) v.2) =ᶠ[𝓝 (t,x)]
        fun v => f v.1 (extChartAt I p v.2.1,extChartAt I p v.2.2) := by
      have hn : {v : P × (X × X) | v.2 ∈ (extChartAt I p).source ×ˢ (extChartAt I p).source} ∈ 𝓝 (t,x) :=
        (show ContinuousAt (Prod.snd : P × (X × X) → X × X) (t,x) from continuousAt_snd).preimage_mem_nhds
          (((show IsOpen ((extChartAt I p).source) from isOpen_extChartAt_source p).prod
            (show IsOpen ((extChartAt I p).source) from isOpen_extChartAt_source p)).mem_nhds hsrc)
      filter_upwards [hn] with v hv
      simp only [push,ite_eq_left hv]
    have hprod : ContinuousAt (fun v : P × (X × X) =>
        (v.1,(extChartAt I p v.2.1,extChartAt I p v.2.2))) (t,x) := by
      exact continuousAt_fst.prodMk (ContinuousAt.comp
        (g := fun y : X × X => (extChartAt I p y.1,extChartAt I p y.2))
        (f := Prod.snd) hco continuousAt_snd)
    have hc' : ContinuousAt (fun v : P × (X × X) => f v.1 (extChartAt I p v.2.1,extChartAt I p v.2.2)) (t,x) := by
      exact ContinuousAt.comp (g := fun v : P × (E × E) => f v.1 v.2)
        (f := fun v : P × (X × X) => (v.1,(extChartAt I p v.2.1,extChartAt I p v.2.2)))
        (hcont (extChartAt I p x.1,extChartAt I p x.2)) hprod
    exact hc'.congr_of_eventuallyEq he
  · apply continuousAt_const.congr_of_eventuallyEq
    have hn := (continuous_snd : Continuous (Prod.snd : P × (X × X) → X × X)).continuousAt (x := (t,x)) |>.preimage_mem_nhds
      ((liftSet_compact p K hc hK).isClosed.isOpen_compl.mem_nhds hx)
    filter_upwards [hn] with v hv
    exact Function.notMem_support.mp (fun h => hv (support_push p (f v.1) K (hf v.1) h))

end TamingCompatibility.ManifoldKernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalParametrix
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma physicalCompact_target (p : A.centers) :
    (D p).physicalCompact ⊆ (extChartAt Model p.val).target ×ˢ (extChartAt Model p.val).target :=
  fun _ hz => ⟨(D p).chart.domain_subset ((D p).physicalCompact_domain hz).1,
    (D p).chart.domain_subset ((D p).physicalCompact_domain hz).2⟩

omit [CompactSpace X] in
lemma assemble_continuousOn
    (K : A.centers → ℝ → Space × Space → FrameSpace A →L[ℝ] FrameSpace A)
    (hsupp : ∀ p t, Function.support (K p t) ⊆ (D p).physicalCompact)
    (hcont : ∀ p t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K p v.1 v.2) (t,z)) :
    ContinuousOn (fun v : ℝ × (X × X) => assemble A K v.1 v.2.1 v.2.2) {v | 0 < v.1} := by
  intro v hv
  apply ContinuousAt.continuousWithinAt
  have hc : ContinuousAt (fun w : ℝ × (X × X) =>
      ∑ p : A.centers, ManifoldKernelExtension.push p.val (K p w.1) (w.2.2,w.2.1)) v := by
    apply tendsto_finsetSum
    intro p _
    have hh := ManifoldKernelExtension.push_joint_continuousAt p.val (K p) (D p).physicalCompact
      (D p).physicalCompact_compact (physicalCompact_target J α ht A D p) (hsupp p) v.1
      (hcont p v.1 hv) (v.2.2,v.2.1)
    exact hh.comp (f := fun w : ℝ × (X × X) => (w.1,(w.2.2,w.2.1)))
      (continuousAt_fst.prodMk (continuousAt_snd.snd.prodMk continuousAt_snd.fst))
  apply hc.congr_of_eventuallyEq
  have hn : {w : ℝ × (X × X) | 0 < w.1} ∈ 𝓝 v :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hv
  filter_upwards [hn] with w hw
  exact ite_eq_left hw

include hD in
lemma globalResidual_continuousOn (hs : IsSmooth α) :
    ContinuousOn (fun v : ℝ × (X × X) => globalResidual J α ht A D v.1 v.2.1 v.2.2) {v | 0 < v.1} :=
  assemble_continuousOn J α ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (residualMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma frameEncode_manifoldTest (p : A.centers) (f : Space → W)
    (hfd : tsupport f ⊆ (E p).chart.domain) (x : X) :
    frameEncode J α ht A E x (HodgeChart.manifoldTest J α ht p.val (E p).chart f x) =
      if x ∈ (extChartAt Model p.val).source then
        coordinateEncode J α ht A E p (extChartAt Model p.val x) (f (extChartAt Model p.val x)) else 0 := by
  by_cases hx : x ∈ (extChartAt Model p.val).source
  · rw [ite_eq_left hx]
    by_cases hfx : extChartAt Model p.val x ∈ tsupport f
    · have hd := hfd hfx
      have hr : HodgeChart.rawVector J α ht p.val (E p).chart
          (HodgeChart.manifoldTest J α ht p.val (E p).chart f) (extChartAt Model p.val x) =
          f (extChartAt Model p.val x) := by
        unfold HodgeChart.rawVector
        rw [HodgeChart.pullback_manifoldTest J α ht p.val (E p).chart f
          ((extChartAt Model p.val).map_source hx)]
        exact coordinates_reconstruct _ _ ((E p).chart.frame_gram _ hd) _
      have hh := coordinateEncode_rawVector J α ht A E p
        (HodgeChart.manifoldTest J α ht p.val (E p).chart f) hd
      rw [hr,(extChartAt Model p.val).left_inv hx] at hh
      exact hh.symm
    · have hz := image_eq_zero_of_notMem_tsupport hfx
      erw [hz,map_zero,HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart f,map_zero]
      rintro ⟨z,hz,he⟩
      have heq : extChartAt Model p.val x = z := by
        rw [← he,(extChartAt Model p.val).right_inv ((E p).chart.domain_subset (hfd hz))]
      exact hfx (heq ▸ hz)
  · erw [ite_eq_right hx,HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart f,map_zero]
    rintro ⟨z,hz,rfl⟩
    exact hx ((extChartAt Model p.val).map_target ((E p).chart.domain_subset (hfd hz)))

include hE in
omit [T2Space X] in
lemma leadingSlice_domain_all (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (leadingSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact leadingSlice_domain J α ht A E p hq t u
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    have he : leadingSlice J α ht A E p q t u = 0 := by
      funext y
      simp only [leadingSlice,partitionLeading_zero_center J α ht A E p hz t y,zero_apply,Pi.zero_apply]
    rw [he,tsupport_zero]
    exact empty_subset _

include hE in
omit [T2Space X] in
lemma residualSlice_domain_all (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (residualSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact residualSlice_domain J α ht A E p hq t u
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    have he : residualSlice J α ht A E p q t u = 0 := by
      funext y
      simp only [residualSlice,partitionResidual_zero_center J α ht A E p hz t y,zero_apply,Pi.zero_apply]
    rw [he,tsupport_zero]
    exact empty_subset _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelForms
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [T2Space X] in
lemma leadingFiberForm_encode (p : A.centers) (y x : X) (t : ℝ) (v : FrameSpace A) :
    frameEncode J α ht A E x (leadingFiberForm J α ht A E p y t v x) =
      ManifoldKernelExtension.push p.val (leadingMatrix J α ht A E p t) (y,x) v := by
  unfold leadingFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · rw [ite_eq_left hy]
    unfold leadingSliceForm
    rw [frameEncode_manifoldTest J α ht A E p _
      (leadingSlice_domain_all J α ht A E hE p _ t _)]
    by_cases hx : x ∈ (extChartAt Model p.val).source
    · rw [ite_eq_left hx,ManifoldKernelExtension.push,ite_eq_left ⟨hy,hx⟩]
      rfl
    · rw [ite_eq_right hx,ManifoldKernelExtension.push,ite_eq_right (by simpa only [Set.mem_prod,hy,true_and] using hx)]
      rfl
  · simp only [ite_eq_right hy,Pi.zero_apply]
    erw [map_zero]
    rw [ManifoldKernelExtension.push,ite_eq_right (fun h => hy h.1)]
    rfl

include hE in
omit [T2Space X] in
lemma residualFiberForm_encode (p : A.centers) (y x : X) (t : ℝ) (v : FrameSpace A) :
    frameEncode J α ht A E x (residualFiberForm J α ht A E p y t v x) =
      ManifoldKernelExtension.push p.val (residualMatrix J α ht A E p t) (y,x) v := by
  unfold residualFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · rw [ite_eq_left hy]
    unfold residualSliceForm
    rw [frameEncode_manifoldTest J α ht A E p _
      (residualSlice_domain_all J α ht A E hE p _ t _)]
    by_cases hx : x ∈ (extChartAt Model p.val).source
    · rw [ite_eq_left hx,ManifoldKernelExtension.push,ite_eq_left ⟨hy,hx⟩]
      rfl
    · rw [ite_eq_right hx,ManifoldKernelExtension.push,ite_eq_right (by simpa only [Set.mem_prod,hy,true_and] using hx)]
      rfl
  · simp only [ite_eq_right hy,Pi.zero_apply]
    erw [map_zero]
    rw [ManifoldKernelExtension.push,ite_eq_right (fun h => hy h.1)]
    rfl

include hE in
omit [T2Space X] in
lemma leadingKernelForm_encode (t : ℝ) (y x : X) (v : FrameSpace A) :
    frameEncode J α ht A E x (leadingKernelForm J α ht A E t y v x) =
      globalLeading J α ht A E t x y v := by
  unfold leadingKernelForm globalLeading assemble
  split_ifs
  · erw [Finset.sum_apply,map_sum,_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro p _
    exact leadingFiberForm_encode J α ht A E hE p y x t v
  · exact map_zero _

include hE in
omit [T2Space X] in
lemma residualKernelForm_encode (t : ℝ) (y x : X) (v : FrameSpace A) :
    frameEncode J α ht A E x (residualKernelForm J α ht A E t y v x) =
      globalResidual J α ht A E t x y v := by
  unfold residualKernelForm globalResidual assemble
  split_ifs
  · erw [Finset.sum_apply,map_sum,_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro p _
    exact residualFiberForm_encode J α ht A E hE p y x t v
  · exact map_zero _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma framePairing_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (framePairing A J α ht E a) := by
  unfold framePairing
  apply (squareMass_inv_smooth A).continuous.smul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro j _
  exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (globalFrame_smooth J α ht A E hE hs p j)).continuous.smul continuous_const

include hs hE in
lemma framePairing_bound (a : TwoForm X) (ha : IsSmooth a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖framePairing A J α ht E a x‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (framePairing_continuous A J α hs ht E hE a ha).continuousOn
  exact ⟨max C 0,le_max_right _ _,fun x => (hC x (mem_univ x)).trans (le_max_left _ _)⟩

include hE in
omit [T2Space X] in
lemma leadingKernelForm_pairing (a : TwoForm X) (y : X) (v : FrameSpace A) (t : ℝ) (x : X) :
    GeometricAdjoint.pairing J α ht a (leadingKernelForm J α ht A E t y v) x =
      framePairing A J α ht E a x (globalLeading J α ht A E t x y v) := by
  rw [← leadingKernelForm_encode J α ht A E hE]
  rw [framePairing_apply]
  unfold GeometricAdjoint.pairing
  dsimp only
  erw [frameDecode_encode J α ht A E hE]

include hE in
omit [T2Space X] in
lemma residualKernelForm_pairing (a : TwoForm X) (y : X) (v : FrameSpace A) (t : ℝ) (x : X) :
    GeometricAdjoint.pairing J α ht a (residualKernelForm J α ht A E t y v) x =
      framePairing A J α ht E a x (globalResidual J α ht A E t x y v) := by
  rw [← residualKernelForm_encode J α ht A E hE]
  rw [framePairing_apply]
  unfold GeometricAdjoint.pairing
  dsimp only
  erw [frameDecode_encode J α ht A E hE]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] Classical.propDecidable

include hs hE in
lemma globalResidual_continuousAt {t : ℝ} (htp : 0 < t) (x y : X) :
    ContinuousAt (fun v : ℝ × (X × X) => globalResidual J α ht A E v.1 v.2.1 v.2.2) (t,(x,y)) :=
  (globalResidual_continuousOn J α ht A E hE hs).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds htp)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelWeakAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma kernel_pairing_integral_continuousOn
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : ∀ t, 0 < t → ∀ x y, ContinuousAt
      (fun z : ℝ × (X × X) => K z.1 z.2.1 z.2.2) (t,(x,y)))
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    ContinuousOn (fun z : ℝ × X => ∫ x, framePairing A J α ht E a x
      (K z.1 x z.2 (v z.2)) ∂geometricVolume A J α) {z | 0 < z.1} := by
  let := geometricVolume_finite A J α hs ht
  apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
  · intro z hz
    have hk := (hK z.1.1 hz.1 z.2 z.1.2).comp
      (f := fun w : (ℝ × X) × X => (w.1.1,(w.2,w.1.2)))
      (continuousAt_fst.fst.prodMk (continuousAt_snd.prodMk continuousAt_fst.snd))
    have hφ : ContinuousAt (fun w : (ℝ × X) × X => framePairing A J α ht E a w.2) z :=
      (framePairing_continuous A J α hs ht E hE a ha).continuousAt.comp
      (f := fun w : (ℝ × X) × X => w.2) continuousAt_snd
    exact (hφ.clm_apply (hk.clm_apply (hv.continuousAt.comp continuousAt_fst.snd))).continuousWithinAt
  · intro _ x _ hx
    exact (hx (mem_univ x)).elim

include hE in
lemma kernel_leading_pairing_hasDerivAt (y : X) (v : FrameSpace A)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) :
    HasDerivAt (fun s => ∫ x, framePairing A J α ht E a.val x
        (globalLeading J α ht A E s x y v) ∂geometricVolume A J α)
      ((∫ x, framePairing A J α ht E a.val x
        (globalResidual J α ht A E t x y v) ∂geometricVolume A J α) -
       (∫ x, framePairing A J α ht E (hodgeLaplacian A J α hs ht a).val x
        (globalLeading J α ht A E t x y v) ∂geometricVolume A J α)) t := by
  have hh := leadingKernelForm_weak_laplacian A J α hs ht E hE y htp v a
  simp_rw [leadingKernelForm_pairing A J α ht E hE,
    residualKernelForm_pairing A J α ht E hE] at hh
  exact hh

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeInputInitial
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] [BorelSpace X] in
lemma kernel_pairing_integral_bound (a : TwoForm X) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ x, ‖framePairing A J α ht E a x‖ ≤ C)
    (K : X → FrameSpace A →L[ℝ] FrameSpace A) (v : FrameSpace A) {H : ℝ}
    (hKi : Integrable (fun x => ‖K x‖) (geometricVolume A J α))
    (hKb : (∫ x, ‖K x‖ ∂geometricVolume A J α) ≤ H) :
    ‖∫ x, framePairing A J α ht E a x (K x v) ∂geometricVolume A J α‖ ≤ C*‖v‖*H := by
  calc
    _ ≤ ∫ x, (C*‖v‖)*‖K x‖ ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (hKi.const_mul _) (Filter.Eventually.of_forall _)
      intro x
      calc
        _ ≤ ‖framePairing A J α ht E a x‖*‖K x v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C*(‖K x‖*‖v‖) := mul_le_mul (hφ x) (ContinuousLinearMap.le_opNorm _ _)
          (norm_nonneg _) hC
        _ = _ := by ring
    _ = (C*‖v‖)*(∫ x, ‖K x‖ ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hKb (mul_nonneg hC (norm_nonneg _))

attribute [local irreducible] framePairing globalLeading globalResidual

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma kernelTestSlice_continuousOn
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : ∀ t, 0 < t → ∀ x y, ContinuousAt (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2) (t,x,y))
    (y : X) (v : FrameSpace A) (a : TwoForm X) (ha : IsSmooth a) :
    ContinuousOn (kernelTestSlice A J α ht E K y v a) (Ioi 0) := by
  have hh := kernel_pairing_integral_continuousOn A J α hs ht E hE K hK
    (fun _ => v) continuous_const a ha
  apply hh.comp (continuous_id.prodMk continuous_const).continuousOn
  exact fun _ hp => hp

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma kernelTestSlice_uniform_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H : ℝ}
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 1 H K)
    (a : TwoForm X) (ha : IsSmooth a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 1, ∀ y v,
      ‖kernelTestSlice A J α ht E K y v a t‖ ≤ C*‖v‖ := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  refine ⟨B*H,mul_nonneg hB hK.nonneg,?_⟩
  intro t hp y v
  have hi := hK.col_int t hp y
  have hb := hK.col t hp y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
  exact (kernel_pairing_integral_bound A J α ht E a hB hφ _ v hi hb).trans_eq (by ring)

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma leading_time_primitive_oai (y : X) (v : FrameSpace A)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in (0:ℝ)..t,
      kernelTestSlice A J α ht E (globalResidual J α ht A E) y v a.val s -
      kernelTestSlice A J α ht E (globalLeading J α ht A E) y v
        (hodgeLaplacian A J α hs ht a).val s) =
    kernelTestSlice A J α ht E (globalLeading J α ht A E) y v a.val t -
      framePairing A J α ht E a.val y v := by
  let := geometricMetricSpace J α hs ht
  let F := kernelTestSlice A J α ht E (globalLeading J α ht A E) y v a.val
  let G := fun s => kernelTestSlice A J α ht E (globalResidual J α ht A E) y v a.val s -
    kernelTestSlice A J α ht E (globalLeading J α ht A E) y v
      (hodgeLaplacian A J α hs ht a).val s
  have hd (s : ℝ) (hp : 0 < s) : HasDerivAt F (G s) s :=
    kernel_leading_pairing_hasDerivAt A J α hs ht E hE y v a hp
  have hc : ContinuousOn G (Ioi 0) :=
    (kernelTestSlice_continuousOn A J α hs ht E hE _
      (fun _ hp x y => globalResidual_continuousAt A J α hs ht E hE hp x y) y v a.val a.property).sub
    (kernelTestSlice_continuousOn A J α hs ht E hE _
      (fun _ hp x y => globalLeading_continuousAt A J α hs ht E hE hp x y) y v
      (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property)
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  obtain ⟨B,hB,hRb⟩ := kernelTestSlice_uniform_bound A J α hs ht E hE _ hR a.val a.property
  obtain ⟨C,hC,hLb⟩ := kernelTestSlice_uniform_bound A J α hs ht E hE _ hL
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property
  have hi : IntervalIntegrable G volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le htp.le).mpr
    apply IntegrableOn.of_bound (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ((hc.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo)
      ((B+C)*‖v‖)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs'
    have hp : s ∈ Ioc 0 1 := ⟨hs'.1,hs'.2.le.trans ht1⟩
    exact (norm_sub_le _ _).trans ((add_le_add (hRb s hp y v) (hLb s hp y v)).trans_eq (by ring))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto htp
    (fun s hp => hd s hp.1) hi
    (kernel_leading_pairing_initial A J α hs ht E hE y v a.val a.property)
    ((hd t htp).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive_oai.{u_1}
