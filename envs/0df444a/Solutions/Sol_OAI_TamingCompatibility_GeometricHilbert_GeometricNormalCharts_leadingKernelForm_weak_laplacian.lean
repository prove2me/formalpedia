-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingKernelForm_weak_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:22:17.242196+00:00
-- url     : https://prove2.me/submissions/67269aa6-a05c-4fc8-86ee-a41025d8c9f5

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc027
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_leadingFiberForm_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_leadingSliceForm_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_leadingSliceForm_weak_deriv
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_residualFiberForm_smooth

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

variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r3d2c09_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r3d2c09_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hD in
lemma coordinatePartition_centerSupport (p : A.centers) :
    tsupport (coordinatePartition A p) ⊆ Metric.closedBall (extChartAt Model p.val p.val) (D p).radius := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := coordinatePartition_tsupport A p hq
  exact Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos])
    ((D p).source_image_subset ⟨x,hD p hx,rfl⟩)

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

omit [T2Space X] [CompactSpace X] in
lemma leadingSliceForm_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (u : W) :
    leadingSliceForm J α ht A E p q t u = 0 := by
  have hz : leadingSlice J α ht A E p q t u = 0 := by
    funext y
    simp only [leadingSlice,partitionLeading_zero_center J α ht A E p hq t y,zero_apply,Pi.zero_apply]
  funext x
  apply HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart
  rw [hz,tsupport_zero,Set.image_empty]
  exact Set.notMem_empty x

omit [T2Space X] [CompactSpace X] in
lemma residualSliceForm_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (u : W) :
    residualSliceForm J α ht A E p q t u = 0 := by
  have hz : residualSlice J α ht A E p q t u = 0 := by
    funext y
    simp only [residualSlice,partitionResidual_zero_center J α ht A E p hq t y,zero_apply,Pi.zero_apply]
  funext x
  apply HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart
  rw [hz,tsupport_zero,Set.image_empty]
  exact Set.notMem_empty x

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalSmooth
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
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeLaplacian_green (a b : PreL2 A J α hs ht true) :
    ⟪smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a),smoothL2 A J α hs ht true b⟫ =
      ⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht a),
        hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht b)⟫ :=
  hodgeLaplacian_green_weak A J α hs ht a (hodgeSmooth A J α hs ht b)

end TamingCompatibility.GeometricHilbert

end
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma smooth_energy_laplacian (a : PreL2 A J α hs ht true) (b : TwoForm X)
    (hb : IsSmooth b) :
    (∫ x, HodgeChart.energyPairing J α ht a.val b x ∂geometricVolume A J α) =
      ∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val b x
        ∂geometricVolume A J α := by
  let b' : PreL2 A J α hs ht true := ⟨b,hb⟩
  have hh := hodgeLaplacian_green A J α hs ht a b'
  rw [hodge_smooth_energy_pair A J α hs ht a b',(smoothL2 A J α hs ht true).inner_map_map,preL2_inner] at hh
  exact hh.symm

namespace GeometricNormalCharts
open HodgeNormalSymbol
variable [T2Space X]
variable (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma leadingSliceForm_weak_laplacian (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) (a : PreL2 A J α hs ht true) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingSliceForm J α ht A E p q s u) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a.val
        (residualSliceForm J α ht A E p q t u) x ∂geometricVolume A J α) -
       (∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val
        (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)) t := by
  have hh := leadingSliceForm_weak_deriv J α ht A E hE hs p hq htp u a.val a.property
  rwa [smooth_energy_laplacian A J α hs ht a _
    (leadingSliceForm_smooth J α ht A E hE hs p hq htp u)] at hh

end GeometricNormalCharts
end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma leadingSliceForm_weak_laplacian_all (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) (a : PreL2 A J α hs ht true) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingSliceForm J α ht A E p q s u) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a.val
        (residualSliceForm J α ht A E p q t u) x ∂geometricVolume A J α) -
       (∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val
        (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)) t := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact leadingSliceForm_weak_laplacian A J α hs ht E hE p hq htp u a
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    have hzero (b : TwoForm X) (x : X) : GeometricAdjoint.pairing J α ht b 0 x = 0 :=
      MetricForms.pairing_zero_right (E := Space) (GeometricAdjoint.pointMetric J α ht x) (b x)
    simp only [leadingSliceForm_zero_center J α ht A E p hz,
      residualSliceForm_zero_center J α ht A E p hz,hzero,integral_zero,sub_self]
    exact hasDerivAt_const t 0

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma pairing_zero_form (b : TwoForm X) (x : X) : GeometricAdjoint.pairing J α ht b 0 x = 0 :=
  MetricForms.pairing_zero_right (E := Space) (GeometricAdjoint.pointMetric J α ht x) (b x)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma pairing_sum_form {ι : Type*} (s : Finset ι) (b : TwoForm X) (f : ι → TwoForm X) (x : X) :
    GeometricAdjoint.pairing J α ht b (∑ i ∈ s, f i) x =
      ∑ i ∈ s, GeometricAdjoint.pairing J α ht b (f i) x := by
  change MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 (b x) _ = _
  erw [Finset.sum_apply,map_sum]
  rfl

include hs in
omit [T2Space X] in
lemma integral_pairing_sum {ι : Type*} (s : Finset ι) (b : TwoForm X) (hb : IsSmooth b)
    (f : ι → TwoForm X) (hf : ∀ i ∈ s, IsSmooth (f i)) :
    (∫ x, GeometricAdjoint.pairing J α ht b (∑ i ∈ s, f i) x ∂geometricVolume A J α) =
      ∑ i ∈ s, ∫ x, GeometricAdjoint.pairing J α ht b (f i) x ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  simp_rw [pairing_sum_form]
  apply integral_finsetSum
  intro i hi
  exact (GeometricAdjoint.pairing_two_smooth J α hs ht hb (hf i hi)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hE in
lemma leadingFiberForm_weak_laplacian (p : A.centers) (y : X)
    {t : ℝ} (htp : 0 < t) (v : FrameSpace A) (a : PreL2 A J α hs ht true) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingFiberForm J α ht A E p y s v) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a.val
        (residualFiberForm J α ht A E p y t v) x ∂geometricVolume A J α) -
       (∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val
        (leadingFiberForm J α ht A E p y t v) x ∂geometricVolume A J α)) t := by
  unfold leadingFiberForm residualFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · simp only [ite_eq_left hy]
    exact leadingSliceForm_weak_laplacian_all A J α hs ht E hE p _ htp _ a
  · simp only [ite_eq_right hy,pairing_zero_form,integral_zero,sub_self]
    exact hasDerivAt_const t 0

include hE in
lemma leadingKernelForm_weak_laplacian_oai (y : X)
    {t : ℝ} (htp : 0 < t) (v : FrameSpace A) (a : PreL2 A J α hs ht true) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingKernelForm J α ht A E s y v) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a.val
        (residualKernelForm J α ht A E t y v) x ∂geometricVolume A J α) -
       (∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val
        (leadingKernelForm J α ht A E t y v) x ∂geometricVolume A J α)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
    leadingFiberForm_weak_laplacian A J α hs ht E hE p y htp v a)
  rw [Finset.sum_sub_distrib] at hd
  have he : (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingKernelForm J α ht A E s y v) x ∂geometricVolume A J α) =ᶠ[𝓝 t]
      (fun s => ∑ p : A.centers, ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingFiberForm J α ht A E p y s v) x ∂geometricVolume A J α) := by
    filter_upwards [eventually_gt_nhds htp] with s hsp
    rw [leadingKernelForm,ite_eq_left hsp]
    exact integral_pairing_sum A J α hs ht _ a.val a.property _ (fun p _ =>
      leadingFiberForm_smooth J α ht A E hE hs p y hsp v)
  have hr := integral_pairing_sum A J α hs ht Finset.univ a.val a.property
    (fun p => residualFiberForm J α ht A E p y t v) (fun p _ =>
      residualFiberForm_smooth J α ht A E hE hs p y htp v)
  have hl := integral_pairing_sum A J α hs ht Finset.univ (hodgeLaplacian A J α hs ht a).val
    (hodgeLaplacian A J α hs ht a).property (fun p => leadingFiberForm J α ht A E p y t v)
    (fun p _ => leadingFiberForm_smooth J α ht A E hE hs p y htp v)
  rw [residualKernelForm,leadingKernelForm,ite_eq_left htp,ite_eq_left htp,hr,hl]
  exact hd.congr_of_eventuallyEq he

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingKernelForm_weak_laplacian_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingKernelForm_weak_laplacian_oai.{u_1}
