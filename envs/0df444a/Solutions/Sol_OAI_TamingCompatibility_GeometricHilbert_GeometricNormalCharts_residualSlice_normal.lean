-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_normal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:22:46.61867+00:00
-- url     : https://prove2.me/submissions/95ef236e-38fa-4d03-a6d6-507f3e273a70

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_residualPatch_apply

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualSlices
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open _root_.MeasureTheory
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance residualSlicesMetricTensorNormedAddCommGroup_rcbd143_1 :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance residualSlicesMetricTensorNormedSpace_rcbd143_1 :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
omit [CompactSpace X] in
lemma residualSlice_normal_oai (p : A.centers) (q : Space) (t : ℝ) (u : W) {z : Space}
    (hz : (q,z) ∈ (E p).normalChart.source) :
    residualSlice J α ht A E p q t u (normalMap (E p).metricExtension (E p).frameExtension q z) =
      (E p).cutoffResidual J α ht q t (coordinatePartition A p q • u) z := by
  unfold residualSlice partitionResidual
  rw [residualPatch_apply J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val) (E p).centerFrame
    (E p).centerFrame_eq (coordinatePartition A p) (E p).normalCutoff t hz]
  simp only [residualCoordinate,ParametrixData.cutoffResidual,smul_apply,
    ContinuousLinearMap.comp_apply,map_smul]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_normal_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_normal_oai.{u_1}
