-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:09:04.131456+00:00
-- url     : https://prove2.me/submissions/7838e8a0-c8d4-4a73-b1f1-8669ccecaca7

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc017
import Definitions.Def_OAIQ239Tc018
import Definitions.Def_OAIQ239Tc019

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedAddCommGroupMetricTensorV_1
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedSpaceRealMetricTensorV_1
lemma volumeDensity_contDiffAt_regular {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics) :
    ContDiffAt ℝ ∞ volumeDensity M :=
  detGram_contDiff.contDiffAt.sqrt (ne_of_gt hM.1)

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4
lemma normalDensity_smooth_oai (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : normalMetric g B x ∈ regularMetrics) :
    ContDiffAt ℝ ∞ (normalDensity g B) x :=
  (volumeDensity_contDiffAt_regular hx).comp x (normalMetric_contDiff g B hg hB).contDiffAt

attribute [local irreducible] normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth_oai := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth_oai
