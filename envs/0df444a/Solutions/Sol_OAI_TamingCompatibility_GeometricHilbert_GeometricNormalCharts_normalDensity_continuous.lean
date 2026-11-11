-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_continuous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:08:59.107205+00:00
-- url     : https://prove2.me/submissions/37a99a72-b568-447f-93fd-9e71778bf5ba

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixInitial
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
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialMetricTensorNormedSpace
lemma normalDensity_continuous_oai (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    Continuous (normalDensity g B) := by
  exact (detGram_contDiff.continuous.comp (normalMetric_contDiff g B hg hB).continuous).sqrt

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_continuous_oai := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_continuous_oai
