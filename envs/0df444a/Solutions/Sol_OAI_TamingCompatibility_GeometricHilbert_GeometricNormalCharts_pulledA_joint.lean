-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_joint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:09:11.893237+00:00
-- url     : https://prove2.me/submissions/95ec1257-dabd-4b25-9a3a-0bcc3cdea1bb

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018
import Definitions.Def_OAIQ239Tc019

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_3
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_3
lemma pulledA_joint_oai (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ regularSet J α ht p D g B) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun y : Space × Space => pulledA J α ht p D g B y.1 i y.2) x := by
  change ContDiffAt ℝ ∞ (fun y : Space × Space => ∑ k,
    ((normalDifferential g B y.1 y.2).inverse (EuclideanEnergy.e k) i) •
      HodgeChart.normalA J α ht p D k (normalMap g B y.1 y.2)) x
  apply ContDiffAt.sum
  intro k _
  have hinv := hx.2.contDiffAt_map_inverse.comp x (normalDifferential_joint g B hg hB).contDiffAt
  have hc := (HodgeChart.normalA_smooth J α ht p D k).contDiffAt
    (D.domain_open.mem_nhds hx.1)
  exact ((EuclideanSpace.proj i).contDiff.contDiffAt.comp x
    (hinv.clm_apply contDiffAt_const)).smul
      (hc.comp x (normalMap_joint g B hg hB).contDiffAt)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_joint_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_joint_oai.{u_1}
