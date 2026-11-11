-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoffResidual_zero_off
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:13:33.551475+00:00
-- url     : https://prove2.me/submissions/4e754752-48a4-4062-9dce-d538f45c6c4b

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_CutoffFamilies_residual_zero_off

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

local instance residualSlicesMetricTensorNormedAddCommGroup_r7940f7_1 :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance residualSlicesMetricTensorNormedSpace_r7940f7_1 :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
omit [CompactSpace X] in
lemma ParametrixData.cutoffResidual_zero_off_oai {p : X} (D : ParametrixData J α ht p)
    (q : Space) (t : ℝ) (u : W) {z : Space} (hz : z ∉ tsupport (D.normalCutoff : Space → ℝ)) :
    D.cutoffResidual J α ht q t u z = 0 := by
  rw [ParametrixData.cutoffResidual,CutoffFamilies.residual_zero_off _ _ _ D.normalCutoff q t hz]
  simp only [zero_apply,map_zero]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoffResidual_zero_off_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoffResidual_zero_off_oai.{u_1}
