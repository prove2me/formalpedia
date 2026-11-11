-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:26.21376+00:00
-- url     : https://prove2.me/submissions/5f7dbdeb-fa83-4b2f-83ea-4ec63b798789

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc019
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FirstJetGauge_actualSquareFirst_skew
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normal_density_principal_jets
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_weighted_principal

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

lemma normalJacobian_contDiff (G : MetricDerivative (V := V)) :
    ContDiff ℝ ∞ (normalJacobian G) := contDiff_const.sub (christoffel G).contDiff

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
lemma normalDifferential_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : ContDiff ℝ ∞ (normalDifferential g B q) :=
  contDiff_const.clm_comp (normalJacobian_contDiff _)

lemma normalInverse_contDiffAt (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) (hBq : (B q).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => (normalDifferential g B q z).inverse) 0 := by
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (normalDifferential g B q 0) := by
    rw [normalDifferential_zero]
    exact hBq.contDiffAt_map_inverse
  exact hi.comp 0 (normalDifferential_contDiff g B q).contDiffAt

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pulledA_contDiffAt (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (q : Space) (hq : q ∈ D.domain) (hBq : (B q).IsInvertible) (i : Fin 4) :
    ContDiffAt ℝ ∞ (pulledA J α ht p D g B q i) 0 := by
  change ContDiffAt ℝ ∞ (fun z => ∑ k,
    ((normalDifferential g B q z).inverse (EuclideanEnergy.e k) i) •
      HodgeChart.normalA J α ht p D k (normalMap g B q z)) 0
  apply ContDiffAt.sum
  intro k _
  have ha : ContDiffAt ℝ ∞ (HodgeChart.normalA J α ht p D k) (normalMap g B q 0) := by
    rw [normalMap_zero]
    exact (HodgeChart.normalA_smooth J α ht p D k).contDiffAt (D.domain_open.mem_nhds hq)
  exact ((EuclideanSpace.proj i).contDiff.contDiffAt.comp 0
    ((normalInverse_contDiffAt g B q hBq).clm_apply contDiffAt_const)).smul
      (ha.comp 0 (normalMap_contDiff g B q).contDiffAt)

lemma pulledB_contDiffAt (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (q : Space) (hq : q ∈ D.domain) :
    ContDiffAt ℝ ∞ (pulledB J α ht p D g B q) 0 := by
  have hb : ContDiffAt ℝ ∞ (HodgeChart.normalB J α ht p D) (normalMap g B q 0) := by
    rw [normalMap_zero]
    exact (HodgeChart.normalB_smooth J α hs ht p D).contDiffAt (D.domain_open.mem_nhds hq)
  exact hb.comp 0 (normalMap_contDiff g B q).contDiffAt

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedSpace
lemma ActualData.jets_oai (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (q : Space) (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) (hactual : ActualData J α ht p D q g B) :
      (∀ i, ContDiffAt ℝ ∞ (pulledA J α ht p D g B q i) 0) ∧
      ContDiffAt ℝ ∞ (pulledB J α ht p D g B q) 0 ∧
      (let m := fun z => normalMetric g B (q,z)
       let ρ := fun z => volumeDensity (m z)
       ContDiffAt ℝ ∞ ρ 0 ∧ ρ 0 = 1 ∧ fderiv ℝ ρ 0 = 0 ∧
       (∀ i j, ContDiffAt ℝ ∞ (fun z => principal (m z) i j) 0 ∧
         principal (m 0) i j = (if i=j then 1 else 0) ∧
         fderiv ℝ (fun z => principal (m z) i j) 0 = 0) ∧
       (∀ j, (actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
           (pulledB J α ht p D g B q) ρ j 0).adjoint =
         -actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
           (pulledB J α ht p D g B q) ρ j 0)) := by
  obtain ⟨O,hO,hqO,hOD,hgact,hBact,hsym⟩ := hactual
  have hq := hOD hqO
  have hBq : (B q).IsInvertible := by
    rw [hBact q hqO]
    exact ⟨frameEquiv _ _ (D.frame_gram q hq),rfl⟩
  have hzero : affineMetric g B (q,0) = innerSL ℝ (E := Space) := by
    simp only [affineMetric,map_zero,add_zero,hgact q hqO,hBact q hqO]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact frameMap_metric _ _ (D.frame_gram q hq) v w
  obtain ⟨hρ,hρone,hρzero,hpr⟩ := normal_density_principal_jets g B hg hB hsym q hzero
  have ha := pulledA_contDiffAt J α ht p D g B q hq hBq
  refine ⟨ha,pulledB_contDiffAt J α hs ht p D g B q hq,hρ,hρone,hρzero,hpr,?_⟩
  intro j
  exact actualSquareFirst_skew EuclideanEnergy.e _ _ _ _ 0
    (fun i => (ha i).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hρ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun i j => (hpr i j).1.differentiableAt (by simp))
    (fun i j => pulledA_weighted_principal J α ht p D g B hg hB hsym O hO hOD hgact
      q hqO hBq i j) hρzero (fun i j => (hpr i j).2.2) j

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets_oai.{u_1}
