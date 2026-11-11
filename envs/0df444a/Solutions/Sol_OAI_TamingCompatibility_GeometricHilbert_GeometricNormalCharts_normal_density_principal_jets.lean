-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normal_density_principal_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:09:09.560211+00:00
-- url     : https://prove2.me/submissions/b424fb54-d896-41e4-aab3-60403e6f14b8

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalMetric_dpos_zero

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_MetricCalculus
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelCLM_apply
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
namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity
open scoped ContDiff RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedAddCommGroupMetricTensorV
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedSpaceRealMetricTensorV
lemma volumeDensity_euclidean : volumeDensity EMetric = 1 := by
  simp [volumeDensity, gram_euclidean, MetricDensity.density]

lemma volumeDensity_contDiffAt : ContDiffAt ℝ ∞ volumeDensity EMetric := by
  apply detGram_contDiff.contDiffAt.sqrt
  simp [gram_euclidean]

lemma cometric_euclidean : cometric EMetric = ContinuousLinearMap.id ℝ V := by
  rw [cometric, metricOperator_euclidean]
  exact ContinuousLinearMap.inverse_id

lemma cometric_contDiffAt : ContDiffAt ℝ ∞ cometric EMetric := by
  apply ContDiffAt.comp EMetric _ metricOperator.contDiff.contDiffAt
  rw [metricOperator_euclidean]
  exact contDiffAt_map_inverse (ContinuousLinearEquiv.refl ℝ V)

lemma principal_euclidean (i j : Fin 4) : principal EMetric i j = if i=j then 1 else 0 := by
  simp [principal, cometric_euclidean, EuclideanSpace.inner_single_left]

lemma principal_contDiffAt (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun M : MetricTensor (V := V) => principal M i j) EMetric :=
  ContDiffAt.inner ℝ (cometric_contDiffAt.clm_apply contDiffAt_const) contDiffAt_const

lemma jets (m : V → MetricTensor (V := V)) (hm : ContDiffAt ℝ ∞ m 0)
    (hm0 : m 0 = EMetric) (hd : fderiv ℝ m 0 = 0) :
    ContDiffAt ℝ ∞ (fun z => volumeDensity (m z)) 0 ∧
    volumeDensity (m 0) = 1 ∧
    fderiv ℝ (fun z => volumeDensity (m z)) 0 = 0 ∧
    (∀ i j, ContDiffAt ℝ ∞ (fun z => principal (m z) i j) 0 ∧
      principal (m 0) i j = (if i=j then 1 else 0) ∧
      fderiv ℝ (fun z => principal (m z) i j) 0 = 0) := by
  have hd' : HasFDerivAt m (0 : V →L[ℝ] MetricTensor (V := V)) 0 := by
    rw [← hd]
    exact (hm.differentiableAt (by simp)).hasFDerivAt
  have hv : ContDiffAt ℝ ∞ volumeDensity (m 0) := by rw [hm0]; exact volumeDensity_contDiffAt
  refine ⟨hv.comp 0 hm, by rw [hm0,volumeDensity_euclidean], ?_, ?_⟩
  · simpa only [Function.comp_def, ContinuousLinearMap.comp_zero] using
      ((hv.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp 0 hd').fderiv
  · intro i j
    have hp : ContDiffAt ℝ ∞ (fun M => principal M i j) (m 0) := by
      rw [hm0]; exact principal_contDiffAt i j
    refine ⟨hp.comp 0 hm, by rw [hm0,principal_euclidean], ?_⟩
    simpa only [Function.comp_def, ContinuousLinearMap.comp_zero] using
      ((hp.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp 0 hd').fderiv

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
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
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Set Metric
open scoped ContDiff
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] in
lemma dpos_eq (F : P × V → W) (hF : Differentiable ℝ F) (p : P) (z : V) :
    dpos F (p,z) = fderiv ℝ (fun u => F (p,u)) z := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (c := p) z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)
  have hh := (hF (p,z)).hasFDerivAt.comp z hd
  exact hh.fderiv.symm

end TamingCompatibility.GeometricHilbert.UniformJets

end

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_NormalDensityJacobian
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_1
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_1
lemma normal_density_principal_jets_oai (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p : Space)
    (hzero : affineMetric g B (p,0) = innerSL ℝ (E := Space)) :
    ContDiffAt ℝ ∞ (fun z => volumeDensity (normalMetric g B (p,z))) 0 ∧
    volumeDensity (normalMetric g B (p,0)) = 1 ∧
    fderiv ℝ (fun z => volumeDensity (normalMetric g B (p,z))) 0 = 0 ∧
    (∀ i j, ContDiffAt ℝ ∞ (fun z => principal (normalMetric g B (p,z)) i j) 0 ∧
      principal (normalMetric g B (p,0)) i j = (if i=j then 1 else 0) ∧
      fderiv ℝ (fun z => principal (normalMetric g B (p,z)) i j) 0 = 0) := by
  apply NormalMetricCalculus.jets
  · exact ((normalMetric_contDiff g B hg hB).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt
  · change pullbackMetric (fun z => affineMetric g B (p,z)) (metricJet g B p) 0 = _
    rw [pullbackMetric_zero]
    exact hzero
  · rw [← UniformJets.dpos_eq _ ((normalMetric_contDiff g B hg hB).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
    exact normalMetric_dpos_zero g B hg hB hsym p hzero
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normal_density_principal_jets_oai := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normal_density_principal_jets_oai
