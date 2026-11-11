-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:52:52.804+00:00
-- url     : https://prove2.me/submissions/ab97ae29-6b55-425b-85c7-e3525a56dd94

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalJets_pullbackMetric_scalar_hasFDerivAt_zero

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricTensor
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelCLM_apply
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

lemma pullbackMetric_contDiffAt (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : ContDiffAt ℝ ∞ g 0) :
    ContDiffAt ℝ ∞ (pullbackMetric g G) 0 := by
  have hg' : ContDiffAt ℝ ∞ g (coordinateJet G 0) := by simpa using hg
  have hgc := hg'.comp (0 : V) (coordinateJet_contDiff G).contDiffAt
  have hj := (normalJacobian_contDiff G).contDiffAt (x := (0 : V))
  have hflip : ContDiff ℝ ∞ (fun h : MetricTensor (V := V) => h.flip) :=
    by
      rw [← contDiffOn_univ]
      apply contDiffOn_clm_apply.mpr
      intro v
      apply contDiffOn_clm_apply.mpr
      intro w
      change ContDiffOn ℝ ∞ (fun h : MetricTensor (V := V) => h w v) Set.univ
      exact ((contDiff_id.clm_apply contDiff_const).clm_apply contDiff_const).contDiffOn
  exact hflip.contDiffAt.comp (0 : V)
    ((hflip.contDiffAt.comp (0 : V) (hgc.clm_comp hj)).clm_comp hj)

lemma pullbackMetric_fderiv_zero (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : ContDiffAt ℝ ∞ g 0)
    (hderiv : HasFDerivAt g G 0) (hg0 : g 0 = innerSL ℝ)
    (hG : ∀ u v w, G u v w = G u w v) :
    fderiv ℝ (pullbackMetric g G) 0 = 0 := by
  have hp := ((pullbackMetric_contDiffAt g G hg).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  ext u v w
  have h := (hp.clm_apply (hasFDerivAt_const v (0 : V))).clm_apply
    (hasFDerivAt_const w (0 : V))
  have he := h.unique (pullbackMetric_scalar_hasFDerivAt_zero g G hderiv hg0 hG v w)
  have he' := congrArg (fun L : V →L[ℝ] ℝ => L u) he
  simpa using he'

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalChart
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelCLM_apply
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

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.instNormedSpaceRealContinuousLinearMapId_solutions
local instance instNormedAddCommGroupMetricTensor_r68f778_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensor_r68f778_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
omit [FiniteDimensional ℝ V] in

lemma metricDerivative_symmetric (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : HasFDerivAt g G 0)
    (hsym : ∀ z v w, g z v w = g z w v) :
    ∀ u v w, G u v w = G u w v := by
  intro u v w
  have hvw := (hg.clm_apply (hasFDerivAt_const v (0 : V))).clm_apply
    (hasFDerivAt_const w (0 : V))
  have hwv := (hg.clm_apply (hasFDerivAt_const w (0 : V))).clm_apply
    (hasFDerivAt_const v (0 : V))
  have heq : (fun z => g z v w) = (fun z => g z w v) := funext fun z => hsym z v w
  rw [heq] at hvw
  have he := congrArg (fun L : V →L[ℝ] ℝ => L u) (hvw.unique hwv)
  simpa using he

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
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

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricDerivativeSpace
lemma affineMetric_symm (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ∀ x v w, g x v w = g x w v)
    (pz : Space × Space) (v w : Space) : affineMetric g B pz v w = affineMetric g B pz w v :=
  hg _ _ _

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricDerivativeSpace
lemma metricJet_eq (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) (p : Space) :
    metricJet g B p = fderiv ℝ (fun z => affineMetric g B (p,z)) 0 :=
  UniformJets.dpos_eq _ ((affineMetric_contDiff g B hg hB).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p 0

lemma normalMetric_dpos_zero_oai (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p : Space)
    (hzero : affineMetric g B (p,0) = innerSL ℝ (E := Space)) :
    UniformJets.dpos (normalMetric g B) (p,0) = 0 := by
  rw [UniformJets.dpos_eq _ ((normalMetric_contDiff g B hg hB).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  have hM : ContDiff ℝ ∞ (fun z => affineMetric g B (p,z)) :=
    (affineMetric_contDiff g B hg hB).comp (contDiff_const.prodMk contDiff_id)
  have hder : HasFDerivAt (fun z => affineMetric g B (p,z)) (metricJet g B p) 0 := by
    rw [metricJet_eq g B hg hB]
    exact (hM.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt
  apply pullbackMetric_fderiv_zero _ _ hM.contDiffAt hder hzero
  exact metricDerivative_symmetric _ _ hder (fun z => affineMetric_symm g B hsym (p,z))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero_oai := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero_oai
