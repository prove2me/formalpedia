-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.centeredDisplacement_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:51:38.171197+00:00
-- url     : https://prove2.me/submissions/c8cb64ad-459a-4ea3-a245-6b6a4437dfe0

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018

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

lemma christoffel_symm (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (u v : V) :
    christoffel G u v = christoffel G v u := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffel_apply, christoffelValue_inner]
  rw [hG w u v]
  ring

lemma coordinateJet_hasFDerivAt (G : MetricDerivative (V := V)) (z : V) :
    HasFDerivAt (coordinateJet G)
      (ContinuousLinearMap.id ℝ V - (1/2 : ℝ) •
        (christoffel G z + (christoffel G).flip z)) z := by
  convert! (hasFDerivAt_id z).sub
    (((christoffel G).hasFDerivAt.clm_apply (hasFDerivAt_id z)).const_smul (1/2 : ℝ)) using 1
  all_goals try with_reducible_and_instances rfl

lemma coordinateJet_hasFDerivAt_normal (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (z : V) :
    HasFDerivAt (coordinateJet G) (normalJacobian G z) z := by
  convert coordinateJet_hasFDerivAt G z using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [normalJacobian, sub_apply, smul_apply, add_apply,
    ContinuousLinearMap.flip_apply]
  rw [christoffel_symm G hG v z]
  module

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
local instance instNormedAddCommGroupMetricTensor_r2bc3f5_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensor_r2bc3f5_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
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

lemma centeredDisplacement_hasFDerivAt_oai (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    HasFDerivAt (fun u => p+B p (coordinateJet (metricJet g B p) u))
      ((B p).comp (normalJacobian (metricJet g B p) z)) z := by
  have hM : ContDiff ℝ ∞ (fun z => affineMetric g B (p,z)) :=
    (affineMetric_contDiff g B hg hB).comp (contDiff_const.prodMk contDiff_id)
  have hder : HasFDerivAt (fun z => affineMetric g B (p,z)) (metricJet g B p) 0 := by
    rw [metricJet_eq g B hg hB]
    exact (hM.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt
  have hG := metricDerivative_symmetric _ _ hder (fun z => affineMetric_symm g B hsym (p,z))
  exact ((B p).hasFDerivAt.comp z (coordinateJet_hasFDerivAt_normal _ hG z)).const_add p

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.centeredDisplacement_hasFDerivAt_oai := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.centeredDisplacement_hasFDerivAt_oai
