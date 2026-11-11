-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:21:48.379214+00:00
-- url     : https://prove2.me/submissions/b9b240c8-d265-4e68-9f2b-bb2aff646ae2

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc019
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_gaugedFirst_center
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalGauge_unitary
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalHeatResidual_compact_cutoff_matrix
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos

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

lemma christoffel_symm (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (u v : V) :
    christoffel G u v = christoffel G v u := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffel_apply, christoffelValue_inner]
  rw [hG w u v]
  ring

lemma christoffel_metric (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (u v w : V) :
    ⟪christoffel G u v,w⟫ + ⟪v,christoffel G u w⟫ = G u v w := by
  rw [real_inner_comm (y := v)]
  simp only [christoffel_apply, christoffelValue_inner]
  rw [hG u w v, hG w u v, hG v u w]
  ring

lemma coordinateJet_contDiff (G : MetricDerivative (V := V)) :
    ContDiff ℝ ∞ (coordinateJet G) := by
  exact contDiff_id.sub (((christoffel G).contDiff.comp contDiff_id).clm_apply
    contDiff_id |>.const_smul (1/2 : ℝ))

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

lemma normalJacobian_apply_hasFDerivAt (G : MetricDerivative (V := V)) (z v : V) :
    HasFDerivAt (fun y => normalJacobian G y v) (-(christoffel G).flip v) z := by
  exact ((christoffel G).flip v).hasFDerivAt.const_sub v

lemma pullbackMetric_scalar_hasFDerivAt_zero (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : HasFDerivAt g G 0)
    (hg0 : g 0 = innerSL ℝ) (hG : ∀ u v w, G u v w = G u w v) (v w : V) :
    HasFDerivAt (fun z => pullbackMetric g G z v w) (0 : V →L[ℝ] ℝ) 0 := by
  have hφ : HasFDerivAt (coordinateJet G) (ContinuousLinearMap.id ℝ V) 0 := by
    simpa using coordinateJet_hasFDerivAt_normal G hG 0
  have hg' : HasFDerivAt g G (coordinateJet G 0) := by simpa using hg
  have hgc := HasFDerivAt.comp (𝕜 := ℝ) (E := V) (F := V)
    (G := MetricTensor (V := V)) (f := coordinateJet G) (f' := ContinuousLinearMap.id ℝ V)
    (g := g) (g' := G) (0 : V) hg' hφ
  simp only [ContinuousLinearMap.comp_id] at hgc
  have h := (hgc.clm_apply (normalJacobian_apply_hasFDerivAt G 0 v)).clm_apply
    (normalJacobian_apply_hasFDerivAt G 0 w)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext u
  simp only [Function.comp_apply, coordinateJet_zero, normalJacobian_zero, ContinuousLinearMap.id_apply,
    hg0, ContinuousLinearMap.comp_apply, add_apply, neg_apply,
    ContinuousLinearMap.flip_apply, zero_apply]
  change 0 = ⟪v, -christoffel G u w⟫ + (⟪-christoffel G u v,w⟫ + G u v w)
  simp only [inner_neg_left, inner_neg_right]
  have hm := christoffel_metric G hG u v w
  linarith

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

lemma metricOperator_apply (M : MetricTensor (V := V)) (u : V) :
    metricOperator M u = (InnerProductSpace.toDual ℝ V).symm (M u) := rfl

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
local instance instNormedAddCommGroupMetricTensor_ra68d7c_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensor_ra68d7c_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMatrixEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy

theorem normalSymbol_adjoint_polarized (ξ η : V) :
    (normalSymbol ξ).adjoint ∘L normalSymbol η +
      (normalSymbol η).adjoint ∘L normalSymbol ξ =
      (2*⟪ξ,η⟫) • ContinuousLinearMap.id ℝ W := by
  apply ContinuousLinearMap.ext
  intro a
  apply ext_inner_left ℝ
  intro b
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.smul_apply,
    ContinuousLinearMap.id_apply,inner_smul_right,inner_add_right]
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  exact normalSymbol_polarized ξ η b a
end TamingCompatibility.HodgeNormalSymbol

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

lemma normalMetric_dpos_zero (g : Space → MetricTensor (V := Space))
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

lemma centeredDisplacement_hasFDerivAt (g : Space → MetricTensor (V := Space))
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

lemma normalMetric_eq_pullback (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    normalMetric g B (p,z) =
      (g (p+B p (coordinateJet (metricJet g B p) z))).bilinearComp
        (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z)
        (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z) := by
  rw [(centeredDisplacement_hasFDerivAt g B hg hB hsym p z).fderiv]
  ext v w
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricOperatorInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open scoped RealInnerProductSpace
open NormalJets GeometricNormalCharts
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma metricOperator_inner (M : MetricTensor (V := V)) (u v : V) :
    ⟪metricOperator M u,v⟫ = M u v := by
  simp only [metricOperator_apply, InnerProductSpace.toDual_symm_apply]

lemma cometric_eq_frame (M : MetricTensor (V := V)) (B : V ≃L[ℝ] V)
    (hB : ∀ u v, M (B u) (B v) = ⟪u,v⟫) :
    cometric M = B.toContinuousLinearMap ∘L B.toContinuousLinearMap.adjoint := by
  have hM (u v : V) : M u v = ⟪B.symm u,B.symm v⟫ := by
    simpa only [B.apply_symm_apply] using hB (B.symm u) (B.symm v)
  have hc : metricOperator M ∘L (B.toContinuousLinearMap ∘L B.toContinuousLinearMap.adjoint) =
      ContinuousLinearMap.id ℝ V := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    change ⟪metricOperator M (B (B.toContinuousLinearMap.adjoint u)),v⟫ = ⟪u,v⟫
    rw [metricOperator_inner,hM,B.symm_apply_apply,ContinuousLinearMap.adjoint_inner_left]
    change ⟪u,B (B.symm v)⟫ = _
    rw [B.apply_symm_apply]
  have hi : Function.Injective (metricOperator M) := by
    intro u v he
    have hh (w) := congrArg (fun f : V => ⟪f,w⟫) he
    simp only [metricOperator_inner,hM] at hh
    apply B.symm.injective
    apply ext_inner_right ℝ
    intro z
    simpa only [B.symm_apply_apply] using hh (B z)
  apply ContinuousLinearMap.inverse_eq hc
  apply ContinuousLinearMap.ext
  intro u
  apply hi
  have hh := congrArg (fun f : V →L[ℝ] V => f (metricOperator M u)) hc
  exact hh

lemma principal_pullback_frame (M : MetricTensor (V := V)) (B L : V ≃L[ℝ] V)
    (hB : ∀ u v, M (B u) (B v) = ⟪u,v⟫) (i j : Fin 4) :
    principal (MetricDensity.pullMetric M L.toContinuousLinearMap) i j =
      ⟪(B.toContinuousLinearMap.adjoint ∘L L.symm.toContinuousLinearMap.adjoint)
          (EuclideanSpace.basisFun (Fin 4) ℝ i),
        (B.toContinuousLinearMap.adjoint ∘L L.symm.toContinuousLinearMap.adjoint)
          (EuclideanSpace.basisFun (Fin 4) ℝ j)⟫ := by
  have hBL : ∀ u v, MetricDensity.pullMetric M L.toContinuousLinearMap
      ((B.trans L.symm) u) ((B.trans L.symm) v) = ⟪u,v⟫ := by
    intro u v
    change M (L (L.symm (B u))) (L (L.symm (B v))) = _
    simpa only [L.apply_symm_apply] using hB u v
  rw [principal,cometric_eq_frame _ (B.trans L.symm) hBL]
  change ⟪(B.trans L.symm).toContinuousLinearMap
    ((B.trans L.symm).toContinuousLinearMap.adjoint _),_⟫ = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have he : (B.trans L.symm).toContinuousLinearMap =
      L.symm.toContinuousLinearMap ∘L B.toContinuousLinearMap := rfl
  rw [he,ContinuousLinearMap.adjoint_comp]

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.CoordinateOperator
open HodgeNormalSymbol EuclideanEnergy
open scoped RealInnerProductSpace ContDiff
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma basis_expansion (v : V) : v = ∑ i, v i • e i := by
  simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e]
    using ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v).symm

lemma pullCoefficient_symbol (b : Fin 4 → V) (C : V →L[ℝ] V) (j : Fin 4) :
    pullCoefficient (HodgeFrozenEnergy.coefficient b) C j =
      normalSymbol (WithLp.toLp 2 (fun k => C (b k) j)) := by
  have hξ : (WithLp.toLp 2 (fun k => C (b k) j) : V) =
      ∑ i, (C (e i) j) • LocalMatrixOperator.frameCovector b i := by
    ext k
    change C (b k) j = _
    conv_lhs => rw [basis_expansion (b k)]
    simp [LocalMatrixOperator.frameCovector,map_sum,map_smul,
      mul_comm]
  rw [hξ]
  change _ = symbolMap _
  simp only [map_sum,map_smul,symbolMap_apply]
  rfl

lemma pullCoefficient_polarized (b : Fin 4 → V) (C : V →L[ℝ] V) (i j : Fin 4) :
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) C i).adjoint ∘L
        pullCoefficient (HodgeFrozenEnergy.coefficient b) C j +
      (pullCoefficient (HodgeFrozenEnergy.coefficient b) C j).adjoint ∘L
        pullCoefficient (HodgeFrozenEnergy.coefficient b) C i =
      (2 * ⟪(WithLp.toLp 2 (fun k => C (b k) i) : V),
        WithLp.toLp 2 (fun k => C (b k) j)⟫) • ContinuousLinearMap.id ℝ W := by
  simp only [pullCoefficient_symbol]
  exact normalSymbol_adjoint_polarized _ _

end TamingCompatibility.GeometricHilbert.CoordinateOperator


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_FirstJetGauge
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open scoped ContDiff RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma fderiv_adjoint (P : V → End (W := W)) {x : V}
    (hP : DifferentiableAt ℝ P x) (v : V) :
    fderiv ℝ (fun y => (P y).adjoint) x v = (fderiv ℝ P x v).adjoint := by
  have h := (adjointCLM.hasFDerivAt.comp x hP.hasFDerivAt).fderiv
  exact congrArg (fun f : V →L[ℝ] End (W := W) => f v) h

lemma squareFirst_skew (P' : ι → ι → End (W := W)) (a : ι → W →L[ℝ] Q)
    (b : W →L[ℝ] Q) (ρ : ℝ) (j : ι)
    (hP : ∀ i, (P' i j).adjoint = - P' i j) :
    (squareFirst P' a b ρ j).adjoint = - squareFirst P' a b ρ j := by
  simp [squareFirst, map_add, map_sub, map_smul, map_sum, hP,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  abel

end TamingCompatibility.GeometricHilbert.FirstJetGauge

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open scoped RealInnerProductSpace
open NormalJets GeometricNormalCharts CoordinateOperator HodgeNormalSymbol
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma pulled_covector (b : Fin 4 → V) (C : V →L[ℝ] V) (i : Fin 4) :
    (WithLp.toLp 2 (fun k => C (b k) i) : V) =
      (frameMap b).adjoint (C.adjoint (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,
    EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left]
  simp [frameMap_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct]

lemma pulled_principal (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (L : V ≃L[ℝ] V) (i j : Fin 4) :
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i).adjoint ∘L
      pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j +
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j).adjoint ∘L
      pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i =
      (2 * principal (MetricDensity.pullMetric g.bilinear L.toContinuousLinearMap) i j) •
        ContinuousLinearMap.id ℝ W := by
  rw [pullCoefficient_polarized,principal_pullback_frame g.bilinear (frameEquiv g b hb) L
    (frameMap_metric g b hb),pulled_covector,pulled_covector]
  rfl

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_WeightedPrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open Filter
open scoped ContDiff Topology
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma weighted_principal_jet_skew_local (P : ι → ι → V → End (W := W))
    (g : ι → ι → V → ℝ) (ρ : V → ℝ) (x v : V) (i j : ι)
    (hP : ∀ i j, DifferentiableAt ℝ (P i j) x)
    (hρ : DifferentiableAt ℝ ρ x) (hg : ∀ i j, DifferentiableAt ℝ (g i j) x)
    (hstar : (fun y => (P i j y).adjoint) =ᶠ[𝓝 x] P j i)
    (hscalar : (fun y => P i j y + P j i y) =ᶠ[𝓝 x]
      (fun y => (2*(ρ y*g i j y)) • ContinuousLinearMap.id ℝ W))
    (hρ0 : fderiv ℝ ρ x = 0) (hg0 : fderiv ℝ (g i j) x = 0) :
    (fderiv ℝ (P i j) x v).adjoint = - fderiv ℝ (P i j) x v := by
  have hadj : fderiv ℝ (P j i) x v = (fderiv ℝ (P i j) x v).adjoint := by
    rw [← fderiv_adjoint (P i j) (hP i j) v,hstar.fderiv_eq]
  have hder := ((hρ.hasFDerivAt.mul (hg i j).hasFDerivAt).const_smul (2:ℝ)).smul_const
    (ContinuousLinearMap.id ℝ W)
  have hsum := ((hP i j).hasFDerivAt.add (hP j i).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => P i j y + P j i y) x = _ at hsum
  rw [hscalar.fderiv_eq] at hsum
  have hderEq : fderiv ℝ (fun y => (2*(ρ y*g i j y)) • ContinuousLinearMap.id ℝ W) x =
      ((2:ℝ) • (ρ x • fderiv ℝ (g i j) x + g i j x • fderiv ℝ ρ x)).smulRight
        (ContinuousLinearMap.id ℝ W) := by
    simpa only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using hder.fderiv
  rw [hderEq] at hsum
  have hv := congrArg (fun f : V →L[ℝ] End (W := W) => f v) hsum
  simp [hρ0,hg0] at hv
  rw [hadj] at hv
  exact eq_neg_of_add_eq_zero_right hv.symm

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma weightedPrincipal_adjoint (a : ι → V → W →L[ℝ] Q) (ρ : V → ℝ) (i j : ι) (x : V) :
    (weightedPrincipal a ρ i j x).adjoint = weightedPrincipal a ρ j i x := by
  simp [weightedPrincipal,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma weightedPrincipal_differentiableAt (a : ι → V → W →L[ℝ] Q) (ρ : V → ℝ)
    {x : V} (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hρ : DifferentiableAt ℝ ρ x) (i j : ι) :
    DifferentiableAt ℝ (weightedPrincipal a ρ i j) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  exact ((S.differentiableAt.comp x (hρ.smul (ha i))).clm_comp (ha j))

variable [Fintype ι]

lemma actualSquareFirst_skew (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (g : ι → ι → V → ℝ) (x : V)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hρ : DifferentiableAt ℝ ρ x)
    (hg : ∀ i j, DifferentiableAt ℝ (g i j) x)
    (hscalar : ∀ i j, (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z)
      =ᶠ[𝓝 x] (fun z => (2*(ρ z*g i j z)) • ContinuousLinearMap.id ℝ W))
    (hρ0 : fderiv ℝ ρ x = 0) (hg0 : ∀ i j, fderiv ℝ (g i j) x = 0) (j : ι) :
    (actualSquareFirst e a b ρ j x).adjoint = -actualSquareFirst e a b ρ j x := by
  apply squareFirst_skew
  intro i
  exact weighted_principal_jet_skew_local (weightedPrincipal a ρ) g ρ x (e i) i j
    (weightedPrincipal_differentiableAt a ρ ha hρ) hρ hg
    (Filter.Eventually.of_forall (weightedPrincipal_adjoint a ρ i j))
    (hscalar i j) hρ0 (hg0 i j)

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_NormalDensityJacobian
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
lemma normal_density_principal_jets (g : Space → MetricTensor (V := Space))
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

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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
lemma normalMap_fderiv (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (q z : Space) :
    fderiv ℝ (normalMap g B q) z = normalDifferential g B q z :=
  (centeredDisplacement_hasFDerivAt g B hg hB hsym q z).fderiv

lemma normalDifferential_eventually_invertible (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) (hBq : (B q).IsInvertible) :
    ∀ᶠ z in 𝓝 0, (normalDifferential g B q z).IsInvertible := by
  have hmem : B q ∈ Set.range (fun e : Space ≃L[ℝ] Space => e.toContinuousLinearMap) := hBq
  have he := (normalDifferential_contDiff g B q).continuous.continuousAt (x := (0 : Space))
    ((ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := Space) (F := Space)).mem_nhds
      (by simpa using hmem))
  exact he

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

lemma pulledA_weighted_principal (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v)
    (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (hgact : ∀ x ∈ U, g x = (coordinateMetric J α ht p x).bilinear)
    (q : Space) (hq : q ∈ U) (hBq : (B q).IsInvertible) (i j : Fin 4) :
    let ρ := fun z => volumeDensity (normalMetric g B (q,z))
    let a := pulledA J α ht p D g B q
    (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z) =ᶠ[𝓝 0]
      (fun z => (2*(ρ z*principal (normalMetric g B (q,z)) i j)) •
        ContinuousLinearMap.id ℝ W) := by
  dsimp only
  have hmap : ∀ᶠ z in 𝓝 0, normalMap g B q z ∈ U :=
    (normalMap_contDiff g B q).continuous.continuousAt
      (by simpa using hU.mem_nhds hq)
  filter_upwards [hmap,normalDifferential_eventually_invertible g B q hBq] with z hz hL
  obtain ⟨L,hL⟩ := hL
  have hg' : normalMetric g B (q,z) =
      MetricDensity.pullMetric (coordinateMetric J α ht p (normalMap g B q z)).bilinear
        L.toContinuousLinearMap := by
    rw [normalMetric_eq_pullback g B hg hB hsym]
    change MetricDensity.pullMetric (g (normalMap g B q z))
      (fderiv ℝ (normalMap g B q) z) = _
    rw [normalMap_fderiv g B hg hB hsym, ←hL, hgact _ hz]
  have hp := pulled_principal (coordinateMetric J α ht p (normalMap g B q z))
    (fun k => D.frame k (normalMap g B q z))
    (D.frame_gram _ (hUD hz)) L i j
  simp only [weightedPrincipal, map_smul, ContinuousLinearMap.smul_comp]
  rw [←smul_add]
  have ha (k : Fin 4) : pulledA J α ht p D g B q k z =
      pullCoefficient (HodgeFrozenEnergy.coefficient (fun l => D.frame l (normalMap g B q z)))
        L.symm.toContinuousLinearMap k := by
    simp only [pulledA,←hL,ContinuousLinearMap.inverse_equiv]
    rfl
  rw [ha i,ha j,hp,smul_smul,hg']
  congr 1
  ring

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_FlatHeat
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open _root_.MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

lemma heat_nonneg (t : ℝ) (z : V) : 0 ≤ heat t z := by
  unfold heat
  positivity

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets

open Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma slice_fderiv_contDiffAt (F : P × V → W) {x : P × V}
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y : P × V => fderiv ℝ (fun z => F (y.1,z)) y.2) x := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    ((hF.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)).mono
      fun y hy => hy.differentiableAt (by norm_num)
  apply (dpos_contDiffAt F x hF).congr_of_eventuallyEq
  filter_upwards [hd] with y hy
  exact (dpos_eq_at F y.1 y.2 hy).symm

end TamingCompatibility.GeometricHilbert.UniformJets

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
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus

section MatrixFamilies
open UniformJets
open scoped ContDiff
variable {P V W Q ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma firstMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => firstMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) j y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      principalMatrix (fun k z => a k (y.1,z)) (fun z => ρ (y.1,z)) i j y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp (ha j)
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact (((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp (ha j))).sub
      ((S.contDiff.contDiffAt.comp x (ha j)).clm_comp hb)

lemma zeroMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : P × V => zeroMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      lowerMatrix (fun k z => a k (y.1,z)) (fun z => b (y.1,z))
        (fun z => ρ (y.1,z)) i y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp hb
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact ((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp hb)

end MatrixFamilies
open UniformJets FirstJetGauge OrthogonalJets
open scoped ContDiff
variable {P V W ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gaugeFirst_joint (e : ι → V) (a : ι → ι → P × V → ℝ)
    (b : ι → P × V → W →L[ℝ] W) (U : P × V → W →L[ℝ] W) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hU : ContDiffAt ℝ ∞ U x) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => gaugeFirst e (fun i j z => a i j (y.1,z))
      (fun j z => b j (y.1,z)) (fun z => U (y.1,z)) j y.2) x := by
  exact (adjointCLM.contDiff.contDiffAt.comp x hU).clm_comp
    (((hb j).clm_comp hU).sub (ContDiffAt.sum (fun i _ =>
      ((ha i j).add (ha j i)).smul
        ((slice_fderiv_contDiffAt U hU).clm_apply (contDiffAt_const (c := e i))))))

lemma gaugeZero_joint (e : ι → V) (a : ι → ι → P × V → ℝ)
    (b : ι → P × V → W →L[ℝ] W) (c U : P × V → W →L[ℝ] W) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ContDiffAt ℝ ∞ c x) (hU : ContDiffAt ℝ ∞ U x) :
    ContDiffAt ℝ ∞ (fun y : P × V => gaugeZero e (fun i j z => a i j (y.1,z))
      (fun j z => b j (y.1,z)) (fun z => c (y.1,z)) (fun z => U (y.1,z)) y.2) x := by
  have hdu (j : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      fderiv ℝ (fun z => U (y.1,z)) y.2 (e j)) x :=
    (slice_fderiv_contDiffAt U hU).clm_apply contDiffAt_const
  have hddu (i j : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      fderiv ℝ (fun z => fderiv ℝ (fun w => U (y.1,w)) z (e j)) y.2 (e i)) x :=
    (slice_fderiv_contDiffAt _ (hdu j)).clm_apply contDiffAt_const
  exact (adjointCLM.contDiff.contDiffAt.comp x hU).clm_comp
    (((hc.clm_comp hU).add (ContDiffAt.sum (fun i _ => (hb i).clm_comp (hdu i)))).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (ha i j).smul (hddu i j)))

lemma gauge_joint (q : ι → V →L[ℝ] ℝ) (b : ι → P → W →L[ℝ] W)
    {x : P × V} (hb : ∀ i, ContDiffAt ℝ ∞ (b i) x.1) :
    ContDiffAt ℝ ∞ (fun y : P × V => gauge (halfJet q (fun i => b i y.1)) y.2) x := by
  have he : ContDiffAt ℝ ∞ (NormedSpace.exp : (W →L[ℝ] W) → (W →L[ℝ] W))
      (halfJet q (fun i => b i x.1) x.2) := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  apply he.comp x
  simp only [halfJet, sum_apply, ContinuousLinearMap.smulRight_apply]
  exact ContDiffAt.sum fun i _ =>
    ((q i).contDiff.contDiffAt.comp x contDiffAt_snd).smul
      (((hb i).comp x contDiffAt_fst).const_smul (1/2 : ℝ))

end TamingCompatibility.GeometricHilbert.OperatorCalculus

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedAddCommGroupMetricTensorV_1
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedSpaceRealMetricTensorV_1
lemma principal_contDiffAt_regular {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (fun L => principal L i j) M :=
  ContDiffAt.inner ℝ (((hM.2.contDiffAt_map_inverse.comp M metricOperator.contDiff.contDiffAt).clm_apply
    contDiffAt_const)) contDiffAt_const

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedSpace
lemma ActualData.jets (J : AlmostComplexStructure X) (α : TwoForm X)
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
lemma normalPrincipal_smooth (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : normalMetric g B x ∈ regularMetrics) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (normalPrincipal g B i j) x :=
  (principal_contDiffAt_regular hx i j).comp x (normalMetric_contDiff g B hg hB).contDiffAt

lemma normalFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (normalFirst J α ht p D g B j) x :=
  firstMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2)) j

lemma normalZero_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalZero J α ht p D g B) x :=
  zeroMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2))

attribute [local irreducible] normalFirst

lemma normalGauge_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalGauge J α ht p D g B) x := by
  have hc : ContDiffAt ℝ ∞ (fun q : Space => (q,(0 : Space))) x.1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf (i : Fin 4) : ContDiffAt ℝ ∞
      (fun q : Space => normalFirst J α ht p D g B i (q,0)) x.1 := by
    have hi : ContDiffAt ℝ ∞ (normalFirst J α ht p D g B i) (x.1,0) :=
      normalFirst_smooth J α ht p D g B hs hg hB hx i
    exact hi.comp x.1 hc
  exact gauge_joint (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
    (fun i q => normalFirst J α ht p D g B i (q,0)) (x := x) hf

lemma gaugedFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ gaugedDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (gaugedFirst J α ht p D g B j) x :=
  gaugeFirst_joint EuclideanEnergy.e (normalPrincipal g B) (normalFirst J α ht p D g B)
    (normalGauge J α ht p D g B) (normalPrincipal_smooth g B hg hB hx.1.2)
    (normalFirst_smooth J α ht p D g B hs hg hB hx.1)
    (normalGauge_smooth J α ht p D g B hs hg hB hx.2) j

lemma gaugedZero_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ gaugedDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (gaugedZero J α ht p D g B) x :=
  gaugeZero_joint EuclideanEnergy.e (normalPrincipal g B) (normalFirst J α ht p D g B)
    (normalZero J α ht p D g B) (normalGauge J α ht p D g B)
    (normalPrincipal_smooth g B hg hB hx.1.2)
    (normalFirst_smooth J α ht p D g B hs hg hB hx.1)
    (normalZero_smooth J α ht p D g B hs hg hB hx.1)
    (normalGauge_smooth J α ht p D g B hs hg hB hx.2)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixGaussian
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
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixGaussianMetricNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixGaussianMetricNormedSpace
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)

include hg hB

attribute [local irreducible] normalGauge normalFirst

lemma normalGauge_norm_le (hs : IsSmooth α) {q : Space}
    (hactual : ActualData J α ht p D q g B) (z : Space) :
    ‖normalGauge J α ht p D g B (q,z)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [ContinuousLinearMap.norm_map_of_mem_unitary
    (normalGauge_unitary J α ht p D g B hs hg hB hactual z),one_mul]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualFamily
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff RealInnerProductSpace
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

lemma cutoff_residual_eq_zero (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) {z : V} (hz : z ∉ tsupport χ) (q : P) (t : ℝ) :
    residual (fun y => CutoffFamilies.principal a χ (q,y))
      (fun y => CutoffFamilies.first a b χ (q,y))
      (fun y => CutoffFamilies.zero a b c χ (q,y)) t z = 0 := by
  have he : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  have hd : fderiv ℝ χ z = 0 := by simpa using he.fderiv_eq (𝕜 := ℝ)
  have hdd (v : V) : fderiv ℝ (fun y => fderiv ℝ χ y v) z = 0 := by
    have he' : (fun y => fderiv ℝ χ y v) =ᶠ[𝓝 z] 0 := by
      filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
      simpa using congrArg (fun C : V →L[ℝ] ℝ => C v) hy
    simpa using he'.fderiv_eq (𝕜 := ℝ)
  simp [residual,CutoffFamilies.principal,CutoffFamilies.first,CutoffFamilies.zero,
    cutoffPrincipal,cutoffFirst,cutoffZero,he.eq_of_nhds,hd,hdd]

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

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

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalGauge normalPrincipal gaugedFirst gaugedZero

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFamilyMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFamilyMetricTensorNormedSpace
lemma residualCoordinate_support (ψ χ : Space → ℝ) (t : ℝ) :
    Function.support (residualCoordinate J α ht p D g B ψ χ t) ⊆
      Function.support ψ ×ˢ tsupport χ := by
  classical
  intro x hx
  constructor
  · intro h
    apply hx
    simp only [residualCoordinate,h,zero_smul]
  · by_contra hz
    apply hx
    rw [residualCoordinate,NormalHeatResidual.cutoff_residual_eq_zero _ _ _ χ hz]
    simp

lemma residualMatrix_gaussian (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (χ : Space → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Space)] 1)
    (K : Set Space) (hK : IsCompact K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B)
    {r : ℝ} (hr : 0 ≤ r)
    (hsub : K ×ˢ Metric.closedBall (0 : Space) r ⊆ gaugedDomain J α ht p D g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r → ∀ t : ℝ, 0 < t →
      ‖NormalHeatResidual.residual
        (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
        (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
        (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
          (gaugedZero J α ht p D g B) χ (q,y)) t z‖ ≤ C*FlatHeat.heat (2*t) z := by
  classical
  have hp (q : Space) (hq : q ∈ K) := (hactual q hq).jets J α hs ht p D q g B hg hB
  obtain ⟨C,hC,hb⟩ := NormalHeatResidual.compact_cutoff_matrix
    (normalPrincipal g B) (gaugedFirst J α ht p D g B) (gaugedZero J α ht p D g B)
    K hK hr
    (fun x hx => normalPrincipal_smooth g B hg hB (hsub hx).1.2)
    (fun x hx => gaugedFirst_smooth J α ht p D g B hs hg hB (hsub hx))
    (fun x hx => gaugedZero_smooth J α ht p D g B hs hg hB (hsub hx))
    (fun q hq i j => by
      simpa only [normalPrincipal,NormalHeatResidual.euclideanPrincipal] using ((hp q hq).2.2.2.2.2.1 i j).2.1)
    (fun q hq i j => by
      simpa only [normalPrincipal] using ((hp q hq).2.2.2.2.2.1 i j).2.2)
    (fun q hq j => gaugedFirst_center J α ht p D g B hs hg hB (hactual q hq) j) χ hχ hχ0
  exact ⟨C,hC,hb⟩

lemma norm_smul_comp_le {s K : ℝ} (hs : 0 ≤ s ∧ s ≤ 1) (U R : W →L[ℝ] W)
    (hU : ‖U‖ ≤ 1) (hR : ‖R‖ ≤ K) : ‖s • (U ∘L R)‖ ≤ K := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hR
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
  calc
    _ ≤ s * (‖U‖ * ‖R‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hs.1
    _ ≤ s * (1*K) := mul_le_mul_of_nonneg_left (mul_le_mul hU hR (norm_nonneg _) zero_le_one) hs.1
    _ ≤ K := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 hK

lemma residualCoordinate_gaussian_oai (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (ψ χ : Space → ℝ) (hψ : ∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Space)] 1)
    (K : Set Space) (hK : IsCompact K) (hψK : Function.support ψ ⊆ K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B)
    {r : ℝ} (hr : 0 ≤ r) (hχr : tsupport χ ⊆ Metric.closedBall (0 : Space) r)
    (hsub : K ×ˢ Metric.closedBall (0 : Space) r ⊆ gaugedDomain J α ht p D g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ q z : Space,
      ‖residualCoordinate J α ht p D g B ψ χ t (q,z)‖ ≤ C*FlatHeat.heat (2*t) z := by

  classical
  obtain ⟨C,hC,hb⟩ := residualMatrix_gaussian J α ht p D g B hs hg hB χ hχ hχ0
    K hK hactual hr hsub
  refine ⟨C,hC,fun t htpos q z => ?_⟩
  by_cases he : residualCoordinate J α ht p D g B ψ χ t (q,z) = 0
  · simpa only [he,norm_zero] using mul_nonneg hC (FlatHeat.heat_nonneg (2*t) z)
  have hh := residualCoordinate_support J α ht p D g B ψ χ t he
  have hqK := hψK hh.1
  have hzr : ‖z‖ ≤ r := by simpa using hχr hh.2
  exact norm_smul_comp_le (hψ q) _ _
    (normalGauge_norm_le J α ht p D g B hg hB hs (hactual q hqK) z)
    (hb q hqK z hzr t htpos)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian_oai.{u_1}
