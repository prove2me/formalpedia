-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:19:11.689949+00:00
-- url     : https://prove2.me/submissions/6e2b743f-0e3b-4b2a-80d4-3ae40c8a3d2b

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc026
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos

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

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_MetricCalculus
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
local instance instNormedAddCommGroupMetricTensor_r1ff684_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensor_r1ff684_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_NormalDensityJacobian
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
lemma normal_density_jacobian (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    volumeDensity (normalMetric g B (p,z)) =
      |LinearMap.det (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z).toLinearMap| *
      volumeDensity (g (p+B p (coordinateJet (metricJet g B p) z))) := by
  rw [normalMetric_eq_pullback g B hg hB hsym]
  exact MetricDensity.density_pullMetric (stdOrthonormalBasis ℝ Space).toBasis _ _

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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

end MatrixFamilies
open UniformJets FirstJetGauge OrthogonalJets
open scoped ContDiff
variable {P V W ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

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

lemma gaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ z : V, Real.exp (-b*‖z‖^2)) = (Real.pi/b)^2 := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) hb
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, show (4:ℝ)/2 = 2 by norm_num,
    Real.rpow_natCast] at h
  simpa only [Real.rpow_ofNat] using h

lemma heat_integral {t : ℝ} (ht : 0 < t) : (∫ z : V, heat t z) = 1 := by
  have he : heat t = fun z : V => (4*Real.pi*t)⁻¹^2 * Real.exp (-(1/(4*t))*‖z‖^2) := by
    funext z
    unfold heat
    congr 2
    ring
  rw [he, integral_const_mul, gaussian_integral (by positivity)]
  field_simp

lemma heat_scale {r : ℝ} (hr : 0 < r) (t : ℝ) (z : V) :
    heat (r^2*t) (r • z) = (r⁻¹)^4 * heat t z := by
  simp only [heat, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  have he : -(r^2*‖z‖^2)/(4*(r^2*t)) = -‖z‖^2/(4*t) := by field_simp
  rw [he]
  ring

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatJointSmooth
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open scoped ContDiff

lemma heat_joint_contDiffAt {x : ℝ × V} (hx : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun v : ℝ × V => heat v.1 v.2) x := by
  have hp : ContDiffAt ℝ ∞ (fun v : ℝ × V => 4*Real.pi*v.1) x :=
    contDiffAt_const.mul contDiffAt_fst
  have hi : ContDiffAt ℝ ∞ (fun v : ℝ × V => (4*Real.pi*v.1)⁻¹^2) x :=
    (hp.inv (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx)).pow 2
  have hn : ContDiffAt ℝ ∞ (fun v : ℝ × V => -‖v.2‖^2) x :=
    (contDiffAt_snd.norm_sq (𝕜 := ℝ)).neg
  have he : ContDiffAt ℝ ∞ (fun v : ℝ × V => -‖v.2‖^2/(4*v.1)) x :=
    hn.div (contDiffAt_const.mul contDiffAt_fst) (mul_ne_zero (by norm_num) hx)
  exact hi.mul he.exp

end TamingCompatibility.GeometricHilbert.FlatHeat

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeApproximateIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open _root_.MeasureTheory Set Filter Bornology
open scoped Topology

lemma heat_decay : Tendsto (fun z : V => ‖z‖^4 * heat 1 z) (cobounded V) (𝓝 0) := by
  have hsq : Tendsto (fun z : V => ‖z‖^2) (cobounded V) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1/4) (by norm_num)).comp hsq
  have h' := h.const_mul ((4*Real.pi)⁻¹^2)
  simp only [mul_zero] at h'
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply,Real.rpow_ofNat,heat,mul_one]
  rw [show -(1/4 : ℝ)*‖z‖^2 = -‖z‖^2/4 by ring]
  ring

lemma heat_scale_inverse_sqrt {t : ℝ} (ht : 0 < t) (z : V) :
    (Real.sqrt t)⁻¹^4 * heat 1 ((Real.sqrt t)⁻¹ • z) = heat t z := by
  have hr := Real.sqrt_pos.2 ht
  have he := heat_scale hr 1 ((Real.sqrt t)⁻¹ • z)
  simpa only [Real.sq_sqrt ht.le,mul_one,smul_smul,mul_inv_cancel₀ (ne_of_gt hr),one_smul] using he.symm

lemma heat_approximate_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : V → E) (hf : Integrable f) (hfc : ContinuousAt f 0) :
    Tendsto (fun t : ℝ => ∫ z : V, heat t z • f z) (𝓝[>] 0) (𝓝 (f 0)) := by
  have hd : Tendsto (fun z : V => ‖z‖^(Module.finrank ℝ V) * heat 1 z)
      (cobounded V) (𝓝 0) := by simpa using heat_decay
  have h := tendsto_integral_comp_smul_smul_of_integrable
    (fun z => heat_nonneg 1 z) (heat_integral zero_lt_one) hd hf hfc
  have hc : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) (𝓝[>] 0) atTop := by
    simpa only [Function.comp_def,Real.sqrt_inv] using Real.tendsto_sqrt_atTop.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  have h' := h.comp hc
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  dsimp only [Function.comp_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  simpa using heat_scale_inverse_sqrt ht z

end TamingCompatibility.GeometricHilbert.FlatHeat

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open Set Filter
open scoped Manifold ContDiff Topology
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma exists_compact_smooth_extension {U K : Set V} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : V → W} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : V → W, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨O,hO,hKO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hKi : K ⊆ interior (closure O) := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hO.mem_nhds (hKO hx)) subset_closure)
  obtain ⟨φ,hφone,hφzero,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,V)) hK.isClosed hKi (n := ⊤)
  have hφsupp : tsupport (φ : V → ℝ) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (hφzero x hn)
  have hgsub : tsupport (fun x => φ x • f x) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (by simp [hφzero x hn])
  refine ⟨fun x => φ x • f x,SchwartzCutoff.smooth hU hf
    (contMDiff_iff_contDiff.mp φ.contMDiff) (hφsupp.trans hOU),
    hOc.of_isClosed_subset (isClosed_tsupport _) hgsub,hgsub.trans hOU,?_⟩
  intro x hx
  filter_upwards [hφone.filter_mono (nhds_le_nhdsSet hx)] with y hy
  simp [hy]

end TamingCompatibility.GeometricHilbert.OperatorCalculus

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

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4
lemma normalFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (normalFirst J α ht p D g B j) x :=
  firstMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2)) j

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

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalInverse
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedSpace
variable (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q = Bq)

lemma geometricNormalChart_symm_right {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q Bq hBq).target) :
    normalMap g B x.1 ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 := by
  have he := congrArg Prod.snd ((geometricNormalChart g B hg hB q Bq hBq).right_inv hx)
  change normalMap g B ((geometricNormalChart g B hg hB q Bq hBq).symm x).1
    ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 at he
  rw [geometricNormalChart_symm_fst g B hg hB q Bq hBq hx] at he
  exact he

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {E F W : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup W]
attribute [local instance] Classical.propDecidable

lemma push_apply (C : OpenPartialHomeomorph E F) (f : E → W) {x : E} (hx : x ∈ C.source) :
    push C f (C x) = f x := by
  simp [push,C.map_source hx,C.left_inv hx]

lemma support_push_subset (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hf : Function.support f ⊆ K) : Function.support (push C f) ⊆ C '' K := by
  intro y hy
  have ht : y ∈ C.target := by
    by_contra h
    exact hy (by simp [push,h])
  refine ⟨C.symm y,hf ?_,C.right_inv ht⟩
  simpa [Function.mem_support,push,ht] using hy

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {P E F W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] Classical.propDecidable

lemma push_family_contDiffAt (C : OpenPartialHomeomorph E F) (f : P → E → W) (K : Set E)
    (hK : IsCompact K) (hKC : K ⊆ C.source) (hfK : ∀ p, Function.support (f p) ⊆ K)
    {p : P} (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ (fun v : P × E => f v.1 v.2) (p,x))
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ (C.symm : F → E) (C x)) (y : F) :
    ContDiffAt ℝ ∞ (fun v : P × F => push C (f v.1) v.2) (p,y) := by
  by_cases hy : y ∈ C '' K
  · obtain ⟨x,hx,rfl⟩ := hy
    have ht := C.map_source (hKC hx)
    have he : (fun v : P × F => push C (f v.1) v.2) =ᶠ[𝓝 (p,C x)]
        (fun v : P × F => f v.1 (C.symm v.2)) := by
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (C.open_target.mem_nhds ht)] with v hv
      have hv' : v.2 ∈ C.target := hv
      simp [push,hv']
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hfx : ContDiffAt ℝ ∞ (fun v : P × E => f v.1 v.2) (p,C.symm (C x)) := by
      simpa [C.left_inv (hKC hx)] using hf x hx
    exact hfx.comp (p,C x) (contDiffAt_fst.prodMk ((hC x hx).comp (p,C x) contDiffAt_snd))
  · have hc : _root_.IsClosed (C '' K) := (hK.image_of_continuousOn (C.continuousOn.mono hKC)).isClosed
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hy)] with v hv
    apply Function.notMem_support.mp
    exact fun h => hv (support_push_subset C (f v.1) K (hfK v.1) h)

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPatch
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedSpace
lemma leadingCoordinate_support (ψ χ : Space → ℝ) (t : ℝ) :
    Function.support (leadingCoordinate J α ht p D g B ψ χ t) ⊆
      Function.support ψ ×ˢ Function.support χ := by
  intro x hx
  constructor
  · intro h
    apply hx
    apply ContinuousLinearMap.ext
    intro u
    simp only [leadingCoordinate,smul_apply,h,zero_apply]
    simp
  · intro h
    apply hx
    apply ContinuousLinearMap.ext
    intro u
    simp only [leadingCoordinate,smul_apply,h,zero_apply]
    simp

lemma leadingCoordinate_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    {t : ℝ} (htpos : 0 < t) {x : Space × Space}
    (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      leadingCoordinate J α ht p D g B ψ χ v.1 v.2) (t,x) := by
  have hψ' : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => ψ v.2.1) (t,x) :=
    hψ.contDiffAt.comp (t,x) contDiffAt_snd.fst
  have hχ' : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => χ v.2.2) (t,x) :=
    hχ.contDiffAt.comp (t,x) contDiffAt_snd.snd
  have hh : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => FlatHeat.heat v.1 v.2.2) (t,x) :=
    (FlatHeat.heat_joint_contDiffAt (x := (t,x.2)) (ne_of_gt htpos)).comp (t,x)
      (contDiffAt_fst.prodMk contDiffAt_snd.snd)
  exact ((hψ'.mul hχ').mul hh).smul
    ((normalGauge_smooth J α ht p D g B hs hg hB hx).comp (t,x) contDiffAt_snd)

lemma leadingPatch_apply (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source) :
    leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (x.1,normalMap g B x.1 x.2) =
      leadingCoordinate J α ht p D g B ψ χ t x :=
  KernelExtension.push_apply _ _ hx

lemma leadingPatch_joint_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (K : Set (Space × Space)) (hK : IsCompact K)
    (hFK : Function.support ψ ×ˢ Function.support χ ⊆ K)
    (O : Set Space) (hKO : K ⊆ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O)
    {t : ℝ} (htpos : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ v.1 v.2) (t,y) := by
  apply KernelExtension.push_family_contDiffAt _ _ K hK (fun x hx => (hKO hx).1.1.1)
    (fun s => (leadingCoordinate_support J α ht p D g B ψ χ s).trans hFK)
  · intro x hx
    exact leadingCoordinate_smooth J α ht p D g B hs hg hB ψ χ hψ hχ htpos (hKO hx).1.2.2
  · intro x hx
    have hi := (hKO hx).1.1.2
    exact (inverseRegularDomain_smooth _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq) _ hi).contDiffAt
      ((inverseRegularDomain_open _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).mem_nhds hi)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixInitial
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
lemma normalDensity_continuous (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    Continuous (normalDensity g B) := by
  exact (detGram_contDiff.continuous.comp (normalMetric_contDiff g B hg hB).continuous).sqrt

lemma normalDensity_zero {q : Space} (hactual : ActualData J α ht p D q g B) :
    normalDensity g B (q,0) = 1 := by
  rw [normalDensity,hactual.metric_zero J α ht p D g B,volumeDensity_euclidean]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialSliceMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialSliceMetricTensorNormedSpace
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)

lemma normalMap_slice_injective (q : Space) :
    InjOn (normalMap g B q) {z | (q,z) ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source} := by
  intro z hz w hw he
  have hc : geometricNormalChart g B hg hB q₀ Bq hBq (q,z) =
      geometricNormalChart g B hg hB q₀ Bq hBq (q,w) := by
    simpa only [geometricNormalChart_apply,Prod.mk.injEq,true_and] using he
  exact congrArg Prod.snd ((geometricNormalChart g B hg hB q₀ Bq hBq).injOn hz hw hc)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace
lemma actual {q : Space} (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) :
    ActualData J α ht p D.chart q D.metricExtension D.frameExtension :=
  ⟨D.actualDomain,D.actual_open,D.centers_actual hq,D.actual_subset,
    D.metric_actual,D.frame_actual,D.metric_symmetric⟩

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAtlasPatches
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r1ff684_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r1ff684_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma normalCutoff_tsupport : tsupport (D.normalCutoff : Space → ℝ) ⊆ Metric.closedBall (0 : Space) D.radius := by
  rw [D.normalCutoff.tsupport_eq]
  apply Metric.closedBall_subset_closedBall
  change D.radius/2 ≤ D.radius
  linarith [D.radius_pos]

end ParametrixData

variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r1ff684_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r1ff684_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hD in
lemma coordinatePartition_centerSupport (p : A.centers) :
    tsupport (coordinatePartition A p) ⊆ Metric.closedBall (extChartAt Model p.val p.val) (D p).radius := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := coordinatePartition_tsupport A p hq
  exact Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos])
    ((D p).source_image_subset ⟨x,hD p hx,rfl⟩)

include hD in
lemma partition_patch_support (p : A.centers) :
    Function.support (coordinatePartition A p) ×ˢ tsupport ((D p).normalCutoff : Space → ℝ) ⊆
      (D p).normalCompact :=
  Set.prod_mono ((subset_tsupport _).trans (coordinatePartition_centerSupport J α ht A D hD p))
    (D p).normalCutoff_tsupport

include hD in
lemma partitionLeading_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => partitionLeading J α ht A D p v.1 v.2) (t,y) :=
  leadingPatch_joint_smooth J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension hs
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_smooth_compact A p).1 (D p).normalCutoff.contDiff
    (D p).normalCompact (D p).normalCompact_compact
    ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans (partition_patch_support J α ht A D hD p))
    (D p).actualDomain (D p).tube htp y

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization NormalJets NormalMetricCalculus
open CoordinateOperator Filter Set _root_.MeasureTheory HodgeNormalSymbol
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma ParametrixData.density_actual {p : X} (D : ParametrixData J α ht p)
    {z : Space} (hz : z ∈ D.actualDomain) :
    volumeDensity (D.metricExtension z) = chartDensity J α p z := by
  rw [D.metric_actual z hz,coordinateMetric_bilinear J α ht p
    (D.chart.domain_subset (D.actual_subset hz))]
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixFormWeak
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
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
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_8_r1ff684_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_8_r1ff684_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma weakSliceDomain_open (q : Space) : IsOpen (E.weakSliceDomain q) :=
  (parametrixDomain_open J α ht p E.chart E.metricExtension E.frameExtension E.metric_smooth
    E.frame_smooth (extChartAt Model p p) E.centerFrame E.centerFrame_eq E.actualDomain
    E.actual_open).preimage (continuous_const.prodMk continuous_id)

lemma cutoff_weakSliceDomain {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius) :
    tsupport (E.normalCutoff : Space → ℝ) ⊆ E.weakSliceDomain q :=
  fun _ hz => E.tube ⟨hq,E.normalCutoff_tsupport hz⟩

lemma weakSliceDomain_actual {q z : Space} (hz : z ∈ E.weakSliceDomain q) :
    normalMap E.metricExtension E.frameExtension q z ∈ E.actualDomain := hz.2

lemma form_normal_smooth (a : TwoForm X) (ha : IsSmooth a) (q : Space) :
    ContDiffOn ℝ ∞ (HodgeChart.rawVector J α ht p E.chart a ∘
      normalMap E.metricExtension E.frameExtension q) (E.weakSliceDomain q) :=
  (HodgeChart.rawVector_smooth J α ht p E.chart ha).comp
    (normalMap_contDiff E.metricExtension E.frameExtension q).contDiffOn
    (fun _ hz => E.actual_subset (E.weakSliceDomain_actual hz))

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupMetricTensorSpace_9_r1ff684_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_9_r1ff684_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hE in
lemma leadingSlice_smooth (hs : IsSmooth α) (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) : ContDiff ℝ ∞ (leadingSlice J α ht A E p q t u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  exact ((partitionLeading_smooth J α ht A E hE hs p htp (q,y)).comp y
    (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).clm_apply contDiffAt_const

omit [CompactSpace X] in
lemma leadingSlice_normal (p : A.centers) (q : Space) (t : ℝ) (u : W) {z : Space}
    (hz : (q,z) ∈ (E p).normalChart.source) :
    leadingSlice J α ht A E p q t u (normalMap (E p).metricExtension (E p).frameExtension q z) =
      normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension (q,z)
        ((E p).normalCutoff z • NormalHeatResidual.modelSection t (coordinatePartition A p q • u) z) := by
  unfold leadingSlice partitionLeading
  rw [leadingPatch_apply J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val) (E p).centerFrame
    (E p).centerFrame_eq (coordinatePartition A p) (E p).normalCutoff t hz]
  simp only [leadingCoordinate,smul_apply,NormalHeatResidual.modelSection,map_smul,smul_smul]
  congr 1
  ring

omit [CompactSpace X] in
lemma leadingSlice_tsupport (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (leadingSlice J α ht A E p q t u) ⊆
      normalMap (E p).metricExtension (E p).frameExtension q ''
        tsupport ((E p).normalCutoff : Space → ℝ) := by
  classical
  apply closure_minimal _
    (((E p).normalCutoff.hasCompactSupport).image
      (normalMap_contDiff (E p).metricExtension (E p).frameExtension q).continuous).isClosed
  intro y hy
  have htarget : (q,y) ∈ (E p).normalChart.target := by
    by_contra hn
    apply hy
    change (if (q,y) ∈ (E p).normalChart.target then
      leadingCoordinate J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
        (coordinatePartition A p) (E p).normalCutoff t ((E p).normalChart.symm (q,y)) else 0) u = 0
    rw [ite_eq_right hn,zero_apply]
  let z := ((E p).normalChart.symm (q,y)).2
  have hf : ((E p).normalChart.symm (q,y)).1 = q :=
    geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq htarget
  have hz : (q,z) ∈ (E p).normalChart.source := by
    have heq : (q,z) = (E p).normalChart.symm (q,y) := Prod.ext hf.symm rfl
    rw [heq]
    exact (E p).normalChart.map_target htarget
  have he : normalMap (E p).metricExtension (E p).frameExtension q z = y :=
    geometricNormalChart_symm_right (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq htarget
  refine ⟨z,?_,he⟩
  by_contra hn
  apply hy
  rw [← he,leadingSlice_normal J α ht A E p q t u hz,
    image_eq_zero_of_notMem_tsupport hn]
  simp

omit [CompactSpace X] in
lemma leadingSlice_compact (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    HasCompactSupport (leadingSlice J α ht A E p q t u) :=
  (((E p).normalCutoff.hasCompactSupport).image
    (normalMap_contDiff (E p).metricExtension (E p).frameExtension q).continuous).of_isClosed_subset
      isClosed_closure (leadingSlice_tsupport J α ht A E p q t u)

omit [CompactSpace X] in
lemma leadingSlice_domain (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) : tsupport (leadingSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  intro y hy
  obtain ⟨z,hz,rfl⟩ := leadingSlice_tsupport J α ht A E p q t u hy
  have hnormal : z ∈ (E p).weakSliceDomain q := (E p).cutoff_weakSliceDomain hq hz
  exact (E p).actual_subset ((E p).weakSliceDomain_actual hnormal)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalSliceIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
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
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_10_r1ff684_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_10_r1ff684_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma normal_slice_integral {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    (F : Space → ℝ)
    (hF : Function.support F ⊆ normalMap E.metricExtension E.frameExtension q ''
      tsupport (E.normalCutoff : Space → ℝ)) :
    (∫ y, volumeDensity (E.metricExtension y) * F y) =
      ∫ z in E.weakSliceDomain q, normalDensity E.metricExtension E.frameExtension (q,z) *
        F (normalMap E.metricExtension E.frameExtension q z) := by
  let U := E.weakSliceDomain q
  let φ := normalMap E.metricExtension E.frameExtension q
  have hf : ∀ y, y ∉ φ '' U → volumeDensity (E.metricExtension y) * F y = 0 := by
    intro y hy
    have hFy : F y = 0 := by
      by_contra hn
      obtain ⟨z,hz,rfl⟩ := hF hn
      exact hy ⟨z,E.cutoff_weakSliceDomain hq hz,rfl⟩
    rw [hFy,mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf]
  have hi : InjOn φ U := (normalMap_slice_injective E.metricExtension E.frameExtension
    E.metric_smooth E.frame_smooth (extChartAt Model p p) E.centerFrame E.centerFrame_eq q).mono
      (fun _ hz => hz.1.1.1)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (E.weakSliceDomain_open q).measurableSet
    (fun z (_ : z ∈ U) => ((normalMap_contDiff E.metricExtension E.frameExtension q).differentiable
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt.hasFDerivAt.hasFDerivWithinAt) hi]
  apply setIntegral_congr_fun (E.weakSliceDomain_open q).measurableSet
  intro z _
  dsimp only
  rw [normalDensity,normal_density_jacobian E.metricExtension E.frameExtension E.metric_smooth
    E.frame_smooth E.metric_symmetric]
  change |(fderiv ℝ φ z).toLinearMap.det| *
      (volumeDensity (E.metricExtension (φ z)) * F (φ z)) =
    (|(fderiv ℝ φ z).toLinearMap.det| * volumeDensity (E.metricExtension (φ z))) * F (φ z)
  ring

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_11_r1ff684_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_11_r1ff684_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma cutoffSection_tsupport (q : Space) (t : ℝ) (u : W) :
    tsupport (E.cutoffSection q t u) ⊆ tsupport (E.normalCutoff : Space → ℝ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hn
  exact hz (by simp only [cutoffSection,image_eq_zero_of_notMem_tsupport hn,zero_smul,map_zero])

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchPairing
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_12_r1ff684_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_12_r1ff684_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma slice_pairing_integral {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    (f k kN : Space → W)
    (hk : Function.support k ⊆ normalMap E.metricExtension E.frameExtension q ''
      tsupport (E.normalCutoff : Space → ℝ))
    (hN : Function.support kN ⊆ tsupport (E.normalCutoff : Space → ℝ))
    (he : ∀ z ∈ E.weakSliceDomain q, k (normalMap E.metricExtension E.frameExtension q z) = kN z) :
    (∫ y, chartDensity J α p y * ⟪f y,k y⟫) =
      ∫ z, normalDensity E.metricExtension E.frameExtension (q,z) *
        ⟪f (normalMap E.metricExtension E.frameExtension q z),kN z⟫ := by
  let F := fun y => ⟪f y,k y⟫
  have hFs : Function.support F ⊆ Function.support k := by
    intro y hy hkzero
    exact hy (by simp only [F,hkzero,inner_zero_right])
  have hd : (∫ y, chartDensity J α p y * F y) =
      ∫ y, volumeDensity (E.metricExtension y) * F y := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : F y = 0
    · simp only [hy,mul_zero]
    · obtain ⟨z,hz,rfl⟩ := hk (hFs hy)
      rw [E.density_actual J α ht (E.weakSliceDomain_actual (E.cutoff_weakSliceDomain hq hz))]
  change (∫ y, chartDensity J α p y * F y) = _
  rw [hd,E.normal_slice_integral hq F (hFs.trans hk)]
  rw [setIntegral_congr_fun (E.weakSliceDomain_open q).measurableSet
    (fun z hz => congrArg (fun w => normalDensity E.metricExtension E.frameExtension (q,z) *
      ⟪f (normalMap E.metricExtension E.frameExtension q z),w⟫) (he z hz))]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hNz : kN z = 0 := Function.notMem_support.mp (fun hh => hz (E.cutoff_weakSliceDomain hq (hN hh)))
  rw [hNz,inner_zero_right,mul_zero]

end ParametrixData
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

local instance instNormedAddCommGroupMetricTensorSpace_12_r1ff684_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_12_r1ff684_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma leadingSlice_pairing_integral (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) (f : Space → W) :
    (∫ y, chartDensity J α p.val y * ⟪f y,leadingSlice J α ht A E p q t u y⟫) =
    ∫ z, normalDensity (E p).metricExtension (E p).frameExtension (q,z) *
      ⟪f (normalMap (E p).metricExtension (E p).frameExtension q z),
        (E p).cutoffSection q t (coordinatePartition A p q • u) z⟫ :=
  (E p).slice_pairing_integral hq f _ _
    ((subset_tsupport _).trans (leadingSlice_tsupport J α ht A E p q t u))
    ((subset_tsupport _).trans ((E p).cutoffSection_tsupport q t _))
    (fun _ hz => leadingSlice_normal J α ht A E p q t u hz.1.1.1)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupMetricTensorSpace_14_r1ff684_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_14_r1ff684_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hE in
lemma leadingSliceForm_smooth (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) : IsSmooth (leadingSliceForm J α ht A E p q t u) := by
  exact HodgeChart.manifoldTest_smooth J α hs ht p.val (E p).chart
    (leadingSlice_smooth J α ht A E hE hs p q htp u)
    (leadingSlice_compact J α ht A E p q t u)
    (leadingSlice_domain J α ht A E p hq t u)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchAllCenters
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [T2Space X] [CompactSpace X] in
lemma partitionLeading_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (y : Space) :
    partitionLeading J α ht A E p t (q,y) = 0 := by
  unfold partitionLeading leadingPatch KernelExtension.push
  split_ifs with hz
  · have hf := geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq hz
    simp only [leadingCoordinate,hf,hq,zero_mul]
    exact zero_smul ℝ (normalGauge J α ht p.val (E p).chart
      (E p).metricExtension (E p).frameExtension ((E p).normalChart.symm (q,y)))
  · rfl

omit [T2Space X] [CompactSpace X] in
lemma leadingSliceForm_zero_center (p : A.centers) {q : Space}
    (hq : coordinatePartition A p q = 0) (t : ℝ) (u : W) :
    leadingSliceForm J α ht A E p q t u = 0 := by
  have hz : leadingSlice J α ht A E p q t u = 0 := by
    funext y
    simp only [leadingSlice,partitionLeading_zero_center J α ht A E p hq t y,zero_apply,Pi.zero_apply]
  funext x
  apply HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart
  rw [hz,tsupport_zero,Set.image_empty]
  exact Set.notMem_empty x

include hE in
lemma leadingSliceForm_smooth_all (hs : IsSmooth α) (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) : IsSmooth (leadingSliceForm J α ht A E p q t u) := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact leadingSliceForm_smooth J α ht A E hE hs p hq htp u
  · rw [leadingSliceForm_zero_center J α ht A E p
      (image_eq_zero_of_notMem_tsupport (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))) t u]
    exact TamingCompatibility.IsSmooth.zero

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCoordinateRetraction
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma coordinateEncode_rawVector (p : A.centers) (a : TwoForm X) {q : Space}
    (hq : q ∈ (D p).chart.domain) :
    coordinateEncode J α ht A D p q (HodgeChart.rawVector J α ht p.val (D p).chart a q) =
      frameEncode J α ht A D ((extChartAt Model p.val).symm q) (a ((extChartAt Model p.val).symm q)) := by
  ext i
  change ⟪HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q,
    HodgeChart.rawVector J α ht p.val (D p).chart a q⟫ = _
  rw [real_inner_comm]
  unfold HodgeChart.rawVector
  rw [coordinates_pairing _ (by simp [Space]) _ ((D p).chart.frame_gram q hq),
    GeometricAdjoint.pairing_two_chart J α ht p.val a (globalFrame J α ht A D i.1 i.2)
      ((D p).chart.domain_subset hq)]
  rfl

omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_apply (p : A.centers) (q : Space) (v : FrameSpace A) :
    coordinateDecode J α ht A D p q v = (squareMass A ((extChartAt Model p.val).symm q))⁻¹ •
      ∑ i : A.centers × Fin 6, v i •
        HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q := by
  change (squareMass A ((extChartAt Model p.val).symm q))⁻¹ • ((∑ i : A.centers × Fin 6,
    (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
      (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q)) v) = _
  simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_rawVector (p : A.centers) (q : Space) (v : FrameSpace A) :
    coordinateDecode J α ht A D p q v = HodgeChart.rawVector J α ht p.val (D p).chart
      (fun x => frameDecode J α ht A D x v) q := by
  rw [coordinateDecode_apply,Fintype.sum_prod_type]
  let L : MetricForms.Form Space 2 →L[ℝ] W :=
    HodgeFrame.coordinates (fun i => (D p).chart.frame i q) ∘L
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (mfderiv Model Model (extChartAt Model p.val).symm q)
  change (squareMass A ((extChartAt Model p.val).symm q))⁻¹ •
    (∑ i : A.centers, ∑ j : Fin 6, v (i,j) • L (globalFrame J α ht A D i j ((extChartAt Model p.val).symm q))) = _
  simp only [HodgeChart.rawVector,ManifoldForms.pullback,frameDecode_apply]
  change _ = L _
  simp only [Finset.smul_sum,smul_smul]
  have he (g : A.centers → Fin 6 → MetricForms.Form Space 2) (c : A.centers → Fin 6 → ℝ) :
      L (∑ i : A.centers, ∑ j : Fin 6, c i j • g i j) = ∑ i : A.centers, ∑ j : Fin 6, c i j • L (g i j) := by
    simp only [map_sum,map_smul]
  exact (he (fun i j => globalFrame J α ht A D i j ((extChartAt Model p.val).symm q))
    (fun i j => (squareMass A ((extChartAt Model p.val).symm q))⁻¹*v (i,j))).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalParametrix
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma frameEncode_manifoldTest (p : A.centers) (f : Space → W)
    (hfd : tsupport f ⊆ (E p).chart.domain) (x : X) :
    frameEncode J α ht A E x (HodgeChart.manifoldTest J α ht p.val (E p).chart f x) =
      if x ∈ (extChartAt Model p.val).source then
        coordinateEncode J α ht A E p (extChartAt Model p.val x) (f (extChartAt Model p.val x)) else 0 := by
  by_cases hx : x ∈ (extChartAt Model p.val).source
  · rw [ite_eq_left hx]
    by_cases hfx : extChartAt Model p.val x ∈ tsupport f
    · have hd := hfd hfx
      have hr : HodgeChart.rawVector J α ht p.val (E p).chart
          (HodgeChart.manifoldTest J α ht p.val (E p).chart f) (extChartAt Model p.val x) =
          f (extChartAt Model p.val x) := by
        unfold HodgeChart.rawVector
        rw [HodgeChart.pullback_manifoldTest J α ht p.val (E p).chart f
          ((extChartAt Model p.val).map_source hx)]
        exact coordinates_reconstruct _ _ ((E p).chart.frame_gram _ hd) _
      have hh := coordinateEncode_rawVector J α ht A E p
        (HodgeChart.manifoldTest J α ht p.val (E p).chart f) hd
      rw [hr,(extChartAt Model p.val).left_inv hx] at hh
      exact hh.symm
    · have hz := image_eq_zero_of_notMem_tsupport hfx
      erw [hz,map_zero,HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart f,map_zero]
      rintro ⟨z,hz,he⟩
      have heq : extChartAt Model p.val x = z := by
        rw [← he,(extChartAt Model p.val).right_inv ((E p).chart.domain_subset (hfd hz))]
      exact hfx (heq ▸ hz)
  · erw [ite_eq_right hx,HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart f,map_zero]
    rintro ⟨z,hz,rfl⟩
    exact hx ((extChartAt Model p.val).map_target ((E p).chart.domain_subset (hfd hz)))

include hE in
omit [T2Space X] in
lemma leadingSlice_domain_all (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (leadingSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact leadingSlice_domain J α ht A E p hq t u
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    have he : leadingSlice J α ht A E p q t u = 0 := by
      funext y
      simp only [leadingSlice,partitionLeading_zero_center J α ht A E p hz t y,zero_apply,Pi.zero_apply]
    rw [he,tsupport_zero]
    exact empty_subset _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelForms
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma leadingFiberForm_smooth (hs : IsSmooth α) (p : A.centers) (y : X)
    {t : ℝ} (htp : 0 < t) (v : FrameSpace A) : IsSmooth (leadingFiberForm J α ht A E p y t v) := by
  unfold leadingFiberForm
  split_ifs
  · exact leadingSliceForm_smooth_all J α ht A E hE hs p _ htp _
  · exact TamingCompatibility.IsSmooth.zero

include hE in
omit [T2Space X] in
lemma leadingFiberForm_encode (p : A.centers) (y x : X) (t : ℝ) (v : FrameSpace A) :
    frameEncode J α ht A E x (leadingFiberForm J α ht A E p y t v x) =
      ManifoldKernelExtension.push p.val (leadingMatrix J α ht A E p t) (y,x) v := by
  unfold leadingFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · rw [ite_eq_left hy]
    unfold leadingSliceForm
    rw [frameEncode_manifoldTest J α ht A E p _
      (leadingSlice_domain_all J α ht A E hE p _ t _)]
    by_cases hx : x ∈ (extChartAt Model p.val).source
    · rw [ite_eq_left hx,ManifoldKernelExtension.push,ite_eq_left ⟨hy,hx⟩]
      rfl
    · rw [ite_eq_right hx,ManifoldKernelExtension.push,ite_eq_right (by simpa only [Set.mem_prod,hy,true_and] using hx)]
      rfl
  · simp only [ite_eq_right hy,Pi.zero_apply]
    erw [map_zero]
    rw [ManifoldKernelExtension.push,ite_eq_right (fun h => hy h.1)]
    rfl

include hE in
omit [T2Space X] in
lemma leadingKernelForm_encode (t : ℝ) (y x : X) (v : FrameSpace A) :
    frameEncode J α ht A E x (leadingKernelForm J α ht A E t y v x) =
      globalLeading J α ht A E t x y v := by
  unfold leadingKernelForm globalLeading assemble
  split_ifs
  · erw [Finset.sum_apply,map_sum,_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro p _
    exact leadingFiberForm_encode J α ht A E hE p y x t v
  · exact map_zero _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [T2Space X] in
lemma leadingKernelForm_pairing (a : TwoForm X) (y : X) (v : FrameSpace A) (t : ℝ) (x : X) :
    GeometricAdjoint.pairing J α ht a (leadingKernelForm J α ht A E t y v) x =
      framePairing A J α ht E a x (globalLeading J α ht A E t x y v) := by
  rw [← leadingKernelForm_encode J α ht A E hE]
  rw [framePairing_apply]
  unfold GeometricAdjoint.pairing
  dsimp only
  erw [frameDecode_encode J α ht A E hE]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma pairing_zero_form (b : TwoForm X) (x : X) : GeometricAdjoint.pairing J α ht b 0 x = 0 :=
  MetricForms.pairing_zero_right (E := Space) (GeometricAdjoint.pointMetric J α ht x) (b x)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma pairing_sum_form {ι : Type*} (s : Finset ι) (b : TwoForm X) (f : ι → TwoForm X) (x : X) :
    GeometricAdjoint.pairing J α ht b (∑ i ∈ s, f i) x =
      ∑ i ∈ s, GeometricAdjoint.pairing J α ht b (f i) x := by
  change MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 (b x) _ = _
  erw [Finset.sum_apply,map_sum]
  rfl

include hs in
omit [T2Space X] in
lemma integral_pairing_sum {ι : Type*} (s : Finset ι) (b : TwoForm X) (hb : IsSmooth b)
    (f : ι → TwoForm X) (hf : ∀ i ∈ s, IsSmooth (f i)) :
    (∫ x, GeometricAdjoint.pairing J α ht b (∑ i ∈ s, f i) x ∂geometricVolume A J α) =
      ∑ i ∈ s, ∫ x, GeometricAdjoint.pairing J α ht b (f i) x ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  simp_rw [pairing_sum_form]
  apply integral_finsetSum
  intro i hi
  exact (GeometricAdjoint.pairing_two_smooth J α hs ht hb (hf i hi)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelWeakAction
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator HodgeNormalSymbol
open FirstJetGauge OrthogonalJets Filter Set OperatorCalculus _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] normalGauge normalFirst

lemma actual_cutoff_initial_local (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B)
    (χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    {U : Set Space} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    (u : W) (η : Space → W) (hη : ContDiffOn ℝ ∞ η U) :
    Tendsto (fun t : ℝ => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection t u z)⟫)
      (𝓝[>] 0) (𝓝 ⟪η 0,u⟫) := by
  obtain ⟨η',hη',hc,hD,he⟩ := exists_compact_smooth_extension hU hχc hχU hη
  let F : Space → ℝ := fun z => normalDensity g B (q,z) * χ z *
    ⟪η' z,normalGauge J α ht p D g B (q,z) u⟫
  have hG : Continuous (fun z : Space => normalGauge J α ht p D g B (q,z)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      ((normalGauge_smooth J α ht p D g B hs hg hB (hactual.center J α ht p D g B).1).comp z
        (contDiffAt_const.prodMk contDiffAt_id)).continuousAt)
  have hF : Continuous F := (((normalDensity_continuous g B hg hB).comp
    (continuous_const.prodMk continuous_id)).mul hχ).mul
      (hη'.continuous.inner (hG.clm_apply continuous_const))
  have hFc : HasCompactSupport F := by
    apply hχc.mono
    intro z hz
    change χ z ≠ 0
    intro hz0
    exact hz (by simp [F,hz0])
  have hzχ : (0 : Space) ∈ tsupport χ := subset_tsupport _ (by simpa only [Function.mem_support,hχ0] using one_ne_zero)
  have hF0 : F 0 = ⟪η 0,u⟫ := by
    simp only [F,normalDensity_zero J α ht p D g B hactual,hχ0,one_mul,
      normalGauge_zero,one_apply_eq_self,(he 0 hzχ).eq_of_nhds]
  have hh := FlatHeat.heat_approximate_identity F (hF.integrable_of_hasCompactSupport hFc) hF.continuousAt
  rw [hF0] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport χ
  · simp only [F,(he z hz).eq_of_nhds,NormalHeatResidual.modelSection,map_smul,
      inner_smul_right,smul_eq_mul]
    ring
  · simp only [F,image_eq_zero_of_notMem_tsupport hz,mul_zero,zero_mul,zero_smul,map_zero,
      inner_zero_right,smul_zero]

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

lemma cutoff_form_initial (hs : IsSmooth α) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ z, normalDensity E.metricExtension E.frameExtension (q,z) *
      ⟪HodgeChart.rawVector J α ht p E.chart a (normalMap E.metricExtension E.frameExtension q z),
        normalGauge J α ht p E.chart E.metricExtension E.frameExtension (q,z)
          (E.normalCutoff z • NormalHeatResidual.modelSection t u z)⟫)
      (𝓝[>] 0) (𝓝 ⟪HodgeChart.rawVector J α ht p E.chart a q,u⟫) := by
  have hh := actual_cutoff_initial_local J α ht p E.chart E.metricExtension E.frameExtension hs
    E.metric_smooth E.frame_smooth (E.actual hq) E.normalCutoff E.normalCutoff.continuous
    E.normalCutoff.hasCompactSupport
    (E.normalCutoff.one_of_mem_closedBall (Metric.mem_closedBall_self E.normalCutoff.rIn_pos.le))
    (E.weakSliceDomain_open q) (E.cutoff_weakSliceDomain hq) u _ (E.form_normal_smooth a ha q)
  simpa only [Function.comp_apply,normalMap_zero] using hh

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldPairingInitial
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma leadingSliceForm_initial (p : A.centers) (q : Space) (u : W)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, GeometricAdjoint.pairing J α ht a
        (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (coordinatePartition A p q * ⟪HodgeChart.rawVector J α ht p.val (E p).chart a q,u⟫)) := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · have hh := (E p).cutoff_form_initial hs hq (coordinatePartition A p q • u) a ha
    rw [inner_smul_right] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t htp
    rw [leadingSliceForm,HodgeChart.pairing_manifoldTest_integral J α ht p.val (E p).chart A hs ha
      (leadingSlice_smooth J α ht A E hE hs p q htp u)
      (leadingSlice_compact J α ht A E p q t u)
      (leadingSlice_domain J α ht A E p hq t u),leadingSlice_pairing_integral J α ht A E p hq]
    rfl
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    simp only [leadingSliceForm_zero_center J α ht A E p hz,pairing_zero_form,
      integral_zero,hz,zero_mul]
    exact tendsto_const_nhds

include hs hE in
lemma leadingFiberForm_initial (p : A.centers) (y : X) (v : FrameSpace A)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, GeometricAdjoint.pairing J α ht a
        (leadingFiberForm J α ht A E p y t v) x ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (A.partition p y * GeometricAdjoint.pairing J α ht a
        (fun x => frameDecode J α ht A E x v) y)) := by
  unfold leadingFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · simp only [ite_eq_left hy]
    have hh := leadingSliceForm_initial A J α hs ht E hE p (extChartAt Model p.val y)
      (coordinateDecode J α ht A E p (extChartAt Model p.val y) v) a ha
    rw [coordinatePartition_apply A p hy] at hh
    by_cases hz : A.partition p y = 0
    · simpa only [hz,zero_mul] using hh
    · have hsupp : y ∈ tsupport (A.partition p) := subset_tsupport _ hz
      have hc : extChartAt Model p.val y ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius :=
        (Metric.closedBall_subset_closedBall (by linarith [(E p).radius_pos]))
          ((E p).source_image_subset ⟨y,hE p hsupp,rfl⟩)
      have hyd := (E p).actual_subset ((E p).centers_actual hc)
      have hpair : ⟪HodgeChart.rawVector J α ht p.val (E p).chart a (extChartAt Model p.val y),
          coordinateDecode J α ht A E p (extChartAt Model p.val y) v⟫ =
          GeometricAdjoint.pairing J α ht a (fun x => frameDecode J α ht A E x v) y := by
        rw [coordinateDecode_rawVector]
        unfold HodgeChart.rawVector
        rw [coordinates_pairing _ (by simp [Space]) _ ((E p).chart.frame_gram _ hyd)]
        have hp := GeometricAdjoint.pairing_two_chart J α ht p.val a
          (show TwoForm X from fun x => frameDecode J α ht A E x v)
          ((extChartAt Model p.val).map_source hy)
        rw [(extChartAt Model p.val).left_inv hy] at hp
        exact hp
      rwa [hpair] at hh
  · have hz : A.partition p y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (A.subordinate p h))
    simp only [ite_eq_right hy,pairing_zero_form,integral_zero,hz,zero_mul]
    exact tendsto_const_nhds

include hs hE in
lemma leadingKernelForm_initial (y : X) (v : FrameSpace A)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, GeometricAdjoint.pairing J α ht a
        (leadingKernelForm J α ht A E t y v) x ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (GeometricAdjoint.pairing J α ht a
        (fun x => frameDecode J α ht A E x v) y)) := by
  have hh := tendsto_finsetSum (s := Finset.univ) (fun (p : A.centers) _ => leadingFiberForm_initial A J α hs ht E hE p y v a ha)
  rw [← Finset.sum_mul, partition_sum A y,one_mul] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t htp
  change 0 < t at htp
  rw [leadingKernelForm,ite_eq_left htp]
  exact (integral_pairing_sum A J α hs ht _ a ha _ (fun p _ =>
    leadingFiberForm_smooth J α ht A E hE hs p y htp v)).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeInputInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma kernel_leading_pairing_initial_oai (y : X) (v : FrameSpace A)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, framePairing A J α ht E a x
      (globalLeading J α ht A E t x y v) ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (framePairing A J α ht E a y v)) := by
  have hh := leadingKernelForm_initial A J α hs ht E hE y v a ha
  rw [← framePairing_apply] at hh
  simp_rw [leadingKernelForm_pairing A J α ht E hE] at hh
  exact hh

attribute [local irreducible] framePairing globalLeading globalResidual

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial_oai.{u_1}
