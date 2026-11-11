-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:51.308598+00:00
-- url     : https://prove2.me/submissions/48901a06-0d02-4569-8491-373fade0d4d0

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc019
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalGauge_unitary
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_scalar_at
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalHeatResidual_actual_cutoff_residual
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalHeatResidual_cutoff_gaussian_residual
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_OrthogonalJets_gauge_contDiff

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeParametrixResidual
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
  normalPrincipal normalGauge gaugedFirst gaugedZero

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixResidualMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixResidualMetricTensorNormedSpace
lemma actual_cutoff_square_eq_oai (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
    (hactual : ActualData J α ht p D q g B)
    (hz : (q,z) ∈ normalDomain J α ht p D g B)
    (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (htpos : 0 < t) (u : W) :
      deriv (fun s => normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)) t +
        weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
          (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
          (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
            (pulledB J α ht p D g B q)
            (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y))) z =
      normalGauge J α ht p D g B (q,z)
        (NormalHeatResidual.residual
          (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
          (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
          (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
            (gaugedZero J α ht p D g B) χ (q,y)) t z u) := by
  have hpa := pulledA_joint J α ht p D g B hg hB hz.1
  have hpb := pulledB_joint J α hs ht p D g B hg hB hz.1
  have hpρ := normalDensity_smooth g B hg hB hz.2
  have hU : ContDiff ℝ ∞ (fun y => normalGauge J α ht p D g B (q,y)) := by
    unfold normalGauge
    exact OrthogonalJets.gauge_contDiff (V := Space) (W := W)
      (halfJet (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
        (fun j => normalFirst J α ht p D g B j (q,0)))
  have hu : ∀ y, normalGauge J α ht p D g B (q,y) ∈ unitary (W →L[ℝ] W) :=
    normalGauge_unitary J α ht p D g B hs hg hB hactual
  have horth (y : Space) : (normalGauge J α ht p D g B (q,y)).adjoint ∘L
      normalGauge J α ht p D g B (q,y) = ContinuousLinearMap.id ℝ W := by
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.mul_def,ContinuousLinearMap.one_def]
      using (Unitary.star_mul_self_of_mem (hu y))
  have hρpos : normalDensity g B (q,z) ≠ 0 := by
    unfold normalDensity
    exact ne_of_gt (volumeDensity_pos hz.2)
  have hres := NormalHeatResidual.actual_cutoff_residual (pulledA J α ht p D g B q)
    (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
    (fun i j y => normalPrincipal g B i j (q,y))
    (fun y => normalGauge J α ht p D g B (q,y)) hU horth χ hχ
    (fun i => ((hpa i).comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hpb.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hpρ.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    hρpos (pulledA_scalar_at J α ht p D g B hg hB hsym hz.1 hgact) htpos u
  have hee : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → Space) = EuclideanEnergy.e := by
    funext i
    simp [EuclideanEnergy.e]
  rw [hee] at hres
  have hf : gaugeFirst EuclideanEnergy.e (fun i j y => normalPrincipal g B i j (q,y))
      (firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (fun y => normalGauge J α ht p D g B (q,y)) =
        (fun j y => gaugedFirst J α ht p D g B j (q,y)) := by
    unfold gaugedFirst normalFirst
    rfl
  have hc : gaugeZero EuclideanEnergy.e (fun i j y => normalPrincipal g B i j (q,y))
      (firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (zeroMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (fun y => normalGauge J α ht p D g B (q,y)) =
        (fun y => gaugedZero J α ht p D g B (q,y)) := by
    unfold gaugedZero normalFirst normalZero
    rfl
  rw [hf,hc] at hres
  have hcut := NormalHeatResidual.cutoff_gaussian_residual
    (fun i j y => normalPrincipal g B i j (q,y))
    (fun j y => gaugedFirst J α ht p D g B j (q,y))
    (fun y => gaugedZero J α ht p D g B (q,y)) χ hχ htpos z u
  rw [hee] at hcut
  rw [hcut] at hres
  have hcancel (v : W) : normalGauge J α ht p D g B (q,z)
      ((normalGauge J α ht p D g B (q,z)).adjoint v) = v := by
    exact congrArg (fun C : W →L[ℝ] W => C v) (by
      simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.mul_def,
        ContinuousLinearMap.one_def] using Unitary.mul_star_self_of_mem (hu z))
  have hh := congrArg (normalGauge J α ht p D g B (q,z)) hres
  rw [hcancel] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [NormalHeatResidual.residual,CutoffFamilies.principal,
    CutoffFamilies.first,CutoffFamilies.zero,hee]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq_oai.{u_1}
