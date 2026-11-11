-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:52.283954+00:00
-- url     : https://prove2.me/submissions/5cc108f2-2ca1-4401-ac25-77484bd67b67

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_CutoffFamilies_residual_zero_off
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FlatHeat_heat_contDiff
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FlatHeat_heat_hasDerivAt_time
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_actual_cutoff_square_eq
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_OperatorCalculus_integral_square_residual_local
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_OrthogonalJets_gauge_contDiff

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixLocalWeak
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
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixLocalWeakMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixLocalWeakMetricTensorNormedSpace
lemma actual_cutoff_weak_local_oai (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q : Space}
    (hactual : ActualData J α ht p D q g B)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {U : Set Space} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    {t : ℝ} (htpos : 0 < t) (u : W)
    (η : Space → W) (hη : ContDiffOn ℝ ∞ η U)
    (hsub : ∀ z ∈ U, (q,z) ∈ normalDomain J α ht p D g B)
    (hgact : ∀ z ∈ U,
      g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear) :
    (∫ z, normalDensity g B (q,z) * ⟪η z,
      deriv (fun s => normalGauge J α ht p D g B (q,z)
        (χ z • NormalHeatResidual.modelSection s u z)) t⟫) +
    (∫ z, normalDensity g B (q,z) *
      ⟪differential EuclideanEnergy.e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q) η z,
        differential EuclideanEnergy.e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
          (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y)) z⟫) =
    ∫ z, normalDensity g B (q,z) * ⟪η z,normalGauge J α ht p D g B (q,z)
      (NormalHeatResidual.residual
        (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
        (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
        (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
          (gaugedZero J α ht p D g B) χ (q,y)) t z u)⟫ := by
  have hG : ContDiff ℝ ∞ (fun y => normalGauge J α ht p D g B (q,y)) := by
    unfold normalGauge
    exact OrthogonalJets.gauge_contDiff (V := Space) (W := W)
      (halfJet (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
        (fun j => normalFirst J α ht p D g B j (q,0)))
  have hk : ContDiff ℝ ∞ (fun y => normalGauge J α ht p D g B (q,y)
      (χ y • NormalHeatResidual.modelSection t u y)) :=
    hG.clm_apply (hχ.smul ((FlatHeat.heat_contDiff t).smul contDiff_const))
  have htime (z : Space) :
      deriv (fun s => normalGauge J α ht p D g B (q,z)
        (χ z • NormalHeatResidual.modelSection s u z)) t =
      normalGauge J α ht p D g B (q,z)
        (χ z • (((-2/t+‖z‖^2/(4*t^2))*FlatHeat.heat t z) • u)) := by
    exact ((normalGauge J α ht p D g B (q,z)).hasFDerivAt.comp_hasDerivAt t
      (((FlatHeat.heat_hasDerivAt_time htpos z).smul_const u).const_smul (χ z))).deriv
  have hd : Continuous (fun z => deriv (fun s => normalGauge J α ht p D g B (q,z)
      (χ z • NormalHeatResidual.modelSection s u z)) t) := by
    simp_rw [htime]
    exact hG.continuous.clm_apply (hχ.continuous.smul
      (((continuous_const.add ((continuous_norm.pow 2).div_const _)).mul
        (FlatHeat.heat_contDiff t).continuous).smul continuous_const))
  apply integral_square_residual_local volume hU hχc hχU EuclideanEnergy.e
    (pulledA J α ht p D g B q) (pulledB J α ht p D g B q) (fun z => normalDensity g B (q,z))
    _ _ _ η _ _ _ hk.contDiffOn hd.continuousOn hη
  · apply closure_minimal _ (isClosed_tsupport χ)
    intro z hz
    by_contra hn
    exact hz (by simp [image_eq_zero_of_notMem_tsupport hn])
  · intro z hz
    by_contra hn
    apply hz
    dsimp only
    rw [htime,image_eq_zero_of_notMem_tsupport hn]
    simp
  · intro z hz
    by_contra hn
    apply hz
    dsimp only
    rw [CutoffFamilies.residual_zero_off _ _ _ χ q t hn]
    simp
  · intro z hz
    unfold normalDensity
    exact ne_of_gt (volumeDensity_pos (hsub z hz).2)
  · intro z hz
    exact actual_cutoff_square_eq J α ht p D g B hs hg hB hsym hactual (hsub z hz)
      (hgact z hz) χ hχ htpos u
  · intro i z hz
    exact ((pulledA_joint J α ht p D g B hg hB (hsub z hz).1 i).comp z
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · intro z hz
    exact ((pulledB_joint J α hs ht p D g B hg hB (hsub z hz).1).comp z
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · intro z hz
    exact ((normalDensity_smooth g B hg hB (hsub z hz).2).comp z
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local_oai.{u_1}
