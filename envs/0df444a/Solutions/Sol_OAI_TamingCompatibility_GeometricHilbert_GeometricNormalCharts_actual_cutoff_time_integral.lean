-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:08:54.374423+00:00
-- url     : https://prove2.me/submissions/01b5e066-85ec-4faa-a10b-6b4bb2808100

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FlatHeat_heat_contDiff
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FlatHeat_heat_hasDerivAt_time
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FlatHeat_heat_joint_contDiffAt
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_continuous
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_OperatorCalculus_hasDerivAt_integral_compact_positive
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_OrthogonalJets_gauge_contDiff

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactTimeIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralMetricTensorNormedSpace
lemma actual_cutoff_time_integral_oai (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q : Space) (χ : Space → ℝ) (hχ : Continuous χ) {t : ℝ} (htpos : 0 < t) (u : W)
    (η : Space → W) (hη : Continuous η) (hc : HasCompactSupport η) :
    HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
      (∫ z, normalDensity g B (q,z) * ⟪η z,
        deriv (fun s => normalGauge J α ht p D g B (q,z)
          (χ z • NormalHeatResidual.modelSection s u z)) t⟫) t := by
  let G : Space → W →L[ℝ] W := fun z => normalGauge J α ht p D g B (q,z)
  let ρ : Space → ℝ := fun z => normalDensity g B (q,z)
  let k : ℝ → Space → W := fun s z => G z (χ z • NormalHeatResidual.modelSection s u z)
  let d : ℝ → Space → W := fun s z => G z (χ z • (((-2/s+‖z‖^2/(4*s^2))*FlatHeat.heat s z) • u))
  have hG : Continuous G := by
    have h : ContDiff ℝ ∞ G := by
      unfold G normalGauge
      exact OrthogonalJets.gauge_contDiff (V := Space) (W := W)
        (halfJet (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
          (fun j => normalFirst J α ht p D g B j (q,0)))
    exact h.continuous
  have hρ : Continuous ρ := (normalDensity_continuous g B hg hB).comp
    (continuous_const.prodMk continuous_id)
  have hd (s : ℝ) (hs : 0 < s) (z : Space) : HasDerivAt (fun r => k r z) (d s z) s :=
    (G z).hasFDerivAt.comp_hasDerivAt s
      (((FlatHeat.heat_hasDerivAt_time hs z).smul_const u).const_smul (χ z))
  have hdc : ContinuousOn (fun v : ℝ × Space => d v.1 v.2) (Ioi 0 ×ˢ univ) := by
    intro v hv
    have hs : v.1 ≠ 0 := ne_of_gt hv.1
    have hh := (FlatHeat.heat_joint_contDiffAt (x := v) hs).continuousAt
    have hp : ContinuousAt (fun w : ℝ × Space => (-2/w.1+‖w.2‖^2/(4*w.1^2))*FlatHeat.heat w.1 w.2) v :=
      ((continuousAt_const.div continuousAt_fst hs).add
        ((continuousAt_snd.norm.pow 2).div (continuousAt_const.mul (continuousAt_fst.pow 2))
          (mul_ne_zero (by norm_num) (pow_ne_zero _ hs)))).mul hh
    exact ((hG.continuousAt.comp continuousAt_snd).clm_apply
      ((hχ.continuousAt.comp continuousAt_snd).smul (hp.smul continuousAt_const))).continuousWithinAt
  let F : ℝ → Space → ℝ := fun s z => ρ z * ⟪η z,k s z⟫
  let F' : ℝ → Space → ℝ := fun s z => ρ z * ⟪η z,d s z⟫
  have hi := hasDerivAt_integral_compact_positive volume F F' (tsupport η) hc
    (fun s _ => hρ.mul (hη.inner (hG.clm_apply (hχ.smul
      ((FlatHeat.heat_contDiff s).continuous.smul continuous_const)))))
    ((hρ.comp continuous_snd).continuousOn.mul ((hη.comp continuous_snd).continuousOn.inner hdc))
    (fun _ _ _ hz => by
      apply subset_tsupport η
      change η _ ≠ 0
      intro he
      exact hz (by simp [F,he]))
    (fun _ _ _ hz => by
      apply subset_tsupport η
      change η _ ≠ 0
      intro he
      exact hz (by simp [F',he]))
    (fun s hs z => by
      simpa only [inner_zero_left,add_zero] using
        ((hasDerivAt_const s (η z)).inner ℝ (hd s hs z)).const_mul (ρ z)) htpos
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with z
  exact congrArg (fun w => ρ z * ⟪η z,w⟫) (hd t htpos z).deriv

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_oai.{u_1}
