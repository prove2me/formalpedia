-- Prove2me | solution 1 for OAI.TamingCompatibility.taming_implies_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:30.885204+00:00
-- url     : https://prove2.me/submissions/7119c2a3-241d-4bb2-8491-14a21f1dac8f

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc024
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_concentration_forces_correction_zero
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalConcentration_Q_control
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalConcentration_current_control
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalConcentration_volume_limit
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_separating_current_L2_correction

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_BundleTotalSpaceT2
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Filter
open scoped Topology

lemma bundle_totalSpace_t2 {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [T2Space B] [T2Space F] (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle F E] : T2Space (TotalSpace F E) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro p q hpq
  by_cases hb : p.proj = q.proj
  · let e := trivializationAt F E p.proj
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hq : q ∈ e.source := e.mem_source.mpr (hb ▸ mem_baseSet_trivializationAt F E p.proj)
    have he : e p ≠ e q := fun h => hpq (e.injOn hp hq h)
    exact (e.toOpenPartialHomeomorph.continuousAt hp).disjoint
      (disjoint_nhds_nhds.mpr he) (e.toOpenPartialHomeomorph.continuousAt hq)
  · exact (FiberBundle.continuous_proj F E).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hb) (FiberBundle.continuous_proj F E).continuousAt
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JAction
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

theorem Tames.isNondegenerate {α : TwoForm X} {J : AlmostComplexStructure X}
    (h : Tames α J) : IsNondegenerate α := by
  intro x v hv
  by_contra hn
  exact (ne_of_gt (h x v hn)) (hv (J.endomorphism x v))

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartUnitaryData
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
open scoped Manifold ContDiff SchwartzMap
namespace TamingCompatibility.GeometricChart
open ManifoldHodge ManifoldVolume ManifoldForms
open MetricModel MetricForms MetricHodge AntiInvariantFrame EuclideanEnergy LocalMatrixOperator
open _root_.MeasureTheory Set
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace Data
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : Data J α ht p)
lemma source_open : IsOpen D.source := by
  exact (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) Metric.isOpen_ball
lemma mem_source : p ∈ D.source := ⟨mem_extChartAt_source p,Metric.mem_ball_self D.radius_pos⟩
end Data

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldScalarCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in
lemma scalarDifferential_comp {f : X → ℝ} (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f)
    {g : ℝ → ℝ} {g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' (f x)) (f x)) :
    scalarDifferential (g ∘ f) = fun x => g' (f x) • scalarDifferential f x := by
  funext x
  unfold scalarDifferential
  rw [mfderiv_comp x ((hg x).differentiableAt.mdifferentiableAt) (hf x),mfderiv_eq_fderiv,
    (hg x).hasFDerivAt.fderiv]
  erw [←map_smul]
  congr 1
  ext v
  let L : Space →L[ℝ] ℝ := mfderiv Model 𝓘(ℝ,ℝ) f x
  change L v * g' (f x) = g' (f x) * L v
  ring

omit [IsManifold Model ∞ X] in
lemma wedgeOne_fun_smul_left (f : X → ℝ) (a b : Form X 1) :
    wedgeOne (fun x => f x • a x) b = fun x => f x • wedgeOne a b x := by
  funext x
  change ExteriorForms.wedgeOne (E := Space) (ExteriorForms.oneLinear (E := Space) (f x • a x)) (b x) = _
  dsimp only [ExteriorForms.oneLinear]
  erw [_root_.map_smul]
  exact _root_.map_smul (ExteriorForms.wedgeOneRight (E := Space) (b x)) _ _
end TamingCompatibility.ManifoldForms

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_SummableCutoff
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory Finset
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X : Type*}

lemma exceptional_null [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n))
    (ν : Measure X) (hs : (∑' n, ∫⁻ x, ENNReal.ofReal (c n x) ∂ν) ≠ ∞) :
    ν (exceptional c) = 0 := by
  have hsum : ∫⁻ x, ∑' n, ‖c n x‖ₑ ∂ν ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hm n).enorm.aemeasurable)]
    simpa only [Real.enorm_eq_ofReal (hc _ _)] using hs
  have hae := ae_lt_top (Measurable.tsum (fun n => (hm n).enorm)) hsum
  change ν {x | ¬ Summable (fun n => c n x)} = 0
  rw [← ae_iff]
  filter_upwards [hae] with x hx
  have := tsum_enorm_ne_top_iff_summable_norm.1 hx.ne
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hc _ x)] using this

end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_SlowLogCutoff
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace TamingCompatibility.SummableCutoff

lemma logActivation_nonneg {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 ≤ logActivation ε δ t := by
  apply mul_nonneg hε
  apply Real.log_nonneg
  have : 0 ≤ t/δ := div_nonneg ht hδ.le
  linarith

lemma logActivation_le {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (ht : 0 ≤ t) :
    logActivation ε δ t ≤ (ε/δ)*t := by
  calc
    _ ≤ ε*((1+t/δ)-1) := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity)) hε
    _ = _ := by ring

lemma hasDerivAt_logActivation {ε δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    HasDerivAt (logActivation ε δ) (ε/(δ+t)) t := by
  have hp : 0 < 1+t/δ := by positivity
  have hh := (((hasDerivAt_id t).div_const δ).const_add 1).log hp.ne'
  have he : ε * (1 / δ / (1 + t / δ)) = ε / (δ+t) := by
    field_simp
  convert! hh.const_mul ε using 1
  all_goals try with_reducible_and_instances rfl
  simpa only [id_eq] using he.symm

lemma logActivation_threshold {ε δ a t : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (ha : δ*Real.exp (1/ε) ≤ a) (ht : a ≤ t) : 1 ≤ logActivation ε δ t := by
  have hx : Real.exp (1/ε) ≤ 1+t/δ := by
    have hh := (le_div_iff₀ hδ).2 (show Real.exp (1/ε)*δ ≤ t by simpa only [mul_comm] using ha.trans ht)
    linarith
  have hlog := Real.log_le_log (Real.exp_pos (1/ε)) hx
  rw [Real.log_exp] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hε.le
  have he : ε*(1/ε) = 1 := by field_simp
  exact he ▸ hm

lemma threshold_scale_pos {ε a : ℝ} (_hε : 0 < ε) (ha : 0 < a) :
    0 < a*Real.exp (-(1/ε)) ∧
      (a*Real.exp (-(1/ε)))*Real.exp (1/ε) ≤ a := by
  refine ⟨mul_pos ha (Real.exp_pos _),?_⟩
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]

lemma tendsto_of_summable_activation {c f a : ℕ → ℝ}
    (hc : Summable c) (hf : ∀ n, 0 ≤ f n)
    (ha : Tendsto a atTop (𝓝 0))
    (hthreshold : ∀ n, a n ≤ f n → 1 ≤ c n) :
    Tendsto f atTop (𝓝 0) := by
  have he : ∀ᶠ n in atTop, f n ≤ a n := by
    filter_upwards [hc.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
    exact le_of_lt (lt_of_not_ge (fun h => (not_le_of_gt hn) (hthreshold n h)))
  exact squeeze_zero' (Eventually.of_forall hf) he ha

end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ActivationScales
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff

lemma stepSize_pos (n : ℕ) : 0 < stepSize n := pow_pos (by norm_num) _
lemma stepSize_le_one (n : ℕ) : stepSize n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
lemma summable_stepSize : Summable stepSize := summable_geometric_of_abs_lt_one (by norm_num)
lemma tendsto_stepSize : Tendsto stepSize atTop (𝓝 0) := summable_stepSize.tendsto_atTop_zero

lemma thresholdScale_pos (n : ℕ) : 0 < thresholdScale n := mul_pos (stepSize_pos n) (Real.exp_pos _)
lemma logActivation_step_threshold (n : ℕ) {t : ℝ} (h : stepSize n ≤ t) :
    1 ≤ logActivation (stepSize n) (thresholdScale n) t := by
  exact logActivation_threshold (stepSize_pos n) (thresholdScale_pos n)
    (threshold_scale_pos (stepSize_pos n) (stepSize_pos n)).2 h

lemma exists_activation_scales (f g h : ℝ → ℝ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 0)) (hg : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hh : Tendsto h (𝓝[>] 0) (𝓝 0)) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n ≤ 1) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ n, f (r n) ≤ thresholdScale n ∧ g (r n) ≤ thresholdScale n ∧ h (r n) ≤ thresholdScale n := by
  have he (n : ℕ) : ∃ r : ℝ, 0 < r ∧ r ≤ stepSize n ∧
      f r ≤ thresholdScale n ∧ g r ≤ thresholdScale n ∧ h r ≤ thresholdScale n := by
    have hr : ∀ᶠ r in 𝓝[>] (0:ℝ), r < stepSize n :=
      nhdsWithin_le_nhds (gt_mem_nhds (stepSize_pos n))
    obtain ⟨r,hrpos,hrn,hfr,hgr,hhr⟩ :=
      ((show ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r from self_mem_nhdsWithin).and (hr.and
        ((hf.eventually (gt_mem_nhds (thresholdScale_pos n))).and
          ((hg.eventually (gt_mem_nhds (thresholdScale_pos n))).and
            (hh.eventually (gt_mem_nhds (thresholdScale_pos n))))))).exists
    exact ⟨r,hrpos,hrn.le,hfr.le,hgr.le,hhr.le⟩
  choose r hr hsmall hbound using he
  refine ⟨r,fun n => ⟨hr n,(hsmall n).trans (stepSize_le_one n)⟩,?_,hbound⟩
  exact squeeze_zero (fun n => (hr n).le) hsmall tendsto_stepSize

lemma logActivation_integral_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hf : ∀ x, 0 ≤ f x)
    (hi : Integrable f μ) (hc : Integrable (fun x => logActivation ε δ (f x)) μ) :
    (∫ x, logActivation ε δ (f x) ∂μ) ≤ (ε/δ)*(∫ x, f x ∂μ) := by
  rw [← integral_const_mul]
  exact integral_mono hc (hi.const_mul _) (fun x => logActivation_le hε hδ (hf x))

lemma weighted_nonneg_ratio_bound {ε δ t e : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (ht : 0 ≤ t) (he : 0 ≤ e) :
    (ε/(δ+t))*(t+e) ≤ ε+(ε/δ)*e := by
  have hd : 0 < δ+t := by positivity
  have ht' : (ε/(δ+t))*t ≤ ε := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hd]
    nlinarith
  have he' : (ε/(δ+t))*e ≤ (ε/δ)*e :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hε hδ (by linarith)) he
  nlinarith
end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ActivationMeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X : Type*} [MeasurableSpace X]

lemma activation_boundary_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (f e g : X → ℝ) (ε δ C : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hf : ∀ x, 0 ≤ f x) (he : ∀ x, 0 ≤ e x) (hei : Integrable e μ)
    (heg : (∫ x, e x ∂μ) ≤ δ) (hg : Integrable g μ)
    (hbound : ∀ x, g x ≤ (ε/(δ+f x))*(C*(f x+e x))) :
    (∫ x, g x ∂μ) ≤ 2*C*ε := by
  calc
    _ ≤ ∫ x, C*(ε+(ε/δ)*e x) ∂μ := integral_mono hg
      (((integrable_const ε).add (hei.const_mul (ε/δ))).const_mul C) (fun x => by
        apply (hbound x).trans
        have hh := mul_le_mul_of_nonneg_left (weighted_nonneg_ratio_bound hε hδ (hf x) (he x)) hC
        nlinarith)
    _ = C*(ε+(ε/δ)*(∫ x, e x ∂μ)) := by
      rw [integral_const_mul,integral_add (integrable_const _) (hei.const_mul _),
        integral_const_mul,integral_const]
      simp
    _ ≤ C*(ε+(ε/δ)*δ) := mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left heg (show 0 ≤ ε/δ by positivity)) _) hC
    _ = _ := by field_simp <;> ring

lemma activation_error_integral (μ : Measure X)
    (f e g : X → ℝ) (ε δ C : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hf : ∀ x, 0 ≤ f x) (he : ∀ x, 0 ≤ e x) (hei : Integrable e μ)
    (heg : (∫ x, e x ∂μ) ≤ δ) (hg : Integrable g μ)
    (hbound : ∀ x, g x ≤ (ε/(δ+f x))*(C*e x)) :
    (∫ x, g x ∂μ) ≤ C*ε := by
  calc
    _ ≤ ∫ x, (ε/δ)*(C*e x) ∂μ := integral_mono hg
      ((hei.const_mul C).const_mul _) (fun x => (hbound x).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hε hδ (by linarith [hf x]))
          (mul_nonneg hC (he x))))
    _ = (ε/δ)*(C*(∫ x, e x ∂μ)) := by rw [integral_const_mul,integral_const_mul]
    _ ≤ (ε/δ)*(C*δ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left heg hC) (by positivity)
    _ = _ := by field_simp

lemma exceptional_null_of_integrals (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n))
    (ν : Measure X) (hi : ∀ n, Integrable (c n) ν)
    (e : ℕ → ℝ) (hes : Summable e) (hb : ∀ n, (∫ x, c n x ∂ν) ≤ e n) :
    ν (exceptional c) = 0 := by
  apply exceptional_null c hc hm ν
  apply ne_top_of_le_ne_top (hes.tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (hc n))]
  exact ENNReal.ofReal_le_ofReal (hb n)
end TamingCompatibility.SummableCutoff

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]

lemma contMDiff_logActivation {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) {ε δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x, 0 ≤ f x) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ (fun x => SummableCutoff.logActivation ε δ (f x)) := by
  intro x
  have hx := hpos x
  apply contMDiffAt_const.mul
  exact (Real.contDiffAt_log.mpr (show 1+f x/δ ≠ 0 by positivity)).comp_contMDiffAt
    (f := fun y => 1+f y/δ) (contMDiffAt_const.add ((hf x).div_const δ))

lemma scalarDifferential_logActivation {f : X → ℝ}
    (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f) {ε δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x, 0 ≤ f x) :
    scalarDifferential (fun x => SummableCutoff.logActivation ε δ (f x)) =
      fun x => (ε/(δ+f x)) • scalarDifferential f x :=
  scalarDifferential_comp hf (g := SummableCutoff.logActivation ε δ)
    (g' := fun t => ε/(δ+t)) (fun x => SummableCutoff.hasDerivAt_logActivation hδ (hpos x))

end TamingCompatibility.ManifoldForms

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PositiveFunctions
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility

section CompactFunctions

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

omit [Nonempty K] in
lemma convex_positiveFunctions : Convex ℝ (positiveFunctions (K := K)) := by
  intro f hf g hg a b ha hb hab x
  change 0 < a * f x + b * g x
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hg x
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (hf x))
      (mul_nonneg hb (hg x).le)

lemma isOpen_positiveFunctions : IsOpen (positiveFunctions (K := K)) := by
  rw [Metric.isOpen_iff]
  intro f hf
  obtain ⟨x₀, _, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) f.continuous.continuousOn
  refine ⟨f x₀, hf x₀, ?_⟩
  intro g hg x
  have hdist := ContinuousMap.dist_apply_le_dist (f := g) (g := f) x
  have hball : dist g f < f x₀ := hg
  have hlo : f x₀ ≤ f x := hmin (Set.mem_univ x)
  rw [Real.dist_eq] at hdist
  have hl := (abs_le.mp hdist).1
  linarith

theorem exists_normalized_positive_annihilator
    (L : Submodule ℝ C(K, ℝ))
    (hL : Disjoint (positiveFunctions (K := K)) (L : Set C(K, ℝ))) :
    ∃ Λ : C(K, ℝ) →L[ℝ] ℝ, Λ 1 = 1 ∧
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ Λ f) ∧ ∀ f ∈ L, Λ f = 0 := by
  obtain ⟨φ, u, hp, hl⟩ := geometric_hahn_banach_open
    convex_positiveFunctions isOpen_positiveFunctions L.convex hL
  have hu : u ≤ 0 := by simpa using hl 0 L.zero_mem
  have hφ1 : φ 1 < 0 := (hp 1 (fun _ => zero_lt_one)).trans_le hu
  have hz (f : C(K, ℝ)) (hf : f ∈ L) : φ f = 0 := by
    by_contra hne
    have h := hl (((u - 1) / φ f) • f) (L.smul_mem _ hf)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
    linarith
  have hn (f : C(K, ℝ)) (hf : ∀ x, 0 ≤ f x) : φ f ≤ 0 := by
    by_contra! hpos
    let c : ℝ := -φ 1 / φ f + 1
    have hc : 0 < c := by
      dsimp [c]
      exact add_pos (div_pos (neg_pos.mpr hφ1) hpos) zero_lt_one
    have hp' : c • f + 1 ∈ positiveFunctions (K := K) := by
      intro x
      change 0 < c * f x + 1
      exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le (hf x)) zero_lt_one
    have h := (hp _ hp').trans_le hu
    rw [map_add, map_smul, smul_eq_mul] at h
    dsimp [c] at h
    rw [add_mul, div_mul_cancel₀ _ hpos.ne'] at h
    linarith
  refine ⟨(φ 1)⁻¹ • φ, ?_, ?_, ?_⟩
  · change (φ 1)⁻¹ * φ 1 = 1
    exact inv_mul_cancel₀ hφ1.ne
  · intro f hf
    change 0 ≤ (φ 1)⁻¹ * φ f
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hφ1.le) (hn f hf)
  · intro f hf
    change (φ 1)⁻¹ * φ f = 0
    rw [hz f hf, mul_zero]

variable [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem exists_probability_annihilating_subspace
    (L : Submodule ℝ C(K, ℝ))
    (hL : Disjoint (positiveFunctions (K := K)) (L : Set C(K, ℝ))) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ f ∈ L, ∫ x, f x ∂μ = 0 := by
  obtain ⟨Λ, hΛ1, hΛpos, hΛL⟩ := exists_normalized_positive_annihilator L hL
  let Ψ : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => Λ f.toContinuousMap
      map_add' := fun f g => by change Λ (f.toContinuousMap + g.toContinuousMap) = _; exact map_add Λ _ _
      map_smul' := fun c f => by change Λ (c • f.toContinuousMap) = _; exact map_smul Λ _ _
      monotone' := by
        intro f g hfg
        have h := hΛpos (g.toContinuousMap - f.toContinuousMap) (fun x => sub_nonneg.mpr (hfg x))
        rw [map_sub] at h
        exact sub_nonneg.mp h }
  let μ := RealRMK.rieszMeasure Ψ
  have hrepr (f : C(K, ℝ)) : ∫ x, f x ∂μ = Λ f := by
    let fc : C_c(K, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure Ψ fc
  have hmass : μ Set.univ = 1 := by
    have h := hrepr 1
    simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one, hΛ1] at h
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.one_ne_top).mp
    simpa only [Measure.real, ENNReal.toReal_one] using h
  exact ⟨μ, ⟨hmass⟩, inferInstance, fun f hf => (hrepr f).trans (hΛL f hf)⟩

end CompactFunctions

open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedUnitEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma metric_normalize (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) (x : X) (v : TangentSpace Model x) (hv : v ≠ 0) :
    g.inner x ((Real.sqrt (g.inner x v v))⁻¹ • v)
      ((Real.sqrt (g.inner x v v))⁻¹ • v) = 1 := by
  have hp := g.pos x v hv
  have hs : Real.sqrt (g.inner x v v) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]
  field_simp
  nlinarith [Real.sq_sqrt hp.le]

instance instNonemptyMetricUnit [Nonempty X] (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : Nonempty (MetricUnit g) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let : Nontrivial (TangentSpace Model x) := inferInstanceAs (Nontrivial Space)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace Model x)
  exact ⟨⟨⟨x, (Real.sqrt (g.inner x v v))⁻¹ • v⟩, metric_normalize g x v hv⟩⟩

lemma tames_iff_unitEvaluation_pos (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (α : TwoForm X) (hα : IsSmooth α) :
    Tames α J ↔ ∀ p, 0 < unitEvaluation J g α hα p := by
  constructor
  · intro h p
    apply h p.val.proj p.val.2
    intro hz
    have hp := p.property
    rw [hz, map_zero] at hp
    norm_num at hp
  · intro h x v hv
    let c := (Real.sqrt (g.inner x v v))⁻¹
    have hu : g.inner x (c • v) (c • v) = 1 := metric_normalize g x v hv
    have hp := h ⟨⟨x, c • v⟩, hu⟩
    change 0 < eval α x (c • v) (J.endomorphism x (c • v)) at hp
    rw [← associatedBilinear_apply] at hp
    simp only [map_smul, _root_.smul_apply, smul_eq_mul] at hp
    rw [associatedBilinear_apply] at hp
    have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr (g.pos x v hv))
    exact (mul_pos_iff_of_pos_left hc).mp ((mul_pos_iff_of_pos_left hc).mp hp)

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_GeometricSeparatingProbability
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

local instance unitT2 [T2Space X] (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : T2Space (MetricUnit g) := by
  let : T2Space (TangentBundle Model X) := bundle_totalSpace_t2 (TangentSpace Model : X → Type)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

attribute [local instance] OAI.TamingCompatibility.unitMeasurable
attribute [local instance] OAI.TamingCompatibility.unitBorel
theorem exists_geometric_separating_probability [CompactSpace X] [T2Space X] [Nonempty X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (hno : ¬ ∃ α : TwoForm X, IsSymplectic α ∧ Compatible α J) :
    ∃ μ : Measure (MetricUnit g), IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ (α : TwoForm X) (hα : IsSmooth α), IsClosed α → IsInvariant α J →
        ∫ p, unitEvaluation J g α hα p ∂μ = 0 := by
  let L := LinearMap.range (closedUnitEvaluation J g)
  have hd : Disjoint (positiveFunctions (K := MetricUnit g)) (L : Set C(MetricUnit g, ℝ)) := by
    rw [Set.disjoint_left]
    intro f hf hL
    obtain ⟨α, rfl⟩ := hL
    have ht : Tames α.val J :=
      (tames_iff_unitEvaluation_pos J g α.val α.property.1).mpr hf
    exact hno ⟨α.val, ⟨α.property.1, α.property.2.1, ht.isNondegenerate⟩,
      ht, α.property.2.2⟩
  obtain ⟨μ, hμ, hreg, hann⟩ := exists_probability_annihilating_subspace L hd
  refine ⟨μ, hμ, hreg, ?_⟩
  intro α hα hc hi
  exact hann _ ⟨⟨α, hα, hc, hi⟩, rfl⟩

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothUnitEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]
attribute [local instance] unitMeasurable unitBorel unitT2

lemma unitMeasureCurrent_pos [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsProbabilityMeasure μ]
    (α : TwoForm X) (hα : IsSmooth α) (ht : Tames α J) :
    0 < unitMeasureCurrent J g μ ⟨α, hα⟩ := by
  let f := unitEvaluation J g α hα
  have hf : ∀ p, 0 < f p := (tames_iff_unitEvaluation_pos J g α hα).mp ht
  have hi := f.continuous.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace f)
  change 0 < ∫ p, f p ∂μ
  rw [integral_pos_iff_support_of_nonneg (fun p => (hf p).le) hi]
  have hs : Function.support f = Set.univ := by
    ext p
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hf p).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

lemma hermitianMetric_unitEvaluation (J : AlmostComplexStructure X)
    (α : TwoForm X) (hα : IsSmooth α) (ht : Tames α J) :
    unitEvaluation J (hermitianMetric J α hα ht)
      (invariantPart J α) (hα.invariantPart J) = 1 := by
  ext p
  change eval (invariantPart J α) p.val.proj p.val.2
    (J.endomorphism p.val.proj p.val.2) = 1
  rw [← associatedBilinear_apply]
  exact p.property

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space _root_.OAI.TamingCompatibility.instNonemptyMetricUnit
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
lemma source_open : IsOpen D.source :=
  (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) Metric.isOpen_ball

lemma mem_source : p ∈ D.source :=
  ⟨mem_extChartAt_source p,Metric.mem_ball_self (half_pos D.radius_pos)⟩

lemma source_subset : D.source ⊆ (extChartAt Model p).source := Set.inter_subset_left

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_UnitMeasureBound
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]
attribute [local instance] unitMeasurable unitBorel unitT2

lemma unitMeasureCurrent_normalized [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (hα : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hα ht))) [IsProbabilityMeasure μ] :
    unitMeasureCurrent J (hermitianMetric J α hα ht) μ
      ⟨invariantPart J α, hα.invariantPart J⟩ = 1 := by
  change (∫ p, unitEvaluation J (hermitianMetric J α hα ht)
    (invariantPart J α) (hα.invariantPart J) p ∂μ) = 1
  rw [hermitianMetric_unitEvaluation]
  simp

theorem exists_geometric_separating_current [CompactSpace X] [T2Space X] [Nonempty X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (hα : IsSmooth α) (ht : Tames α J)
    (hn : ¬ ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J) :
    ∃ μ : Measure (MetricUnit (hermitianMetric J α hα ht)),
      ∃ hμ : IsProbabilityMeasure μ,
      letI := hμ
      μ.Regular ∧
      let P := unitMeasureCurrent J (hermitianMetric J α hα ht) μ
      P ⟨invariantPart J α, hα.invariantPart J⟩ = 1 ∧
      (∀ β : ManifoldForms.smoothForms X 2,
        IsClosed β.val → IsInvariant β.val J → P β = 0) ∧
      (∀ β : ManifoldForms.smoothForms X 2, Tames β.val J → 0 < P β) := by
  obtain ⟨μ, hμ, hr, hz⟩ := exists_geometric_separating_probability J
    (hermitianMetric J α hα ht) hn
  let := hμ
  refine ⟨μ, hμ, hr, unitMeasureCurrent_normalized J α hα ht μ, ?_, ?_⟩
  · intro β hβc hβi
    exact hz β.val β.property hβc hβi
  · intro β hβ
    exact unitMeasureCurrent_pos J _ μ β.val β.property hβ

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldBoundaryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma log_boundary_eval (J : AlmostComplexStructure X) (f : X → ℝ)
    (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f) (hpos : ∀ x, 0 ≤ f x)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (θ : Form X 1) (x : X) (v : TangentSpace Model x) :
    |eval (ManifoldForms.wedgeOne
      (scalarDifferential (fun x => SummableCutoff.logActivation ε δ (f x))) θ) x v (J.endomorphism x v)| =
      (ε/(δ+f x))*|eval (ManifoldForms.wedgeOne (scalarDifferential f) θ) x v (J.endomorphism x v)| := by
  rw [scalarDifferential_logActivation hf hδ hpos,wedgeOne_fun_smul_left]
  simp only [eval,ContinuousAlternatingMap.smul_apply,smul_eq_mul,abs_mul,
    abs_of_nonneg (show 0 ≤ ε/(δ+f x) by have := hpos x; positivity)]

variable [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (ht : Tames α J) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

omit [T2Space X] [CompactSpace X] in
lemma log_boundary_norm (f : X → ℝ) (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f)
    (hpos : ∀ x, 0 ≤ f x) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (θ : Form X 1) (x : X) :
    ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne
      (scalarDifferential (fun x => SummableCutoff.logActivation ε δ (f x))) θ x)‖ =
      (ε/(δ+f x))*‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential f) θ x)‖ := by
  rw [scalarDifferential_logActivation hf hδ hpos,wedgeOne_fun_smul_left]
  erw [_root_.map_smul]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ ε/(δ+f x) by have := hpos x; positivity)]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_TripleAtlas
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space _root_.OAI.TamingCompatibility.instNonemptyMetricUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]

lemma finite_triple_partition
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J) :
    ∃ A : FiniteCharts X,
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (parametrixData J α hs ht p.val).source) ∧
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (HodgeChart.data J α hs ht p.val).source) ∧
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (GeometricChart.data J α hs ht p.val).source) := by
  classical
  let U : X → Set X := fun p => (parametrixData J α hs ht p).source ∩
    (HodgeChart.data J α hs ht p).source ∩ (GeometricChart.data J α hs ht p).source
  have hU (p : X) : IsOpen (U p) :=
    ((parametrixData J α hs ht p).source_open.inter (HodgeChart.data J α hs ht p).source_open).inter
      (GeometricChart.data J α hs ht p).source_open
  have hp (p : X) : p ∈ U p :=
    ⟨⟨(parametrixData J α hs ht p).mem_source,(HodgeChart.data J α hs ht p).mem_source⟩,
      (GeometricChart.data J α hs ht p).mem_source⟩
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun p _ => mem_iUnion_of_mem p (hp p))
  have hc : (univ : Set X) ⊆ ⋃ p : s, U p.val := by
    intro x hx
    obtain ⟨p,hp',hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp'⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => U p.val) (fun p => hU p.val) hc
  let A : FiniteCharts X := ⟨s,ρ,fun p => (hρ p).trans
    (inter_subset_left.trans (inter_subset_left.trans (parametrixData J α hs ht p.val).source_subset))⟩
  exact ⟨A,fun p => (hρ p).trans (inter_subset_left.trans inter_subset_left),
    fun p => (hρ p).trans (inter_subset_left.trans inter_subset_right),
    fun p => (hρ p).trans inter_subset_right⟩
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_nonneg (r : ℝ) (z : V) : 0 ≤ rationalKernel r z := by
  unfold rationalKernel
  positivity

end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationChart
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian NormalMetricCalculus CoordinateOperator
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}

variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel unitT2

omit [T2Space X] [CompactSpace X] in
lemma concentrationPatch_apply (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) (x : X) : concentrationPatch A J α hs ht E μ p r x =
      A.partition p x*localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) := by
  by_cases hx : x ∈ (extChartAt Model p.val).source
  · simp only [concentrationPatch,scalarChartLift,ite_eq_left hx,coordinatePartition_apply A p hx]
  · have he : A.partition p x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.subordinate p h))
    simp only [concentrationPatch,scalarChartLift,ite_eq_right hx,he,zero_mul]

lemma globalConcentration_smooth (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (globalConcentration A J α hs ht E μ r) := by
  classical
  exact contMDiff_finsetSum' (fun p _ => concentrationPatch_smooth A J α hs ht E μ p hr)

omit [T2Space X] [CompactSpace X] in
lemma localConcentration_nonneg (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) (b : Space) : 0 ≤ localConcentration A J α hs ht E μ p r b := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (E p).concentrationCutoff.bump.nonneg (rationalKernel_nonneg _ _)

omit [T2Space X] [CompactSpace X] in
lemma globalConcentration_nonneg (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (r : ℝ) (x : X) : 0 ≤ globalConcentration A J α hs ht E μ r x := by
  classical
  simp only [globalConcentration,Finset.sum_apply]
  apply Finset.sum_nonneg
  intro p _
  rw [concentrationPatch_apply]
  exact mul_nonneg (A.partition.nonneg _ _) (localConcentration_nonneg A J α hs ht E μ p r _)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationGlobalError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

omit [ConnectedSpace X] in
lemma globalConcentration_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) :
    Integrable (globalConcentration A J α hs ht E μ r) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (globalConcentration_smooth A J α hs ht E μ hr).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarBoundaryIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

omit [MeasurableSpace X] [BorelSpace X] in
lemma unit_boundary_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    Integrable (fun u : MetricUnit (hermitianMetric J α hs ht) =>
      |eval (ManifoldForms.wedgeOne (scalarDifferential f) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)|) μ :=
  (smoothUnitEvaluation J (hermitianMetric J α hs ht)
    ⟨_,smooth_boundary f hf θ⟩).continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include hE in
lemma coefficient_boundary_integrable
    (Q : L2 A J α hs ht true) (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (θ : smoothForms X 1) :
    Integrable (fun x => ‖l2Coefficients A J α hs ht E hE Q x‖ *
      ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential f) θ.val x)‖)
      (geometricVolume A J α) := by
  let q := l2Coefficients A J α hs ht E hE Q
  have hb := smoothFrameEncode_memLp A J α hs ht E hE ⟨_,smooth_boundary f hf θ⟩
  exact (Lp.memLp q).norm.integrable_mul hb.norm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationActivations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

include hE hD hG in
lemma concentrationActivationData_nonempty
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) :
    Nonempty (ConcentrationActivationData A J α hs ht E hE μ Q) := by
  obtain ⟨eP,heP,hiP,h0P,hbP⟩ := globalConcentration_current_control A J α hs ht E hE D hD G hG μ hann Q hT
  obtain ⟨eQ,heQ,hiQ,h0Q,hbQ⟩ := globalConcentration_Q_control A J α hs ht E hE μ hann Q
  obtain ⟨r,hr,hr0,hrb⟩ := exists_activation_scales
    (fun r => ∫ u, eP r u ∂μ) (fun r => ∫ x, eQ r x ∂geometricVolume A J α)
    (fun r => ∫ x, globalConcentration A J α hs ht E μ r x ∂geometricVolume A J α)
    h0P h0Q (globalConcentration_volume_limit A J α hs ht E hE μ)
  let f := fun n => globalConcentration A J α hs ht E μ (r n)
  have hf (n) := globalConcentration_smooth A J α hs ht E μ (hr n).1
  have hfn (n) := globalConcentration_nonneg A J α hs ht E μ (r n)
  let c := fun n x => logActivation (stepSize n) (thresholdScale n) (f n x)
  have hc (n) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (c n) := contMDiff_logActivation (hf n) (thresholdScale_pos n) (hfn n)
  have hcn (n) (x) : 0 ≤ c n x := logActivation_nonneg (stepSize_pos n).le (thresholdScale_pos n) (hfn n x)
  let := geometricVolume_finite A J α hs ht
  have hci (n) : Integrable (c n) (geometricVolume A J α) :=
    (hc n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcv (n) : (∫ x, c n x ∂geometricVolume A J α) ≤ stepSize n := by
    apply (logActivation_integral_bound (geometricVolume A J α) (f n) _ _ (stepSize_pos n).le
      (thresholdScale_pos n) (hfn n) (globalConcentration_integrable A J α hs ht E μ (hr n).1) (hci n)).trans
    have hh := mul_le_mul_of_nonneg_left (hrb n).2.2
      (div_nonneg (stepSize_pos n).le (thresholdScale_pos n).le)
    simpa only [div_mul_cancel₀ _ (thresholdScale_pos n).ne'] using hh
  refine ⟨⟨r,fun n => (hr n).1,fun n => (hr n).2,hr0,c,hcn,hc,
    exceptional_null_of_integrals c hcn (fun n => (hc n).continuous.measurable)
      (geometricVolume A J α) hci stepSize summable_stepSize hcv,?_,?_,?_⟩⟩
  · intro x hx
    have hsum : Summable (fun n => c n x) := not_not.mp hx
    exact tendsto_of_summable_activation hsum (fun n => hfn n x) tendsto_stepSize
      (fun n hn => logActivation_step_threshold n hn)
  · intro θ
    obtain ⟨C,hC,hb⟩ := hbP θ
    refine ⟨2*C,by positivity,fun n => ?_⟩
    apply activation_boundary_integral μ (fun u => f n u.val.proj) (eP (r n))
      (fun u => |eval (ManifoldForms.wedgeOne (scalarDifferential (c n)) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)|)
      (stepSize n) (thresholdScale n) C (stepSize_pos n).le (thresholdScale_pos n) hC
      (fun u => hfn n u.val.proj) (heP _ (hr n).1) (hiP _ (hr n).1) (hrb n).1
      (unit_boundary_integrable J α hs ht μ (c n) (hc n) θ)
    intro u
    rw [show c n = fun x => logActivation (stepSize n) (thresholdScale n) (f n x) from rfl,
      log_boundary_eval J _ ((hf n).mdifferentiable (by simp)) (hfn n) (stepSize_pos n).le (thresholdScale_pos n)]
    exact mul_le_mul_of_nonneg_left (hb _ (hr n).1 u) (div_nonneg (stepSize_pos n).le (add_nonneg (thresholdScale_pos n).le (hfn n u.val.proj)))
  · intro θ
    obtain ⟨C,hC,hb⟩ := hbQ θ
    refine ⟨C,hC,fun n => ?_⟩
    apply activation_error_integral (geometricVolume A J α) (f n) (eQ (r n))
      (fun x => ‖l2Coefficients A J α hs ht E hE Q x‖ *
        ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential (c n)) θ.val x)‖)
      (stepSize n) (thresholdScale n) C (stepSize_pos n).le (thresholdScale_pos n) hC
      (hfn n) (heQ _ (hr n).1) (hiQ _ (hr n).1) (hrb n).2.1
      (coefficient_boundary_integrable A J α hs ht E hE Q (c n) (hc n) θ)
    intro x
    rw [show c n = fun x => logActivation (stepSize n) (thresholdScale n) (f n x) from rfl,
      log_boundary_norm A J α ht E _ ((hf n).mdifferentiable (by simp)) (hfn n) (stepSize_pos n).le (thresholdScale_pos n)]
    have hh := mul_le_mul_of_nonneg_left (hb _ (hr n).1 (hr n).2 x)
      (div_nonneg (stepSize_pos n).le (add_nonneg (thresholdScale_pos n).le (hfn n x)))
    nlinarith
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricHilbert GeometricHilbert.GeometricNormalCharts Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem taming_implies_compatibility_oai
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X]
    (J : AlmostComplexStructure X)
    (h : ∃ α : TwoForm X, IsSymplectic α ∧ Tames α J) :
    ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J := by
  classical
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨α,⟨hs,hc,_⟩,ht⟩ := h
  by_contra hn
  obtain ⟨A,hE,hD,hG⟩ := finite_triple_partition J α hs ht
  let E := fun p : A.centers => parametrixData J α hs ht p.val
  let D := fun p : A.centers => HodgeChart.data J α hs ht p.val
  let G := fun p : A.centers => GeometricChart.data J α hs ht p.val
  obtain ⟨μ,hμ,-,-,hann,-⟩ := exists_geometric_separating_current J α hs ht hn
  let := hμ
  obtain ⟨Q,haQ,hQ,hT,hnormal⟩ := separating_current_L2_correction J α hs ht hc A E hE D hD μ hann
  obtain ⟨S⟩ := concentrationActivationData_nonempty A J α hs ht E hE D hD G hG μ hann Q hT
  have hzero := concentration_forces_correction_zero A J α hs ht E hE D hD μ hann Q haQ hQ hT S
  rw [hzero,inner_zero_left] at hnormal
  norm_num at hnormal
end TamingCompatibility

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.taming_implies_compatibility_oai.{u_1} := @OAI.TamingCompatibility.taming_implies_compatibility_oai.{u_1}
