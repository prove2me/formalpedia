-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.subprob_anti_cross_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:15:38.450837+00:00
-- url     : https://prove2.me/submissions/2417169c-69b2-482f-9215-96bf3a18a24e

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc032
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_current_quantitative
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodgePositiveCurrentFamily_anti_cross_tendsto
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodge_regularized_positive_current_cross

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothingKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertKernel
open _root_.MeasureTheory
open scoped RealInnerProductSpace
variable {H F G A B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

lemma kernel_inner (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (x : A) (y : B) (a : F) (b : G) :
    ⟪a,kernel E D x y b⟫ = ⟪(E x).adjoint a,(D y).adjoint b⟫ := by
  exact (ContinuousLinearMap.adjoint_inner_left (E x) ((D y).adjoint b) a).symm

lemma regularize_pair [MeasurableSpace A] (μ : Measure A)
    (E : A → H →L[ℝ] F) (v : A → F)
    (hv : Integrable (fun x => (E x).adjoint (v x)) μ) (f : H) :
    ⟪regularize μ E v,f⟫ = ∫ x, ⟪v x,E x f⟫ ∂μ := by
  have h := (innerSL ℝ f).integral_comp_comm hv
  simp only [innerSL_apply_apply] at h
  rw [regularize,real_inner_comm,← h]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [real_inner_comm,ContinuousLinearMap.adjoint_inner_left]

lemma regularize_kernel_pair [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (v : A → F) (w : B → G)
    (hv : Integrable (fun x => (E x).adjoint (v x)) μ)
    (hw : Integrable (fun y => (D y).adjoint (w y)) ν) :
    ⟪regularize μ E v,regularize ν D w⟫ =
      ∫ x, ∫ y, ⟪v x,kernel E D x y (w y)⟫ ∂ν ∂μ := by
  rw [regularize_pair μ E v hv]
  apply integral_congr_ae
  filter_upwards [] with x
  have h := ((innerSL ℝ (v x)).comp (E x)).integral_comp_comm hw
  simpa only [regularize,ContinuousLinearMap.comp_apply,innerSL_apply_apply,kernel] using h.symm

end TamingCompatibility.HilbertKernel

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_QuadraticShell
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

lemma exists_dyadic_majorant {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    ∃ n : ℕ, d < 2^(n+1)*r ∧ (1+d/r)⁻¹^6 ≤ (1/64:ℝ)^n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near (le_max_left 1 (d/r)) (by norm_num : (1:ℝ)<2)
  have hbase : (2:ℝ)^n ≤ 1+d/r := hn.trans (max_le (le_add_of_nonneg_right (div_nonneg hd hr.le)) (by linarith))
  refine ⟨n,(div_lt_iff₀ hr).mp ((le_max_right 1 (d/r)).trans_lt hn'),?_⟩
  calc
    (1+d/r)⁻¹^6 ≤ ((2:ℝ)^n)⁻¹^6 := by
      gcongr
    _ = (1/64:ℝ)^n := by
      rw [← inv_pow,← pow_mul,Nat.mul_comm,pow_mul,inv_pow]
      norm_num

lemma profile_ofReal {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    profile r (ENNReal.ofReal d) = ENNReal.ofReal ((1+d/r)⁻¹^6) := by
  simp only [profile, ← ENNReal.ofReal_div_of_pos hr, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (div_nonneg hd hr.le)]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow (by positivity)]

lemma profile_top {r : ℝ} : profile r ⊤ = 0 := by
  simp [profile, ENNReal.top_div]

lemma profile_majorant {r : ℝ} (hr : 0 < r) (d : ℝ≥0∞) :
    profile r d ≤ ∑' n : ℕ,
      {e : ℝ≥0∞ | e < ENNReal.ofReal (2^(n+1)*r)}.indicator
        (fun _ => ENNReal.ofReal ((1/64:ℝ)^n)) d := by
  by_cases hd : d = ⊤
  · rw [hd,profile_top]; exact bot_le
  obtain ⟨n,hn,hbound⟩ := exists_dyadic_majorant hr d.toReal_nonneg
  have hdreal : ENNReal.ofReal d.toReal = d := ENNReal.ofReal_toReal hd
  have hn' : d < ENNReal.ofReal (2^(n+1)*r) := by
    rw [←hdreal]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hn
  calc
    _ = ENNReal.ofReal ((1+d.toReal/r)⁻¹^6) := by rw [←hdreal,profile_ofReal hr d.toReal_nonneg]; simp [hdreal]
    _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := by simp only [indicator, mem_ofPred_eq, hn', ↓reduceIte]
    _ ≤ _ := ENNReal.le_tsum n

lemma dyadic_term_identity (C r : ℝ) (n : ℕ) :
    (1/64:ℝ)^n*(C*(2^(n+1)*r)^2) = 4*C*r^2*(1/16:ℝ)^n := by
  have hpow : ((2:ℝ)^n)^2 = ((2:ℝ)^2)^n := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  calc
    _ = 4*C*r^2*((1/64:ℝ)^n*((2:ℝ)^2)^n) := by rw [pow_succ,←hpow]; ring
    _ = _ := by rw [←mul_pow]; norm_num

theorem lintegral_profile_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ y, profile r (δ y) ∂μ ≤ ENNReal.ofReal (8*C*r^2) := by
  let f : ℕ → Y → ℝ≥0∞ := fun n =>
    {y | δ y < ENNReal.ofReal (2^(n+1)*r)}.indicator
      (fun _ => ENNReal.ofReal ((1/64:ℝ)^n))
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_const.indicator (measurableSet_lt hδ measurable_const)
  have hi (n : ℕ) : ∫⁻ y, f n y ∂μ ≤ ENNReal.ofReal (4*C*r^2*(1/16:ℝ)^n) := by
    rw [lintegral_indicator_const (measurableSet_lt hδ measurable_const)]
    have hm : μ {y | δ y < ENNReal.ofReal (2^(n+1)*r)} ≤
        ENNReal.ofReal (C*(2^(n+1)*r)^2) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (hgrowth _ (by positivity))
    calc
      _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) * ENNReal.ofReal (C*(2^(n+1)*r)^2) :=
        by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), dyadic_term_identity]
  calc
    _ ≤ ∫⁻ y, ∑' n, f n y ∂μ := lintegral_mono fun y => profile_majorant hr (δ y)
    _ = ∑' n, ∫⁻ y, f n y ∂μ := lintegral_tsum fun n => (hf n).aemeasurable
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (4*C*r^2*(1/16:ℝ)^n) := ENNReal.tsum_le_tsum hi
    _ = ENNReal.ofReal (4*C*r^2) * (1-ENNReal.ofReal (1/16))⁻¹ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4*C*r^2), ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/16)]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (8*C*r^2) := by
      have hratio : (1-ENNReal.ofReal (1/16))⁻¹ ≤ ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/16)]
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1-1/16)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      calc
        _ ≤ ENNReal.ofReal (4*C*r^2)*ENNReal.ofReal 2 := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end QuadraticShell

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_QuadraticShellLimit
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
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

lemma profile_le_one (r : ℝ) (d : ℝ≥0∞) : profile r d ≤ 1 := by
  apply pow_le_one₀ bot_le
  exact ENNReal.inv_le_one.mpr le_self_add

lemma measurable_profile {Y : Type*} [MeasurableSpace Y]
    (δ : Y → ℝ≥0∞) (hδ : Measurable δ) (r : ℝ) :
    Measurable (fun y => profile r (δ y)) := by
  unfold profile
  fun_prop

lemma integral_profile_toReal {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : Y → ℝ≥0∞) (hδ : Measurable δ) (r : ℝ) :
    (∫ y, (profile r (δ y)).toReal ∂μ) = (∫⁻ y, profile r (δ y) ∂μ).toReal := by
  exact integral_toReal (measurable_profile δ hδ r).aemeasurable
    (Eventually.of_forall fun y => (profile_le_one r (δ y)).trans_lt (by simp))

lemma integral_profile_normalized_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) : (∫ y, (profile r (δ y)).toReal ∂μ)/r^2 ≤ 8*C := by
  rw [integral_profile_toReal μ δ hδ r]
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_profile_le μ δ hδ C hC hgrowth hr)
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr hle

end QuadraticShell

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolvent
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Filter Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeRegularization_norm_le (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeRegularization A J α hs ht r f‖ ≤ ‖f‖ := by
  change ‖hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f))‖ ≤ ‖f‖
  exact (hodgeResolvent_norm_le A J α hs ht r _).trans
    ((hodgeResolvent_norm_le A J α hs ht r _).trans (hodgeResolvent_norm_le A J α hs ht r f))
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma evaluationVector_continuous : Continuous (C.evaluationVector g) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.evaluation_continuous g)).clm_apply continuous_const

lemma evaluationVector_integrable (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    Integrable (C.evaluationVector g) μ :=
  (C.evaluationVector_continuous g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma regularize_inner (μ ν : Measure (MetricUnit g)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪C.regularize g μ,C.regularize g ν⟫ =
      ∫ u, ∫ v, C.innerKernel g u v ∂ν ∂μ := by
  have h := HilbertKernel.regularize_kernel_pair μ ν (C.evaluation g) (C.evaluation g)
    (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (C.evaluationVector_integrable g μ) (C.evaluationVector_integrable g ν)
  simpa only [regularize,HilbertKernel.regularize,innerKernel,evaluationVector,
    HilbertKernel.kernel_inner] using h

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalSmooth
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricAdjoint _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace GeometricHilbert
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

attribute [local instance] OAI.TamingCompatibility.instNormedAddCommGroupTangentSpaceRealSpaceModel_2
local instance instNormedSpaceRealTangentSpaceSpaceModel_2_r8233de_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
attribute [local instance] OAI.TamingCompatibility.instFiniteDimensionalRealTangentSpaceSpaceModel_2
lemma preJAction_square (a : PreL2 A J α hs ht true) :
    preJAction A J α hs ht (preJAction A J α hs ht a) = a :=
  Subtype.ext (jAction_involutive J a.val)

lemma l2JAction_square (a : L2 A J α hs ht true) :
    l2JAction A J α hs ht (l2JAction A J α hs ht a) = a := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq ((l2JAction A J α hs ht).continuous.comp
      (l2JAction A J α hs ht).continuous) continuous_id) ?_
  intro b
  rw [l2JAction_smooth,l2JAction_smooth,preJAction_square]

lemma l2JAction_norm (a : L2 A J α hs ht true) : ‖l2JAction A J α hs ht a‖ = ‖a‖ := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq (l2JAction A J α hs ht).continuous.norm continuous_norm) ?_
  intro b
  rw [l2JAction_smooth,(smoothL2 A J α hs ht true).norm_map,
    (preJAction A J α hs ht).norm_map,(smoothL2 A J α hs ht true).norm_map]

lemma l2JAction_self_adjoint (a b : L2 A J α hs ht true) :
    ⟪l2JAction A J α hs ht a,b⟫ = ⟪a,l2JAction A J α hs ht b⟫ := by
  let S : L2 A J α hs ht true →ₗᵢ[ℝ] L2 A J α hs ht true :=
    ⟨(l2JAction A J α hs ht).toLinearMap,l2JAction_norm A J α hs ht⟩
  conv_lhs => rw [← l2JAction_square A J α hs ht b]
  exact S.inner_map_map a (l2JAction A J α hs ht b)

lemma l2AntiProjection_smooth (a : PreL2 A J α hs ht true) :
    l2AntiProjection A J α hs ht (smoothL2 A J α hs ht true a) =
      smoothL2 A J α hs ht true ⟨antiInvariantPart J a.val,IsSmooth.antiInvariantPart a.property J⟩ := by
  rw [l2AntiProjection_apply,l2JAction_smooth,← map_sub,← map_smul]
  rfl

lemma l2AntiProjection_self_adjoint (a b : L2 A J α hs ht true) :
    ⟪l2AntiProjection A J α hs ht a,b⟫ = ⟪a,l2AntiProjection A J α hs ht b⟫ := by
  simp only [l2AntiProjection_apply,real_inner_smul_left,real_inner_smul_right,
    inner_sub_left,inner_sub_right,l2JAction_self_adjoint]

lemma l2AntiProjection_norm (a : L2 A J α hs ht true) :
    ‖l2AntiProjection A J α hs ht a‖ ≤ ‖a‖ := by
  rw [l2AntiProjection_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have h := norm_sub_le a (l2JAction A J α hs ht a)
  rw [l2JAction_norm] at h
  linarith

end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization _root_.MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable [T2Space X]
variable {A J α hs ht D hD}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma heatEvaluation_continuous : Continuous (C.heatEvaluation g) :=
  (C.evaluation_continuous g).clm_comp continuous_const

lemma heatEvaluationVector_continuous : Continuous (C.heatEvaluationVector g) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.heatEvaluation_continuous g)).clm_apply continuous_const

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelGammaBounds
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open _root_.MeasureTheory Set

lemma moment_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s^n * Real.exp (-(b*s))) (Ioi 0) := by
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)

lemma moment_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ s : ℝ in Ioi 0, s^n * Real.exp (-(b*s))) = moment n b := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1)
    (by positivity) hb
  simp_rw [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  have he : (n:ℝ)+1 = ((n+1:ℕ):ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast] at h
  exact h

lemma moment_pos (n : ℕ) {b : ℝ} (hb : 0 < b) : 0 < moment n b := by
  unfold moment
  positivity

lemma gammaTail_le {T : ℝ} (hT : 0 ≤ T) :
    gammaTail T ≤ moment 5 (1/2) * Real.exp (-(T/2)) := by
  have hi := (moment_integrable 5 (by norm_num : (0:ℝ)<1)).mono_set
    (show Ioi T ⊆ Ioi (0:ℝ) from fun _ hs => hT.trans_lt hs)
  have hj := (moment_integrable 5 (by norm_num : (0:ℝ)<1/2)).mono_set
    (show Ioi T ⊆ Ioi (0:ℝ) from fun _ hs => hT.trans_lt hs)
  calc
    gammaTail T ≤ ∫ s : ℝ in Ioi T, (s^5 * Real.exp (-((1/2)*s))) * Real.exp (-(T/2)) := by
      apply integral_mono_ae (by simpa only [IntegrableOn, mul_comm, one_mul, mul_one] using hi)
        (hj.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have he : Real.exp (-s) ≤ Real.exp (-((1/2)*s)) * Real.exp (-(T/2)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [show T < s from hs])
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right he (pow_nonneg (hT.trans hs.le) 5)
    _ ≤ ∫ s : ℝ in Ioi 0, (s^5 * Real.exp (-((1/2)*s))) * Real.exp (-(T/2)) := by
      apply setIntegral_mono_set ((moment_integrable 5 (by norm_num : (0:ℝ)<1/2)).mul_const _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        positivity
      · exact Filter.Eventually.of_forall (fun _ hs => hT.trans_lt hs)
    _ = moment 5 (1/2) * Real.exp (-(T/2)) := by
      rw [integral_mul_const, moment_integral 5 (by norm_num : (0:ℝ)<1/2)]

lemma exp_neg_le_power {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.exp (-a) ≤ (n.factorial : ℝ) / a^n := by
  apply (le_div_iff₀ (pow_pos ha n)).mpr
  have h := (div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)).mp
    (Real.pow_div_factorial_le_exp a ha.le n)
  calc
    Real.exp (-a) * a^n ≤ Real.exp (-a) * ((n.factorial : ℝ)*Real.exp a) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using h) (Real.exp_pos _).le
    _ = (n.factorial : ℝ) := by rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

lemma gammaTail_small_scale (M : ℕ) {t₀ r : ℝ} (ht₀ : 0 < t₀) (hr : 0 < r) :
    gammaTail (t₀/r^2) ≤
      (moment 5 (1/2) * (M.factorial : ℝ) * (2/t₀)^M) * r^(2*M) := by
  have h := (gammaTail_le (div_nonneg ht₀.le (sq_nonneg r))).trans
    (mul_le_mul_of_nonneg_left
      (exp_neg_le_power (show 0 < t₀/r^2/2 by positivity) M)
      (moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le)
  calc
    _ ≤ moment 5 (1/2) * ((M.factorial : ℝ) / (t₀/r^2/2)^M) := h
    _ = _ := by
      rw [div_pow, div_pow, pow_mul, div_pow]
      field_simp

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricDistance
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma geometric_edist_eq (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x y : X) :
    let := geometricMetricSpace J α hs ht
    edist x y = hermitianEDist J α hs ht x y := rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairingIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
omit [T2Space X] in
lemma hodgeRegularization_symmetric (r : ℝ) (u v : L2 A J α hs ht true) :
    ⟪hodgeRegularization A J α hs ht r u,v⟫ = ⟪u,hodgeRegularization A J α hs ht r v⟫ := by
  have hsym (f g : L2 A J α hs ht true) :
      ⟪hodgeResolvent A J α hs ht r f,g⟫ = ⟪f,hodgeResolvent A J α hs ht r g⟫ :=
    hodgeResolvent_symmetric A J α hs ht r f g
  change ⟪hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r u)),v⟫ =
    ⟪u,hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r v))⟫
  rw [hsym,hsym,hsym]

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

variable [T2Space X]
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma gammaTailKernel_bound (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) :
    |C.gammaTailKernel g T hT r u v| ≤
      (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*
        ‖C.heatEvaluationVector g u‖*‖C.heatEvaluationVector g v‖ := by
  apply (abs_real_inner_le_norm _ _).trans
  have hh := mul_le_mul_of_nonneg_left
    (hodgeGammaShiftLinear_bound A J α hs ht D hD T hT r (2*ρ^2) (C.heatEvaluationVector g v))
    (norm_nonneg (C.heatEvaluationVector g u))
  exact hh.trans_eq (by ring)

lemma gammaTailKernel_uniform (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, ∀ u v : MetricUnit g,
      |C.gammaTailKernel g T hT r u v| ≤ (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*B^2 := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (C.heatEvaluationVector_continuous g).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hb (u : MetricUnit g) : ‖C.heatEvaluationVector g u‖ ≤ M := (hB u (mem_univ _)).trans (le_max_left _ _)
  refine ⟨M,hM,fun r u v => (C.gammaTailKernel_bound g T hT r u v).trans ?_⟩
  have htail : 0 ≤ HodgeKernelBounds.gammaTail (T/r^2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg ((div_nonneg hT (sq_nonneg r)).trans_lt hsp).le _)
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul (hb u) (hb v) (norm_nonneg _) hM)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/120) htail)
  simpa only [sq,mul_assoc] using hh

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma preAntiProjection_smooth (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a) =
      l2AntiProjection A J α hs ht (smoothL2 A J α hs ht true a) :=
  (l2AntiProjection_smooth A J α hs ht a).symm

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] in
lemma hodgeRegularization_l2_represents (Q : L2 A J α hs ht true) {r : ℝ} (hr : 0 < r) :
    hodgeCubeRepresents A J α hs ht r (l2CurrentSource A J α hs ht Q)
      (hodgeRegularization A J α hs ht r Q) := by
  intro a
  rw [hodgeRegularization_symmetric,hodgeRegularization_smoothShift_cube A J α hs ht r hr]
  rfl

omit [T2Space X] in
lemma hodgeRegularization_anti_source (Q : L2 A J α hs ht true)
    (hQ : l2AntiProjection A J α hs ht Q = Q) {r : ℝ} (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    ⟪hodgeRegularization A J α hs ht r Q,
      smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
        (a-preAntiProjection A J α hs ht a))⟫ = 0 := by
  rw [hodgeRegularization_l2_represents A J α hs ht Q hr]
  change ⟪Q,smoothL2 A J α hs ht true (a-preAntiProjection A J α hs ht a)⟫ = 0
  rw [map_sub,inner_sub_right,preAntiProjection_smooth,←l2AntiProjection_self_adjoint,hQ,sub_self]
end TamingCompatibility.GeometricHilbert

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma l2AntiProjection_idempotent (a : L2 A J α hs ht true) :
    l2AntiProjection A J α hs ht (l2AntiProjection A J α hs ht a) =
      l2AntiProjection A J α hs ht a := by
  simp only [l2AntiProjection_apply,map_smul,map_sub,l2JAction_square]
  module

lemma smoothAntiProjection_dense (v : L2 A J α hs ht true)
    (hv : l2AntiProjection A J α hs ht v = v) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : PreL2 A J α hs ht true,
      ‖smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a)-v‖ < ε := by
  obtain ⟨a,ha⟩ := (smoothL2_dense A J α hs ht true).exists_dist_lt v hε
  refine ⟨a,?_⟩
  rw [preAntiProjection_smooth,← hv,← map_sub]
  apply (l2AntiProjection_norm A J α hs ht _).trans_lt
  rw [dist_eq_norm,norm_sub_rev] at ha
  simpa only [hv] using ha

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaTailPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

variable [T2Space X]
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma gammaTailKernel_rapid {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
      |C.gammaTailKernel g T hT.le r u v| ≤ B*r^(2*N) := by
  obtain ⟨M,hM,hb⟩ := C.gammaTailKernel_uniform g T hT.le
  let B := ((1/120 : ℝ)*HodgeKernelBounds.moment 5 (1/2)*(N.factorial : ℝ)*(2/T)^N)*M^2
  have hB : 0 ≤ B := by
    have hm := (HodgeKernelBounds.moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le
    dsimp [B]
    positivity
  refine ⟨B,hB,fun r hr u v => (hb r u v).trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (HodgeKernelBounds.gammaTail_small_scale N hT hr)
      (by norm_num : (0:ℝ)≤1/120)) (sq_nonneg M)
  exact hh.trans_eq (by dsimp [B] <;> ring)

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

include hE D hD in
lemma same_resolvent_current_point_bound :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr),
        ∀ u v : MetricUnit g,
        |S.innerKernel g u v| ≤
          (C/r^4+C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 + B := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,C,hT,hC,_,hbound,hker⟩ :=
    same_resolvent_current_quantitative A J α hs ht E hE D hD g 6
  let ρ := Real.sqrt T/2
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.mpr hT) (by norm_num)
  have hρT : 2*ρ^2 ≤ T := by
    have hsqrt := Real.sq_sqrt hT.le
    dsimp [ρ]
    nlinarith
  let R := hodgeSmoothingCover A J α hs ht D hD ρ hρ
  obtain ⟨B,hB,hBR⟩ := R.gammaTailKernel_rapid g hT 0
  refine ⟨C,B,hC,hB,fun r hr S u v => ?_⟩
  have hb := hbound r hr u v
  have ha : 0 < 1+dist u.val.proj v.val.proj/r := by positivity
  have hw : VolterraBounds.weight 6 (r^2) u.val.proj v.val.proj =
      (1+dist u.val.proj v.val.proj/r)^6 := by
    simp only [VolterraBounds.weight,Real.sqrt_sq_eq_abs,abs_of_pos hr]
  rw [hw] at hb
  have hdiv (x c : ℝ) (h : (1+dist u.val.proj v.val.proj/r)^6 * |x| ≤ c) :
      |x| ≤ c*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 := by
    rw [inv_pow,← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos ha _)).mpr (by simpa only [mul_comm] using h)
  have htbound : |R.gammaTailKernel g T hT.le r u v| ≤ B := by
    simpa using hBR r hr u v
  rw [hker r hr S ρ hρ R hρT u v]
  calc
    _ ≤ |unitCurrentKernel A J α ht E g
          (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| +
        |unitCurrentKernel A J α ht E g
          (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| +
        |R.gammaTailKernel g T hT.le r u v| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C/r^4*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 +
        C/r^2*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 + B :=
      add_le_add (add_le_add (hdiv _ _ hb.1) (hdiv _ _ hb.2)) htbound
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSubprobMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local instance] unitMeasurable unitBorel 

include hE D hD in
lemma same_resolvent_subprob_current_mass_bound :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ], μ.real univ ≤ 1 → ∀ M : ℝ, 0 ≤ M →
      (∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
      ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
        ‖S.regularize g μ‖^2 ≤ (C*M+B)/r^2 := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_current_point_bound A J α hs ht E hE D hD g
  refine ⟨16*C,B,mul_nonneg (by norm_num) hC,hB,?_⟩
  intro μ _ hμ M hM hgrowth r hr hr1 S
  have hb : Continuous (fun v : MetricUnit g => v.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  let P : X → MetricUnit g → ℝ := fun x v => ((1+dist x v.val.proj/r)⁻¹)^6
  have hm (x : X) : Measurable (fun v : MetricUnit g => ENNReal.ofReal (dist x v.val.proj)) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.dist hb)).measurable
  have hp (x : X) : Continuous (P x) := by
    apply Continuous.pow
    apply Continuous.inv₀
    · exact continuous_const.add ((continuous_const.dist hb).div_const r)
    · intro v
      have h : 0 < 1+dist x v.val.proj/r := by positivity
      exact h.ne'
  have hi (x : X) : Integrable (P x) μ :=
    (hp x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint (x : X) : (∫ v, P x v ∂μ) ≤ 8*M*r^2 := by
    have hh := QuadraticShell.integral_profile_normalized_bound μ
      (fun v : MetricUnit g => ENNReal.ofReal (dist x v.val.proj)) (hm x) M hM (hgrowth x) hr
    have he (v : MetricUnit g) :
        (QuadraticShell.profile r (ENNReal.ofReal (dist x v.val.proj))).toReal = P x v := by
      rw [QuadraticShell.profile_ofReal hr dist_nonneg,ENNReal.toReal_ofReal (by positivity)]
    simp_rw [he] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hr)).mp hh
  have hcoef : 0 ≤ C/r^4+C/r^2 := by positivity
  have hinner (u : MetricUnit g) : ‖∫ v, S.innerKernel g u v ∂μ‖ ≤ (16*C*M+B)/r^2 := by
    calc
      _ ≤ ∫ v, |S.innerKernel g u v| ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ v, (C/r^4+C/r^2)*P u.val.proj v+B ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
          (((hi u.val.proj).const_mul _).add (integrable_const _))
          (Eventually.of_forall (hbound r hr S u))
      _ ≤ (C/r^4+C/r^2)*(∫ v, P u.val.proj v ∂μ)+B := by
        rw [integral_add ((hi u.val.proj).const_mul _) (integrable_const _),
          integral_const_mul,integral_const,smul_eq_mul]
        nlinarith [mul_le_mul_of_nonneg_right hμ hB]
      _ ≤ (C/r^4+C/r^2)*(8*M*r^2)+B :=
        add_le_add (mul_le_mul_of_nonneg_left (hint u.val.proj) hcoef) le_rfl
      _ = (8*C*M+8*C*M*r^2+B*r^2)/r^2 := by
        field_simp
      _ ≤ (16*C*M+B)/r^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg r)
        have hr2 : r^2 ≤ 1 := pow_le_one₀ hr.le hr1
        have h1 := mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ 8*C*M)
        have h2 := mul_le_mul_of_nonneg_left hr2 hB
        nlinarith
  have hout := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hinner)
  rw [← S.regularize_inner g μ μ,real_inner_self_eq_norm_sq,
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hout
  exact hout.trans (by nlinarith [mul_le_mul_of_nonneg_left hμ (show 0 ≤ (16*C*M+B)/r^2 by positivity)])

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local instance] unitMeasurable unitBorel 

include hE D hD in
lemma same_resolvent_subprob_current_mass_cross :
    let := geometricMetricSpace J α hs ht
    ∀ (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ], μ.real univ ≤ 1 → ∀ M : ℝ, 0 ≤ M →
      (∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
      ∀ V : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (a-preAntiProjection A J α hs ht a))⟫ = 0) →
        |⟪S.regularize g μ,V⟫| ≤ K*‖V‖ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  intro μ _ hμ M hM hgrowth
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_subprob_current_mass_bound A J α hs ht E hE D hD g
  obtain ⟨L,hL,hcross⟩ := hodge_regularized_positive_current_cross A J α hs ht D hD
  have hCB : 0 ≤ C*M+B := add_nonneg (mul_nonneg hC hM) hB
  refine ⟨L*Real.sqrt (C*M+B),mul_nonneg hL (Real.sqrt_nonneg _),?_⟩
  intro r hr hr1 S V hV
  have hm := hbound μ hμ M hM hgrowth r hr hr1 S
  have hm' : (r*‖S.regularize g μ‖)^2 ≤ C*M+B := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hr)).mp hm
    nlinarith
  have hsqrt : r*‖S.regularize g μ‖ ≤ Real.sqrt (C*M+B) := by
    have hh := Real.sq_sqrt hCB
    have hp := Real.sqrt_nonneg (C*M+B)
    nlinarith [norm_nonneg (S.regularize g μ)]
  calc
    _ ≤ L*r*‖S.regularize g μ‖*‖V‖ := hcross r hr hr1 S g μ V hV
    _ = L*(r*‖S.regularize g μ‖)*‖V‖ := by ring
    _ ≤ (L*Real.sqrt (C*M+B))*‖V‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hL) (norm_nonneg V)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAntiL2Cross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

include hE hD in
lemma subprob_anti_cross_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hμ : μ.real univ ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hgrowth : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | hermitianEDist J α hs ht x v.val.proj < ENNReal.ofReal s} ≤ M*s^2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ V : L2 A J α hs ht true, l2AntiProjection A J α hs ht V = V →
      |⟪hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ r,
        hodgeRegularization A J α hs ht r V⟫| ≤ K*‖V‖ := by
  let := geometricMetricSpace J α hs ht
  have hg : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
    intro x s hs'
    simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth x s hs'
  obtain ⟨K,hK,hbound⟩ := same_resolvent_subprob_current_mass_cross A J α hs ht E hE D hD
    (hermitianMetric J α hs ht) μ hμ M hM hg
  refine ⟨K,hK,fun r hr hr1 V hV => ?_⟩
  simp only [hodgePositiveCurrentFamily,dite_eq_left hr]
  exact (hbound r hr hr1 _ _ (hodgeRegularization_anti_source A J α hs ht V hV hr)).trans
    (mul_le_mul_of_nonneg_left (hodgeRegularization_norm_le A J α hs ht r V) hK)

include hE hD in
lemma subprob_anti_cross_tendsto_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hμ : μ.real univ ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hgrowth : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | hermitianEDist J α hs ht x v.val.proj < ENNReal.ofReal s} ≤ M*s^2)
    (Q : L2 A J α hs ht true) (hQ : l2AntiProjection A J α hs ht Q = Q) :
    Tendsto (fun r : ℝ => ⟪hodgePositiveCurrentFamily A J α hs ht D hD
      (hermitianMetric J α hs ht) μ r,hodgeRegularization A J α hs ht r Q⟫)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ := subprob_anti_cross_bound A J α hs ht E hE D hD μ hμ M hM hgrowth
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := smoothAntiProjection_dense A J α hs ht Q hQ (ε/(2*(K+1))) (by positivity)
  let b := smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a)
  have hb : l2AntiProjection A J α hs ht b = b := by
    dsimp only [b]
    rw [preAntiProjection_smooth,l2AntiProjection_idempotent]
  have hdiff : l2AntiProjection A J α hs ht (Q-b) = Q-b := by rw [map_sub,hQ,hb]
  have hsmall : K*‖Q-b‖ < ε/2 := by
    have hh : ‖Q-b‖ < ε/(2*(K+1)) := by simpa only [b,norm_sub_rev] using ha
    have ht' := (lt_div_iff₀ (show 0 < 2*(K+1) by positivity)).mp hh
    nlinarith [norm_nonneg (Q-b)]
  have hl := hodgePositiveCurrentFamily_anti_cross_tendsto A J α hs ht D hD
    (hermitianMetric J α hs ht) μ a
  have he := (Metric.tendsto_nhds.mp hl) (ε/2) (by positivity)
  have hl1 : ∀ᶠ r in 𝓝[>] (0:ℝ), r < 1 :=
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0) (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin,hl1,he] with r hr hr1 he
  change 0 < r at hr
  let P := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ r
  have hd : |⟪P,hodgeRegularization A J α hs ht r (Q-b)⟫| < ε/2 :=
    (hbound r hr hr1.le (Q-b) hdiff).trans_lt hsmall
  have he' : |⟪P,hodgeRegularization A J α hs ht r b⟫| < ε/2 := by
    simpa only [Real.dist_eq,sub_zero] using he
  have heq : ⟪P,hodgeRegularization A J α hs ht r Q⟫ =
      ⟪P,hodgeRegularization A J α hs ht r (Q-b)⟫+⟪P,hodgeRegularization A J α hs ht r b⟫ := by
    rw [map_sub,inner_sub_right]; ring
  rw [Real.dist_eq,sub_zero]
  change |⟪P,hodgeRegularization A J α hs ht r Q⟫| < ε
  rw [heq]
  exact (abs_add_le _ _).trans_lt (by linarith)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.subprob_anti_cross_tendsto_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.subprob_anti_cross_tendsto_oai.{u_1}
