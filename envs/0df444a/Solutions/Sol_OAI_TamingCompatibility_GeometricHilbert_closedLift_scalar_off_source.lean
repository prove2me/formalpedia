-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:37:26.801313+00:00
-- url     : https://prove2.me/submissions/0568e043-8d34-4d42-b77d-3e22b8f144f5

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc029
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_closedLift_scaled_basis_local_bound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_geometric_center_local_energy_two_jet
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_harmonic_schwartz_seminorm_bound

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiInvariantFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms ExteriorForms
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

section Unitary
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)

include hdim hb h0 h1 h2 h3 in
lemma realPart_antiInvariant : (realPart g b).compContinuousLinearMap J = -realPart g b := by
  apply frame_ext g hdim b hb
  intro i j
  rw [MetricForms.comp_two,ContinuousAlternatingMap.neg_apply]
  fin_cases i <;> fin_cases j <;>
    simp [h0,h1,h2,h3,eval_neg_left,eval_neg_right,realPart_apply,hb]
include hdim hb h0 h1 h2 h3 in
lemma imagPart_antiInvariant : (imagPart g b).compContinuousLinearMap J = -imagPart g b := by
  apply frame_ext g hdim b hb
  intro i j
  rw [MetricForms.comp_two,ContinuousAlternatingMap.neg_apply]
  fin_cases i <;> fin_cases j <;>
    simp [h0,h1,h2,h3,eval_neg_left,eval_neg_right,imagPart_apply,hb]

end Unitary

end TamingCompatibility.AntiInvariantFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalSymbol
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

namespace TamingCompatibility.ManifoldForms
open Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_lift_antiInvariantPart (J : AlmostComplexStructure X) (p : X)
    (β : Space → MetricForms.Form Space 2) {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (hβ : (β z).compContinuousLinearMap (ManifoldHodge.coordinateJ J p z) = -β z) :
    pullback (antiInvariantPart J (chartLift p β)) (extChartAt Model p).symm z = β z := by
  rw [pullback_antiInvariantPart J _ p hz,pullback_chartLift p β hz,hβ]
  module
end TamingCompatibility.ManifoldForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : Data J α ht p)

omit [T2Space X] in
lemma coordinateTest_anti {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain)
    (z : Space) : (coordinateTest J α ht p D q z).compContinuousLinearMap (coordinateJ J p z) =
      -coordinateTest J α ht p D q z := by
  by_cases hz : z ∈ tsupport q
  · obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z (hqD hz)
    have hψ := realPart_antiInvariant (coordinateMetric J α ht p z) (by simp [Space])
      (fun i => D.frame i z) (D.frame_gram z (hqD hz)) (coordinateJ J p z) h0 h1 h2 h3
    have hχ := imagPart_antiInvariant (coordinateMetric J α ht p z) (by simp [Space])
      (fun i => D.frame i z) (D.frame_gram z (hqD hz)) (coordinateJ J p z) h0 h1 h2 h3
    apply ContinuousAlternatingMap.ext
    intro v
    have hψv := congrArg (fun a : MetricForms.Form Space 2 => a v) hψ
    have hχv := congrArg (fun a : MetricForms.Form Space 2 => a v) hχ
    simp only [coordinateTest,frameTest,ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.neg_apply,smul_eq_mul] at hψv hχv ⊢
    rw [hψv,hχv]
    ring
  · have hzq := image_eq_zero_of_notMem_tsupport hz
    have ht : coordinateTest J α ht p D q z = 0 := frameTest_zero hzq
    rw [ht]
    ext v
    simp

omit [T2Space X] in
lemma pullback_manifoldTest {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z = coordinateTest J α ht p D q z :=
  pullback_lift_antiInvariantPart J p _ hz (coordinateTest_anti J α ht p D hqD z)

end TamingCompatibility.GeometricChart

end
end

section
noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma pairLinear_eq_make (p : A.centers) (a : smoothForms X 2) :
    pairLinear A J α ht D hD p a = ScalarPair.make
      (scalarSchwartz A J α ht D hD p a.val a.property 2)
      (scalarSchwartz A J α ht D hD p a.val a.property 3) := rfl
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartTestPairing
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_combination_mixed (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (A B C D : ℝ) :
    pairing g (A • realPart g b + B • imagPart g b) (C • realPart g b + D • imagPart g b) =
      2 * (A*C+B*D) := by
  rw [pairing_two_eq_sum g hdim b hb]
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul,
    realPart_apply,imagPart_apply,hb]
  simp [Fin.sum_univ_succ,FormMetric.pairLeft,FormMetric.pairRight]
  ring
end TamingCompatibility.AntiInvariantFrame

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator ManifoldLocalization ManifoldVolume
open Set _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

lemma pullback_anti {a : TwoForm X} (ha : antiInvariantPart J a = a)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    (pullback a (extChartAt Model p).symm z).compContinuousLinearMap (coordinateJ J p z) =
      -pullback a (extChartAt Model p).symm z := by
  have hj : TamingCompatibility.jAction J a = -a := by
    calc TamingCompatibility.jAction J a = a - (2:ℝ) • antiInvariantPart J a := by
          unfold antiInvariantPart
          module
         _ = -a := by rw [ha]; module
  have hp := pullback_jAction_chart (⟨J.endomorphism,J.square,J.smooth⟩ :
    SmoothAlmostComplex.AlmostComplexStructure X) a p hz
  change pullback (TamingCompatibility.jAction J a) (extChartAt Model p).symm z = _ at hp
  rw [hj] at hp
  exact hp.symm

lemma rawScalar_expansion {a : TwoForm X} (ha : antiInvariantPart J a = a)
    {z : Space} (hz : z ∈ D.domain) :
    pullback a (extChartAt Model p).symm z =
      rawScalar J α ht p D a 2 z • realPart (coordinateMetric J α ht p z) (fun i => D.frame i z) +
      rawScalar J α ht p D a 3 z • imagPart (coordinateMetric J α ht p z) (fun i => D.frame i z) := by
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  exact expansion (coordinateMetric J α ht p z) (by simp [Space]) _ (D.frame_gram z hz)
    (coordinateJ J p z) h0 h1 h2 h3 _ (pullback_anti J p ha (D.domain_subset hz))

lemma pairing_coordinateTest {a : TwoForm X} (ha : antiInvariantPart J a = a)
    {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain) {z : Space}
    (_hz : z ∈ (extChartAt Model p).target) :
    MetricForms.pairing (coordinateMetric J α ht p z) (pullback a (extChartAt Model p).symm z)
      (coordinateTest J α ht p D q z) =
    2 * (rawScalar J α ht p D a 2 z * q z 0 + rawScalar J α ht p D a 3 z * q z 1) := by
  by_cases hzq : z ∈ tsupport q
  · rw [rawScalar_expansion J α ht p D ha (hqD hzq)]
    exact pairing_combination_mixed _ (by simp [Space]) _ (D.frame_gram z (hqD hzq)) _ _ _ _
  · have hq := image_eq_zero_of_notMem_tsupport hzq
    have htest : coordinateTest J α ht p D q z = 0 := frameTest_zero hq
    rw [htest,MetricForms.pairing_zero_right,hq]
    simp

lemma manifoldTest_zero_off (q : Space → EuclideanEnergy.Pair) {x : X}
    (hx : x ∉ (extChartAt Model p).symm '' tsupport q) : manifoldTest J α ht p D q x = 0 := by
  have hn : x ∉ liftSupport p (coordinateTest J α ht p D q) := by
    rintro ⟨z,hz,hzx⟩
    exact hx ⟨z,coordinateTest_support J α ht p D q hz,hzx⟩
  unfold manifoldTest antiInvariantPart
  have hz := chartLift_zero_off p (coordinateTest J α ht p D q) hn
  ext v
  simp only [Pi.smul_apply,Pi.sub_apply,ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sub_apply,TamingCompatibility.jAction]
  rw [hz]
  simp

variable [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (hs : IsSmooth α)
include hs in
lemma pairing_manifoldTest_integral {a : TwoForm X} (ha : IsSmooth a)
    (hanti : antiInvariantPart J a = a) {q : Space → EuclideanEnergy.Pair}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain) :
    (∫ x, GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q) x ∂geometricVolume A J α) =
    ∫ z, chartDensity J α p z *
      (2 * (rawScalar J α ht p D a 2 z * q z 0 + rawScalar J α ht p D a 3 z * q z 1)) := by
  let f := GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q)
  have hfc : Continuous f := (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (manifoldTest_smooth J α hs ht p D hq hc hqD)).continuous
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have hfK : tsupport f ⊆ (extChartAt Model p).symm '' tsupport q := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    apply hx
    change MetricForms.pairing (E := Space) (GeometricAdjoint.pointMetric J α ht x) (a x)
      (manifoldTest J α ht p D q x) = 0
    rw [manifoldTest_zero_off J α ht p D q hn]
    exact MetricForms.pairing_zero_right (E := Space) _ _
  have hfsource : tsupport f ⊆ (extChartAt Model p).source := by
    rintro x hx
    obtain ⟨z,hz,rfl⟩ := hfK hx
    exact (extChartAt Model p).map_target (D.domain_subset (hqD hz))
  change (∫ x, f x ∂geometricVolume A J α) = _
  rw [integral_geometricVolume_coordinate A J α hs ht p f hfc hfsource,
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ (extChartAt Model p).target
  · rw [indicator_of_mem hz]
    change chartDensity J α p z * GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q)
      ((extChartAt Model p).symm z) = _
    rw [← pairing_chart J α ht p (Or.inr rfl) a (manifoldTest J α ht p D q) hz]
    change chartDensity J α p z * MetricForms.pairing (coordinateMetric J α ht p z)
      (TamingCompatibility.pullback a (extChartAt Model p).symm z)
      (TamingCompatibility.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z) = _
    rw [pullback_manifoldTest J α ht p D hqD hz,pairing_coordinateTest J α ht p D hanti hqD hz]
  · rw [indicator_of_notMem hz]
    have hqz : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (D.domain_subset (hqD h)))
    simp only [hqz,PiLp.zero_apply,mul_zero,add_zero]

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_CriticalHolder
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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
namespace TamingCompatibility.CriticalSobolev
open _root_.MeasureTheory
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance instFactLeENNRealOfNatOfRealHDivReal_solutions : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩

lemma schwartz_holder_critical (u φ : 𝓢(E,ℝ)) :
    |∫ x, φ x * u x| ≤ ‖u.toLp 4 (volume : Measure E)‖ *
      ‖φ.toLp (ENNReal.ofReal (4/3:ℝ)) (volume : Measure E)‖ := by
  have hpq : (4:ℝ).HolderConjugate (4/3) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq (u.memLp _ volume) (φ.memLp _ volume)
  rw [SchwartzMap.norm_toLp' (by norm_num : (4:ENNReal) ≠ 0) (by norm_num),
    SchwartzMap.norm_toLp' (by norm_num : ENNReal.ofReal (4/3:ℝ) ≠ 0) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4/3),one_div] at *
  refine le_trans ?_ hh
  have h := norm_integral_le_integral_norm (μ := (volume : Measure E)) (fun x => φ x * u x)
  simpa only [Real.norm_eq_abs,abs_mul,mul_comm] using h

lemma schwartz_multiply_L4 (τ u : 𝓢(E,ℝ)) :
    ‖(SchwartzMap.smulLeftCLM ℝ τ u).toLp 4 (volume : Measure E)‖ ≤
      SchwartzMap.seminorm ℝ 0 0 τ * ‖u.toLp 4 (volume : Measure E)‖ := by
  let T := SchwartzMap.seminorm ℝ 0 0 τ
  have hT : 0 ≤ T := apply_nonneg _ _
  have hb : ∀ᵐ x ∂(volume : Measure E), ‖(SchwartzMap.smulLeftCLM ℝ τ u) x‖ ≤ T * ‖u x‖ := by
    filter_upwards [] with x
    simp only [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,smul_eq_mul]
    change ‖τ x * u x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ τ x) (norm_nonneg _)
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hb 4
  have ht : ENNReal.ofReal T * eLpNorm u 4 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (u.memLp 4 volume).eLpNorm_ne_top
  have h := ENNReal.toReal_mono ht he
  simpa only [SchwartzMap.norm_toLp,ENNReal.toReal_mul,ENNReal.toReal_ofReal hT] using h

local instance instFactLeENNRealOfNat_solutions_r74c801_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
lemma schwartz_cutoff_holder_critical (τ u φ : 𝓢(E,ℝ)) :
    |∫ x, φ x * (τ x * u x)| ≤ SchwartzMap.seminorm ℝ 0 0 τ *
      ‖u.toLp 4 (volume : Measure E)‖ * ‖φ.toLp (ENNReal.ofReal (4/3:ℝ)) volume‖ := by
  simpa only [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,smul_eq_mul] using
    (schwartz_holder_critical (SchwartzMap.smulLeftCLM ℝ τ u) φ).trans
    (mul_le_mul_of_nonneg_right (schwartz_multiply_L4 τ u) (norm_nonneg _))
end TamingCompatibility.CriticalSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_VariationalResolvent
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped RealInnerProductSpace

namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma mem_nullspace_iff (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) :
    f ∈ Fredholm.nullspace (resolvent i D hc) ↔ ∃ u : V, i u = f ∧ D u = 0 := by
  rw [Fredholm.mem_nullspace]
  constructor
  · intro hf
    refine ⟨weakSolution i D hc f, hf, ?_⟩
    have he := weakSolution_identity i D hc f (weakSolution i D hc f)
    change i (weakSolution i D hc f) = f at hf
    rw [hf] at he
    have hz : ⟪D (weakSolution i D hc f), D (weakSolution i D hc f)⟫ = 0 := by linarith
    exact inner_self_eq_zero.mp hz
  · rintro ⟨u, rfl, hu⟩
    have he : weakSolution i D hc (i u) = u := by
      apply hc.continuousLinearEquivOfBilin.injective
      apply ext_inner_right ℝ
      intro v
      rw [hc.continuousLinearEquivOfBilin_apply,
        hc.continuousLinearEquivOfBilin_apply, energy_apply, energy_apply,
        weakSolution_identity, hu, inner_zero_left, add_zero]
    change i (weakSolution i D hc (i u)) = i u
    rw [he]

end TamingCompatibility.Variational

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFredholm
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma mem_harmonicAnti (f : L2 A J α hs ht true) :
    f ∈ harmonicAnti A J α hs ht ↔ ∃ u : antiEnergy A J α hs ht,
      energyInclusion A J α hs ht u = f ∧ weakDelta A J α hs ht u = 0 :=
  Variational.mem_nullspace_iff (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht) f

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.componentTest_apply _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

lemma rawPair_manifoldTest {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ D.domain) :
    rawPair J α ht p D (manifoldTest J α ht p D q) z = q z := by
  have he : TamingCompatibility.pullback (manifoldTest J α ht p D q)
      (extChartAt Model p).symm z = coordinateTest J α ht p D q z :=
    pullback_manifoldTest J α ht p D hqD (D.domain_subset hz)
  unfold rawPair rawScalar
  rw [he]
  ext i
  fin_cases i <;>
    simp [EuclideanEnergy.pair,coordinateTest,frameTest,realPart_apply,imagPart_apply,
      D.frame_gram z hz]

end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [CompactSpace X] in
lemma scalar_eq_weight (p : A.centers) (a : TwoForm X) (j : Fin 4)
    {z : Space} (hz : z ∈ (D p).domain) :
    scalar A J α ht D p a j z = coordinateWeight A p z * rawScalar J α ht p.val (D p) a j z := by
  unfold scalar localizedFunction
  rw [indicator_of_mem hz,indicator_of_mem ((D p).domain_subset hz)]
  rfl

lemma realPairSchwartz_apply (p : A.centers) (a : smoothForms X 2) (z : Space) :
    realPairSchwartz A J α ht D hD p a z =
      EuclideanEnergy.pair (scalar A J α ht D p a.val 2 z) (scalar A J α ht D p a.val 3 z) := by
  ext i
  fin_cases i <;> simp [realPairSchwartz,pairLinear_eq_make,ScalarPair.make_apply,EuclideanEnergy.pair] <;> rfl

lemma realPairSchwartz_embed (p : A.centers) (a : smoothForms X 2) :
    SchwartzMap.postcompCLM (embed 2) (realPairSchwartz A J α ht D hD p a) =
      pairLinear A J α ht D hD p a := by
  ext z i
  fin_cases i <;> simp [realPairSchwartz_apply,pairLinear_eq_make,ScalarPair.make_apply,EuclideanEnergy.pair] <;> rfl

lemma realPairSchwartz_raw (p : A.centers) (a : smoothForms X 2)
    {z : Space} (hz : z ∈ (D p).domain) :
    realPairSchwartz A J α ht D hD p a z =
      coordinateWeight A p z • rawPair J α ht p.val (D p) a.val z := by
  rw [realPairSchwartz_apply,scalar_eq_weight A J α ht D p a.val 2 hz,
    scalar_eq_weight A J α ht D p a.val 3 hz]
  ext i
  fin_cases i <;> rfl

lemma cutoff_realPair_raw (p : A.centers) (a : smoothForms X 2) (τ : 𝓢(Space,ℝ))
    {z : Space} (hz : z ∈ (D p).domain) (hτ : τ z * coordinateWeight A p z = 1) :
    SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a) z =
      rawPair J α ht p.val (D p) a.val z := by
  rw [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth]
  rw [realPairSchwartz_raw A J α ht D hD p a hz,smul_smul,hτ,one_smul]
end TamingCompatibility.GeometricChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart _root_.MeasureTheory ComplexMatrix
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma scalarDistribution_smooth (p : A.centers) (a : antiPre A J α hs ht) :
    scalarDistribution A J α hs ht D hD p (antiToEnergy A J α hs ht a) =
      (pairLinear A J α ht D hD p a.val : 𝓢'(Space,ScalarPair.F)) := by
  change ScalarPair.jetDistribution none
    (energyToScalarJet A J α hs ht D hD p (antiToEnergy A J α hs ht a)) = _
  rw [energyToScalarJet_smooth]
  exact ScalarPair.jetDistribution_jet _ none

lemma rawDistribution_smooth (p : A.centers) (τ : 𝓢(Space,ℝ)) (a : antiPre A J α hs ht) :
    rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht a) =
      (SchwartzMap.postcompCLM (embed 2)
        (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a.val)) :
          𝓢'(Space,ScalarPair.F)) := by
  change smulLeftCLM ScalarPair.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
    (scalarDistribution A J α hs ht D hD p (antiToEnergy A J α hs ht a)) = _
  rw [scalarDistribution_smooth,product_schwartz]
  congr 1
  rw [← realPairSchwartz_embed A J α ht D hD p a.val]
  ext z i
  simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM τ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply τ.hasTemperateGrowth,SchwartzMap.postcompCLM_apply,embed_apply,
    PiLp.smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_WeakNormal
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma smooth_energy_pair (f v : antiPre A J α hs ht) :
    ⟪smoothL2 A J α hs ht true f.val,
      energyInclusion A J α hs ht (antiToEnergy A J α hs ht v)⟫ =
    ∫ x, GeometricAdjoint.pairing J α ht f.val.val v.val.val x ∂geometricVolume A J α := by
  change ⟪smoothL2 A J α hs ht true f.val,smoothL2 A J α hs ht true v.val⟫ = _
  rw [(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  rfl

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_WeightedRawPairing
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma densityTest_apply (p : A.centers) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain) (z : Space) :
    densityTest A J α hs ht D p φ hc hφD z = φ z * (2*chartDensity J α p.val z) := rfl

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma densityTest_support (p : A.centers) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain) :
    tsupport (densityTest A J α hs ht D p φ hc hφD) ⊆ tsupport φ :=
  tsupport_smul_subset_left _ _

lemma smooth_raw_component_pair (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) (w : antiPre A J α hs ht) :
    (rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht w)
      (SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD)))) j =
    (⟪energyInclusion A J α hs ht (antiToEnergy A J α hs ht w),energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  rw [rawDistribution_smooth,embedded_component_apply]
  change _ = (⟪smoothL2 A J α hs ht true w.val,energyInclusion A J α hs ht
    (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
      (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ)
  rw [smooth_energy_pair]
  congr 1
  change _ = ∫ x, GeometricAdjoint.pairing J α ht w.val.val
    (manifoldTest J α ht p.val (D p) (componentTest j φ)) x ∂geometricVolume A J α
  rw [pairing_manifoldTest_integral J α ht p.val (D p) A hs w.val.property w.property
    ((componentTest j φ).smooth ⊤) (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [componentTest_inner,densityTest_apply]
  by_cases hz : z ∈ tsupport φ
  · rw [cutoff_realPair_raw A J α ht D hD p w.val τ (hUD (hφU hz)) (hτ z (hφU hz))]
    fin_cases j <;> simp [rawPair,EuclideanEnergy.pair,componentTest_apply] <;> ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp [componentTest_apply,image_eq_zero_of_notMem_tsupport hz]

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalRescaleH1
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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

namespace TamingCompatibility.ScalarPair
open _root_.MeasureTheory ManifoldLocalization LineDeriv
open scoped SchwartzMap ENNReal NNReal LineDeriv

lemma critical_sobolev_jet : ∃ C : ℝ, 0 ≤ C ∧
    ∀ u : 𝓢(Space,F), HasCompactSupport u →
      ‖u.toLp 4 (volume : Measure Space)‖ ≤ C * ‖jet u‖ := by
  let c := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2
  refine ⟨(c:ℝ)*4,by positivity,fun u hu => ?_⟩
  let du (i : Fin (Module.finrank ℝ Space)) :=
    lineDerivOpCLM ℝ 𝓢(Space,F) (stdOrthonormalBasis ℝ Space i) u
  have hd : eLpNorm (fderiv ℝ u) 2 (volume : Measure Space) ≤
      ∑ i, eLpNorm (du i) 2 volume := by
    calc
      eLpNorm (fderiv ℝ u) 2 volume ≤
          eLpNorm (fun x => ∑ i, ‖du i x‖) 2 volume := by
        apply eLpNorm_mono_ae_real
        exact Filter.Eventually.of_forall (fun x => by
          simpa only [du,LineDeriv.lineDerivOpCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv] using
            CriticalSobolev.opNorm_le_sum_basis (fderiv ℝ u x))
      _ ≤ ∑ i, eLpNorm (fun x => ‖du i x‖) 2 volume := by
        simpa only [Finset.sum_fn] using eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (μ := (volume : Measure Space))
          (f := fun index x => ‖du index x‖)
          (by norm_num : (1:ℝ≥0∞) ≤ 2)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index _
        exact eLpNorm_norm _
  have hj (i : Fin (Module.finrank ℝ Space)) :
      eLpNorm (du i) 2 volume ≤ ENNReal.ofReal ‖jet u‖ := by
    have hi : ‖(du i).toLp 2 (volume : Measure Space)‖ ≤ ‖jet u‖ := by
      exact PiLp.norm_apply_le (jet u) (some i)
    rw [SchwartzMap.norm_toLp] at hi
    rw [← ENNReal.ofReal_toReal ((du i).memLp 2 volume).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hi
  have hsum : (∑ i, eLpNorm (du i) 2 volume) ≤ 4 * ENNReal.ofReal ‖jet u‖ := by
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ Space), ENNReal.ofReal ‖jet u‖ :=
        Finset.sum_le_sum (fun i _ => hj i)
      _ = _ := by simp [Space]
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Space)
    (u.smooth 1) hu
    (p := (2:ℝ≥0)) (p' := (4:ℝ≥0)) (by norm_num)
    (by simp [Space]) (by norm_num [Space])
  have hb : eLpNorm u 4 volume ≤ (c:ℝ≥0∞) * (4 * ENNReal.ofReal ‖jet u‖) :=
    hgns.trans (mul_le_mul_of_nonneg_left (hd.trans hsum) (zero_le))
  have hr := ENNReal.toReal_mono (by finiteness) hb
  simpa only [SchwartzMap.norm_toLp,ENNReal.toReal_mul,ENNReal.coe_toReal,
    ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (norm_nonneg _),mul_assoc] using hr
end TamingCompatibility.ScalarPair

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalManifoldSobolev
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff SchwartzMap ENNReal
local instance instFactLeENNRealOfNat_solutions_r74c801_2 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [MeasurableSpace X] [BorelSpace X] in
lemma pairLinear_compact (p : A.centers) (a : smoothForms X 2) :
    HasCompactSupport (pairLinear A J α ht D hD p a : Space → ScalarPair.F) := by
  have h₀ := ((scalar_smooth_compact A J α ht D hD p a.val a.property 2).2).comp_left
    (map_zero (ScalarPair.inject 0))
  have h₁ := ((scalar_smooth_compact A J α ht D hD p a.val a.property 3).2).comp_left
    (map_zero (ScalarPair.inject 1))
  exact h₀.add h₁

lemma pair_energy_L4_bound (p : A.centers) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : antiPre A J α hs ht,
      ‖(pairLinear A J α ht D hD p a.val).toLp 4 (volume : Measure Space)‖ ≤
        C * ‖antiToEnergy A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := ScalarPair.critical_sobolev_jet
  let T := energyToScalarJet A J α hs ht D hD p
  refine ⟨C*‖T‖,mul_nonneg hC (norm_nonneg T),fun a => ?_⟩
  have hj : ScalarPair.jet (pairLinear A J α ht D hD p a.val) = T (antiToEnergy A J α hs ht a) :=
    (energyToScalarJet_smooth A J α hs ht D hD p a).symm
  calc
    _ ≤ C * ‖ScalarPair.jet (pairLinear A J α ht D hD p a.val)‖ :=
      hb _ (pairLinear_compact A J α ht D hD p a.val)
    _ ≤ C * (‖T‖ * ‖antiToEnergy A J α hs ht a‖) := by
      rw [hj]
      exact mul_le_mul_of_nonneg_left (T.le_opNorm _) hC
    _ = _ := by ring

lemma component_energy_L4_bound (p : A.centers) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : antiPre A J α hs ht, ∀ j : Fin 2,
      ‖(realComponent (realPairSchwartz A J α ht D hD p a.val) j).toLp 4 (volume : Measure Space)‖ ≤
        C * ‖antiToEnergy A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := pair_energy_L4_bound A J α hs ht D hD p
  refine ⟨C,hC,fun a j => ?_⟩
  apply le_trans _ (hb a)
  rw [SchwartzMap.norm_toLp,SchwartzMap.norm_toLp]
  apply ENNReal.toReal_mono ((pairLinear A J α ht D hD p a.val).memLp 4 volume).eLpNorm_ne_top
  apply eLpNorm_mono
  intro x
  change |((pairLinear A J α ht D hD p a.val) x j).re| ≤
    ‖(pairLinear A J α ht D hD p a.val) x‖
  exact (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le _ _)

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_CriticalChartPairing
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume ComplexMatrix
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
local instance instFactLeENNRealOfNatOfRealHDivReal_solutions : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩

local instance localInst_r74c801_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
include hD in
lemma critical_chart_pairing (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space,ℝ))
      (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
      (j : Fin 2) (u : antiEnergy A J α hs ht),
      |⟪energyInclusion A J α hs ht
          (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
            (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD)))),
        energyInclusion A J α hs ht u⟫| ≤
      C * ‖(densityTest A J α hs ht D p φ hc (hφU.trans hUD)).toLp
        (ENNReal.ofReal (4/3:ℝ)) (volume : Measure Space)‖ * ‖u‖ := by
  obtain ⟨C,hC,hbound⟩ := component_energy_L4_bound A J α hs ht D hD p
  let T := SchwartzMap.seminorm ℝ 0 0 τ
  have hT : 0 ≤ T := apply_nonneg _ _
  refine ⟨T*C,mul_nonneg hT hC,fun φ hc hφU j u => ?_⟩
  let ψ := densityTest A J α hs ht D p φ hc (hφU.trans hUD)
  let v := antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD)))
  change |⟪energyInclusion A J α hs ht v,energyInclusion A J α hs ht u⟫| ≤
    (T*C) * ‖ψ.toLp (ENNReal.ofReal (4/3:ℝ)) volume‖ * ‖u‖
  refine (antiToEnergy_dense A J α hs ht).induction_on u ?_ ?_
  · exact isClosed_le ((continuous_const.inner (energyInclusion A J α hs ht).continuous).abs)
      (continuous_const.mul continuous_norm)
  intro a
  have heq := smooth_raw_component_pair A J α hs ht D hD p τ hUD hτ φ hc hφU j a
  rw [rawDistribution_smooth,embedded_component_apply] at heq
  have heqr := Complex.ofReal_injective heq
  rw [real_inner_comm,← heqr]
  have hh := CriticalSobolev.schwartz_cutoff_holder_critical τ
    (realComponent (realPairSchwartz A J α ht D hD p a.val) j) ψ
  have hh' : |∫ x, ⟪(SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ
      (realPairSchwartz A J α ht D hD p a.val)) x,componentTest j ψ x⟫| ≤
      T * ‖(realComponent (realPairSchwartz A J α ht D hD p a.val) j).toLp 4 volume‖ *
        ‖ψ.toLp (ENNReal.ofReal (4/3:ℝ)) volume‖ := by
    simpa only [componentTest_inner,SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,
      PiLp.smul_apply,smul_eq_mul,realComponent_apply] using hh
  refine hh'.trans ?_
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hbound a j) hT)
    (norm_nonneg (ψ.toLp (ENNReal.ofReal (4/3:ℝ)) volume))
  nlinarith only [hb]
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_CriticalInverse
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
namespace TamingCompatibility.CriticalSobolev
open _root_.MeasureTheory
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma schwartz_LfourThirds_support_scale (hdim : Module.finrank ℝ E = 4)
    (φ : 𝓢(E,ℝ)) (p : E) {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hs : tsupport φ ⊆ Metric.ball p r) (hb : ∀ x, |φ x| ≤ M) :
    ‖φ.toLp (ENNReal.ofReal (4/3:ℝ)) (volume : Measure E)‖ ≤
      M * ((Real.pi^2/2) ^ (3/4:ℝ)) * r^3 := by
  have he : eLpNorm φ (ENNReal.ofReal (4/3:ℝ)) volume ≤
      ENNReal.ofReal M * volume (Metric.ball p r) ^ (3/4:ℝ) := by
    have h := eLpNorm_sub_le_of_dist_bdd (volume : Measure E)
      (p := ENNReal.ofReal (4/3:ℝ)) (by norm_num) measurableSet_ball hM
      (f := (φ : E → ℝ)) (g := 0)
      (fun x => by simpa [Real.dist_eq] using hb x)
      ((subset_tsupport _).trans hs) (by simp)
    norm_num at h ⊢
    exact h
  have hvol : volume (Metric.ball p r) = ENNReal.ofReal r ^ 4 *
      ENNReal.ofReal (Real.pi^2/2) := by
    have h := InnerProductSpace.volume_ball_of_dim_even (E := E) (k := 2)
      (by omega : Module.finrank ℝ E = 2*2) p r
    simpa [hdim,Nat.factorial] using h
  have hfin : ENNReal.ofReal M * volume (Metric.ball p r) ^ (3/4:ℝ) ≠ ⊤ := by
    rw [hvol]
    finiteness
  have h := ENNReal.toReal_mono hfin he
  rw [SchwartzMap.norm_toLp]
  apply h.trans_eq
  rw [hvol,ENNReal.toReal_mul,← ENNReal.toReal_rpow,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hr,ENNReal.toReal_ofReal hM,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi^2/2),
    Real.mul_rpow (by positivity) (by positivity)]
  have hp : (r^4) ^ (3/4:ℝ) = r^3 := by
    rw [← Real.rpow_natCast r 4,← Real.rpow_mul hr]
    norm_num
  rw [hp]
  ring
end TamingCompatibility.CriticalSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume ComplexMatrix
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

local instance instFactLeENNRealOfNatOfRealHDivReal_solutions_2_r74c801_1 : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma densityTest_scale_bound (p : A.centers) {V : Set Space}
    (hV : IsCompact V) (hVD : V ⊆ (D p).domain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
      (hφV : tsupport φ ⊆ V) (q : Space) (r M : ℝ), 0 ≤ r → 0 ≤ M →
      tsupport φ ⊆ Metric.ball q r → (∀ x, |φ x| ≤ M) →
      ‖(densityTest A J α hs ht D p φ hc (hφV.trans hVD)).toLp
        (ENNReal.ofReal (4/3:ℝ)) (volume : Measure Space)‖ ≤ C*M*r^3 := by
  obtain ⟨K,hK⟩ := hV.exists_bound_of_continuousOn
    (((chartDensity_smooth J α hs ht p.val).continuousOn.mono
      (hVD.trans (D p).domain_subset)).const_mul 2)
  let K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  refine ⟨K'*(Real.pi^2/2)^(3/4:ℝ),by positivity,fun φ hc hφV q r M hr hM hball hb => ?_⟩
  have hψ : ∀ x, |densityTest A J α hs ht D p φ hc (hφV.trans hVD) x| ≤ M*K' := by
    intro x
    rw [densityTest_apply,abs_mul]
    by_cases hx : x ∈ tsupport φ
    · apply mul_le_mul (hb x) _ (abs_nonneg _) hM
      exact (show |2*chartDensity J α p.val x| ≤ K from hK x (hφV hx)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx,abs_zero,zero_mul]
      exact mul_nonneg hM hK'
  have h := CriticalSobolev.schwartz_LfourThirds_support_scale
    (E := Space) (by simp [Space]) (densityTest A J α hs ht D p φ hc (hφV.trans hVD)) q
    hr (mul_nonneg hM hK')
    ((densityTest_support A J α hs ht D p φ hc (hφV.trans hVD)).trans hball) hψ
  convert h using 1 <;> first | rfl | ring

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_ScaledDual
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume ComplexMatrix
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma geometric_scaled_source_dual (p : A.centers) (τ : 𝓢(Space,ℝ)) {V : Set Space}
    (hV : IsCompact V) (hVD : V ⊆ (D p).domain)
    (hτ : ∀ z ∈ V, τ z * coordinateWeight A p z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space,ℝ))
      (hc : HasCompactSupport (φ : Space → ℝ)) (hφV : tsupport φ ⊆ V)
      (j : Fin 2) (q : Space) (r M : ℝ), 0 ≤ r → 0 ≤ M →
      tsupport φ ⊆ Metric.ball q r → (∀ x, |φ x| ≤ M) →
      ∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true
          (testAnti A J α hs ht D p (componentTest j φ)
            (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφV.trans hVD))).val,
          energyInclusion A J α hs ht v⟫| ≤ (C*M*r^3)*‖v‖ := by
  obtain ⟨B,hB,hpair⟩ := critical_chart_pairing A J α hs ht D hD p τ hVD hτ
  obtain ⟨K,hK,hscale⟩ := densityTest_scale_bound A J α hs ht D p hV hVD
  refine ⟨B*K,mul_nonneg hB hK,fun φ hc hφV j q r M hr hM hball hb v => ?_⟩
  apply (hpair φ hc hφV j v).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hscale φ hc hφV q r M hr hM hball hb) hB) (norm_nonneg v)
  simpa only [mul_assoc] using h

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalDDStarEstimate
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma weightedRawRHS_spec (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (f : antiPre A J α hs ht) {z : Space} (hz : z ∈ (D p).domain)
    (hτ : τ z * coordinateWeight A p z = 1) (hρ : ρ z = chartDensity J α p.val z) :
    weightedRawRHS A J α hs ht D hD p τ ρ f z =
      (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z := by
  simp only [weightedRawRHS,smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth,
    cutoff_realPair_raw A J α ht D hD p f.val τ hz hτ,hρ,smul_smul]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ShrinkingCutoff
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
namespace TamingCompatibility.EuclideanSobolevOperators
open Set Filter
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normalizedCutoff_apply (L : E ≃L[ℝ] E) (q y : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) : normalizedCutoff L q r hr χ y = χ (r⁻¹ • L y - r⁻¹ • L q) := by
  rw [normalizedCutoff,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    affineSchwartz_apply,sub_eq_add_neg]

lemma normalizedCutoff_support (L : E ≃L[ℝ] E) (q : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) : tsupport (normalizedCutoff L q r hr χ) ⊆
      (fun y => r⁻¹ • L y - r⁻¹ • L q) ⁻¹' tsupport χ := by
  apply closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
  intro y hy
  apply subset_tsupport χ
  simpa only [Function.mem_support,normalizedCutoff_apply] using hy

lemma normalizedCutoff_eventually_support (L : E ≃L[ℝ] E) (q₀ : E)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    {W : Set E} (hW : IsOpen W) (hq : q₀ ∈ W) :
    ∀ᶠ t : ℝ × E in 𝓝 (0,q₀), ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr χ) ⊆ W := by
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hW q₀ hq
  obtain ⟨R,hR⟩ := hχ.exists_bound_of_continuousOn (f := fun x : E => x) continuous_id.continuousOn
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  have hc : Continuous (fun t : ℝ × E => ‖t.2-q₀‖+|t.1| *‖(L.symm : E →L[ℝ] E)‖*B) := by fun_prop
  have ht : ∀ᶠ t : ℝ × E in 𝓝 (0,q₀), ‖t.2-q₀‖+|t.1| *‖(L.symm : E →L[ℝ] E)‖*B < δ :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa using hδ)
  filter_upwards [ht] with t ht
  intro hr y hy
  let z := t.1⁻¹ • L y - t.1⁻¹ • L t.2
  have hz : z ∈ tsupport χ := normalizedCutoff_support L t.2 t.1 hr χ hy
  have hze : ‖z‖ ≤ B := (hR z hz).trans (le_max_left _ _)
  have he : y-t.2 = t.1 • L.symm z := by
    apply L.injective
    simp only [map_sub,map_smul,ContinuousLinearEquiv.apply_symm_apply,z,
      smul_sub,smul_smul,mul_inv_cancel₀ hr,one_smul]
  have hnorm : ‖y-t.2‖ ≤ |t.1| *‖(L.symm : E →L[ℝ] E)‖*B := by
    rw [he,norm_smul,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left ((L.symm : E →L[ℝ] E).le_opNorm z) (abs_nonneg _)).trans
    calc
      _ ≤ |t.1| *(‖(L.symm : E →L[ℝ] E)‖*B) := by gcongr
      _ = _ := by ring
  apply hball
  rw [Metric.mem_ball,dist_eq_norm]
  calc
    ‖y-q₀‖ = ‖(y-t.2)+(t.2-q₀)‖ := by congr 1; abel
    _ ≤ ‖y-t.2‖+‖t.2-q₀‖ := norm_add_le _ _
    _ ≤ |t.1| *‖(L.symm : E →L[ℝ] E)‖*B+‖t.2-q₀‖ := add_le_add hnorm le_rfl
    _ < δ := by linarith
end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialCutoffGeometry
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Set Filter ComplexMatrix EuclideanSobolevOperators
open scoped ContDiff Topology SchwartzMap

namespace GeometricHilbert

lemma normalizedCutoff_bounded_radius (L : Space ≃L[ℝ] Space)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : Space, ∀ r : ℝ, ∀ hr : 0 < r,
      tsupport (normalizedCutoff L q r hr.ne' χ) ⊆ Metric.closedBall q (c*r) := by
  obtain ⟨R,hR⟩ := hc.exists_bound_of_continuousOn (f := fun x : Space => x) continuous_id.continuousOn
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨‖L.symm.toContinuousLinearMap‖*B+1,by positivity,?_⟩
  intro q r hr y hy
  let z := r⁻¹ • L y-r⁻¹ • L q
  have hz : z ∈ tsupport χ := normalizedCutoff_support L q r hr.ne' χ hy
  have hze : ‖z‖ ≤ B := (hR z hz).trans (le_max_left _ _)
  have he : y-q = r • L.symm z := by
    apply L.injective
    simp only [map_sub,map_smul,ContinuousLinearEquiv.apply_symm_apply,z,
      smul_sub,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [Metric.mem_closedBall,dist_eq_norm,he,norm_smul,Real.norm_of_nonneg hr.le]
  calc
    _ ≤ r*(‖L.symm.toContinuousLinearMap‖*‖z‖) :=
      mul_le_mul_of_nonneg_left (L.symm.toContinuousLinearMap.le_opNorm z) hr.le
    _ ≤ r*(‖L.symm.toContinuousLinearMap‖*B) := by gcongr
    _ ≤ _ := by nlinarith

lemma normalizedCutoffs_bounded_radius (L : Space ≃L[ℝ] Space)
    (χ : ℕ → 𝓢(Space,ℂ)) (hc : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n ≤ 3, ∀ q : Space, ∀ r : ℝ, ∀ hr : 0 < r,
      tsupport (normalizedCutoff L q r hr.ne' (χ (n+1))) ⊆ Metric.closedBall q (c*r) := by
  classical
  choose c hcpos hcs using fun n : Fin 4 => normalizedCutoff_bounded_radius L (χ (n.val+1)) (hc n.val (by omega))
  have hn : 0 ≤ ∑ n : Fin 4, c n := Finset.sum_nonneg (fun n _ => (hcpos n).le)
  refine ⟨1+∑ n : Fin 4, c n,by linarith,?_⟩
  intro n hn q r hr
  apply (hcs ⟨n,by omega⟩ q r hr).trans
  apply Metric.closedBall_subset_closedBall
  apply mul_le_mul_of_nonneg_right _ hr.le
  exact (Finset.single_le_sum (fun i _ => (hcpos i).le) (Finset.mem_univ _)).trans
    (le_add_of_nonneg_left (by norm_num))

lemma closedBall_ball_disjoint_of_radii {b y : Space} {R r : ℝ}
    (hsep : R+r ≤ dist b y) : Disjoint (Metric.closedBall y r) (Metric.ball b R) := by
  rw [Set.disjoint_left]
  intro z hz hzb
  have hzy : dist z y ≤ r := hz
  have hzb' : dist b z < R := by simpa only [dist_comm,Metric.mem_ball] using hzb
  have htri := dist_triangle b z y
  linarith
end GeometricHilbert
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawPairLinear
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma rawPair_sub (a b : TwoForm X) (z : Space) :
    rawPair J α ht p D (a-b) z = rawPair J α ht p D a z - rawPair J α ht p D b z := by
  ext i
  fin_cases i <;> rfl
end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HarmonicSeminormBound
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

include hD in
lemma harmonic_schwartz_derivative_bound
    (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ n ≤ N, ∀ v : Fin n → E, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (F₀ h)) x‖ ≤ C * ‖smoothL2 A J α hs ht true f.val‖ := by
  classical
  choose C hC hb using fun n => harmonic_schwartz_seminorm_bound A J α hs ht D hD F₀ 0 n
  refine ⟨∑ n ∈ Finset.range (N+1), C n,Finset.sum_nonneg (fun n _ => hC n),fun f h hh n hn v hv x => ?_⟩
  have hN : C n ≤ ∑ n ∈ Finset.range (N+1), C n :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (by omega))
  have hd : ‖(∂^{v} (F₀ h)) x‖ ≤ SchwartzMap.seminorm ℝ 0 n (F₀ h) := by
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    calc
      _ ≤ ‖iteratedFDeriv ℝ n (F₀ h) x‖ * ∏ i, ‖v i‖ := (iteratedFDeriv ℝ n (F₀ h) x).le_opNorm v
      _ ≤ ‖iteratedFDeriv ℝ n (F₀ h) x‖ * 1 := by
        apply mul_le_mul_of_nonneg_left (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hv i)) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ n (F₀ h) x‖ := mul_one _
      _ ≤ _ := (F₀ h).norm_iteratedFDeriv_le_seminorm ℝ n x
  exact hd.trans ((hb n f h hh).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg _)))
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HarmonicDualBound
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] in

lemma harmonicAnti_dual_bound (f : L2 A J α hs ht true) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ v : antiEnergy A J α hs ht,
      |⟪f,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) :
    ‖(harmonicAnti A J α hs ht).starProjection f‖ ≤ M := by
  let K := harmonicAnti A J α hs ht
  obtain ⟨v,hv,hd⟩ := (mem_harmonicAnti A J α hs ht (K.starProjection f)).mp
    (K.starProjection_apply_mem f)
  have hn : ‖v‖ = ‖K.starProjection f‖ := by
    have hg := WithLp.prod_norm_sq_eq_of_L2 v.val
    change ‖v‖^2 = ‖energyInclusion A J α hs ht v‖^2 + ‖weakDelta A J α hs ht v‖^2 at hg
    rw [hv,hd,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero] at hg
    nlinarith [norm_nonneg v,norm_nonneg (K.starProjection f)]
  have hp : K.starProjection (K.starProjection f) = K.starProjection f :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem f)
  have hi : ⟪f,K.starProjection f⟫ = ‖K.starProjection f‖^2 := by
    have h := K.inner_starProjection_left_eq_right f (K.starProjection f)
    rw [hp,real_inner_self_eq_norm_sq] at h
    exact h.symm
  have h := hb v
  rw [hv,hn,hi,abs_of_nonneg (sq_nonneg _)] at h
  change ‖K.starProjection f‖ ≤ M
  by_cases hz : ‖K.starProjection f‖ = 0
  · rw [hz]; exact hM
  · have hp : 0 < ‖K.starProjection f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

variable (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

include hD in

lemma harmonic_schwartz_dual_derivative_bound
    (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      ∀ n ≤ N, ∀ v : Fin n → E, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (F₀ h)) x‖ ≤ C*M := by
  obtain ⟨C,hC,hbound⟩ := harmonic_schwartz_derivative_bound A J α hs ht D hD F₀ N
  refine ⟨C,hC,fun f h hh M hM hb n hn v hv x => ?_⟩
  have hself : smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
      (smoothL2 A J α hs ht true h.val) := by
    rw [hh,(harmonicAnti A J α hs ht).starProjection_eq_self_iff.mpr
      ((harmonicAnti A J α hs ht).starProjection_apply_mem _)]
  have hp := harmonicAnti_dual_bound A J α hs ht _ M hM hb
  rw [← hh] at hp
  exact (hbound h h hself n hn v hv x).trans (mul_le_mul_of_nonneg_left hp hC)
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_NormalizedHarmonicRHS
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma normalizedRawRHSMap_apply (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (L : Space ≃L[ℝ] Space)
    (f : antiPre A J α hs ht) :
    normalizedRawRHSMap A J α hs ht D hD p τ ρ L f =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ f)) := rfl

include hD in

lemma normalized_harmonic_rhs_bound (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (L : Space ≃L[ℝ] Space) (N : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      ∀ n ≤ N, ∀ v : Fin n → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ h)))) x‖ ≤ C₀*M := by
  obtain ⟨C₀,hC,hb⟩ := harmonic_schwartz_dual_derivative_bound A J α hs ht D hD
    (normalizedRawRHSMap A J α hs ht D hD p τ ρ L) N
  exact ⟨C₀,hC,by simpa only [normalizedRawRHSMap_apply] using hb⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HarmonicOffJet
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

theorem geometric_off_source_two_jet (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (hr : 0 < t.1),
      t.1 ≤ 1 → ∀ (f h a : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      (∃ O : Set Space, IsOpen O ∧ O ⊆ W ∧
        (∀ n ≤ 3, tsupport (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1))) ⊆ O) ∧
        ∀ z ∈ O, rawPair J α ht p.val (D p) f.val.val z = 0) →
      (∀ v : antiEnergy A J α hs ht,
        ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true (f-h).val,energyInclusion A J α hs ht v⟫) →
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (localizedRawSchwartz A J α hs ht D hD p τ η a)
      ∀ x : Space, ((χ 4 : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖u (t.1 • x+L t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u) (t.1 • x+L t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ Space j} (∂_{stdOrthonormalBasis ℝ Space i} u)) (t.1 • x+L t.2)‖ ≤
        C₀*(M*t.1^3 + ‖antiToEnergy A J α hs ht a‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_center_local_energy_two_jet A J α hs ht D hD p τ hU hUD hτ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨K,hK,harm⟩ := normalized_harmonic_rhs_bound A J α hs ht D hD p τ ρ L 3
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C*(K+1),by positivity,?_⟩
  filter_upwards [hest] with t hh
  intro hr hr1 f h a M hM hproj hdual hzero heq
  obtain ⟨O,hO,hOW,hχO,hfO⟩ := hzero
  let g := -weightedRawRHS A J α hs ht D hD p τ ρ h
  have hg : ∀ z ∈ O, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) (f-h).val.val z := by
    intro z hz
    change -(weightedRawRHS A J α hs ht D hD p τ ρ h z) = _
    rw [weightedRawRHS_spec A J α hs ht D hD p τ ρ h (hUD (hWU (hOW hz)))
      (hτ z (hWU (hOW hz))) (hρ z (hWU (hOW hz)))]
    change _ = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) (f.val.val-h.val.val) z
    rw [rawPair_sub,hfO z hz,zero_sub,smul_neg]
  have hd : ∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
      ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) g))) x‖ ≤ (K*M)/t.1^k := by
    intro k hk v hv x
    have hb := harm f h hproj M hM hdual k hk v hv x
    have he : ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) g))) x‖ =
      ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ h)))) x‖ := by
      simp only [g,map_neg,LineDeriv.iteratedLineDerivOp_neg,neg_apply,norm_neg]
    rw [he]
    apply hb.trans
    apply (le_div_iff₀ (pow_pos hr k)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1) (mul_nonneg hK hM)
  have hb := hh hr (f-h) a g (K*M) (mul_nonneg hK hM)
    ⟨O,hO,hOW,hχO,hg⟩ hd heq
  dsimp only
  intro x hx
  apply (hb x hx).trans
  have hm : 0 ≤ M*t.1^3 := mul_nonneg hM (pow_nonneg hr.le _)
  nlinarith [norm_nonneg (antiToEnergy A J α hs ht a),mul_nonneg hC hm,
    mul_nonneg hK (norm_nonneg (antiToEnergy A J α hs ht a))]
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScaledOffData
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hH hweak hB hdual in

theorem geometric_scaled_off_source_of_data :
      ∀ (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
        (_hU : IsOpen U) (hUD : U ⊆ (D p).domain)
        (_hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
        (_hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
        (K : Set Space) (_hK : IsCompact K) (hKU : K ⊆ U)
        (q : Space) (_hq : q ∈ U)
        (ζ : 𝓢(Space,ℂ)) (_hζ : HasCompactSupport (ζ : Space → ℂ))
        (χ : ℕ → 𝓢(Space,ℂ)) (_hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
        (_hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
        (_hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1),
      ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (hr : 0 < t.1),
      t.1 ≤ 1 → ∀ (φ : 𝓢(Space,ℝ))
        (hc : HasCompactSupport (φ : Space → ℝ)) (hφK : tsupport φ ⊆ K)
        (j : Fin 2) (b : Space) (R M : ℝ), 0 ≤ R → 0 ≤ M →
        tsupport φ ⊆ Metric.ball b R → (∀ z, |φ z| ≤ M) →
        (∀ n ≤ 3, tsupport (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1))) ⊆ W \ tsupport φ) →
        let f := testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
        let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))
        ∀ x : Space, ((χ 4 : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
          t.1*‖u (t.1 • x+L t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u) (t.1 • x+L t.2)‖ +
            t.1^3*∑ i, ∑ k, ‖(∂_{stdOrthonormalBasis ℝ Space k} (∂_{stdOrthonormalBasis ℝ Space i} u)) (t.1 • x+L t.2)‖ ≤
          C*M*R^3 := by
  intro p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_off_source_two_jet A J α hs ht D hD p τ ρ hU hUD hτ hρ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨E,hE,hsource⟩ := geometric_scaled_source_dual A J α hs ht D hD p τ hK (hKU.trans hUD)
    (fun z hz => hτ z (hKU hz))
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C*(1+B)*E,by positivity,?_⟩
  filter_upwards [hest] with t hh
  intro hr hr1 φ hc hφK j b R M hR hM hball hbound hobs
  let f := testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
  have hd : ∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ (E*M*R^3)*‖v‖ :=
    hsource φ hc hφK j b R M hR hM hball hbound
  have hEM : 0 ≤ E*M*R^3 := by positivity
  have ha := hdual f (E*M*R^3) hEM hd
  have hz : ∀ z ∈ W \ tsupport φ, rawPair J α ht p.val (D p) f.val.val z = 0 := by
    intro z hzz
    change rawPair J α ht p.val (D p) (manifoldTest J α ht p.val (D p) (componentTest j φ)) z = 0
    rw [rawPair_manifoldTest J α ht p.val (D p)
      ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD))) (hUD (hWU hzz.1))]
    rw [componentTest_apply,image_eq_zero_of_notMem_tsupport hzz.2,zero_smul]
  have hb := hh hr hr1 f (H f) (Gs f) (E*M*R^3) hEM (hH f) hd
    ⟨W \ tsupport φ,hW.sdiff (isClosed_tsupport φ),sdiff_subset,hobs,hz⟩ (hweak f)
  dsimp only
  intro x hx
  apply (hb x hx).trans
  calc
    C*(E*M*R^3*t.1^3+‖antiToEnergy A J α hs ht (Gs f)‖) ≤ C*(E*M*R^3+B*(E*M*R^3)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hp := mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1 : t.1^3 ≤ 1) hEM
      nlinarith only [hp,ha]
    _ = C*(1+B)*E*M*R^3 := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem closedLift_scaled_off_source :
      ∀ (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
        (_hU : IsOpen U) (hUD : U ⊆ (D p).domain)
        (_hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
        (_hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
        (K : Set Space) (_hK : IsCompact K) (hKU : K ⊆ U)
        (q : Space) (_hq : q ∈ U)
        (ζ : 𝓢(Space,ℂ)) (_hζ : HasCompactSupport (ζ : Space → ℂ))
        (χ : ℕ → 𝓢(Space,ℂ)) (_hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
        (_hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
        (_hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
        (_hχ0 : ((χ 4 : Space → ℂ) =ᶠ[𝓝 0] fun _ => 1)),
      ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (hr : 0 < t.1),
      t.1 ≤ 1 → ∀ (φ : 𝓢(Space,ℝ))
        (hc : HasCompactSupport (φ : Space → ℝ)) (hφK : tsupport φ ⊆ K)
        (j : Fin 2) (b : Space) (R M : ℝ), 0 ≤ R → 0 ≤ M →
        tsupport φ ⊆ Metric.ball b R → (∀ z, |φ z| ≤ M) →
        (∀ n ≤ 3, tsupport (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1))) ⊆ W \ tsupport φ) →
        let f := testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
        ‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
          (extChartAt Model p.val).symm t.2 -
          ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm t.2‖ ≤
          C*M*R^3/t.1^3 := by
  intro p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ hχ0
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_scaled_off_source_of_data A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  have hKV : Metric.closedBall q (ε/2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεV
  obtain ⟨C₀,hC₀,hout⟩ := closedLift_scaled_basis_local_bound A J α hs ht D hD
    (stdOrthonormalBasis ℝ Space).toBasis p τ η L
    hV (hVW.trans (hWU.trans hUD))
    (fun z hz => hτ z (hWU (hVW hz))) hηone (isCompact_closedBall q (ε/2)) hKV
  have htK : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), t.2 ∈ Metric.closedBall q (ε/2) :=
    (continuous_snd.tendsto (0,q)).eventually (Metric.closedBall_mem_nhds q (by positivity))
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C₀*C,mul_nonneg hC₀ hC,?_⟩
  filter_upwards [hest,htK] with t hh htK
  intro hr hr1 φ hc hφK j b R M hR hM hball hbound hobs
  dsimp only
  let f := testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
  have hj := hh hr hr1 φ hc hφK j b R M hR hM hball hbound hobs 0 hχ0
  have ho := hout H Gs f t.2 htK t.1 (C*M*R^3) hr hr1 (by
    simpa only [smul_zero,zero_add,OrthonormalBasis.coe_toBasis] using hj)
  apply (le_div_iff₀ (pow_pos hr 3)).mpr
  calc
    _ = t.1^3*‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
        (extChartAt Model p.val).symm t.2 -
        ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm t.2‖ := mul_comm _ _
    _ ≤ C₀*(C*M*R^3) := ho
    _ = C₀*C*M*R^3 := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialScalarOff
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem closedLift_scalar_off_source_oai
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    (hχ0 : ((χ 4 : Space → ℂ) =ᶠ[𝓝 0] fun _ => 1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q),
      ∀ (_hr : 0 < t.1), t.1 ≤ 1 →
      ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
        (hφK : tsupport φ ⊆ K) (j : Fin 2) (b : Space) (R M : ℝ), 0 ≤ R → 0 ≤ M →
        tsupport φ ⊆ Metric.ball b R → (∀ z, |φ z| ≤ M) →
        R+c*t.1 ≤ dist b t.2 →
        let f := testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
        ‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
          (extChartAt Model p.val).symm t.2 -
          ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm t.2‖ ≤ C*M*R^3/t.1^3 := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,he⟩ :=
    closedLift_scaled_off_source A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ hχ0
  obtain ⟨c,hc,hcs⟩ := normalizedCutoffs_bounded_radius L χ hcχ
  have hshrink : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), ∀ n : Fin 4, ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr (χ (n.val+1))) ⊆ W := by
    apply Filter.eventually_all.mpr
    intro n
    exact normalizedCutoff_eventually_support L q (χ (n.val+1)) (hcχ n.val (by omega)) hW hqW
  refine ⟨c,hc,C,hC,?_⟩
  filter_upwards [he,hshrink] with t htest hts
  intro hr hr1 φ hφc hφK j b R M hR hM hball hval hsep
  dsimp only
  apply htest hr hr1 φ hφc hφK j b R M hR hM hball hval
  intro n hn z hz
  refine ⟨hts ⟨n,by omega⟩ hr.ne' hz,?_⟩
  intro hφz
  exact Set.disjoint_left.mp (closedBall_ball_disjoint_of_radii hsep)
    (hcs n hn t.2 t.1 hr hz) (hball hφz)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source_oai.{u_1}
