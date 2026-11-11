-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffLog_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:30:38.063196+00:00
-- url     : https://prove2.me/submissions/a5bf6747-7ef4-4b09-a6b5-82d19c95e556

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc029

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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

local instance instFactLeENNRealOfNat_solutions_r5f3bf5_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.componentTest_apply _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
local instance instFactLeENNRealOfNat_solutions_r5f3bf5_2 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
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

local instance localInst_r5f3bf5_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGradientBridge
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
namespace TamingCompatibility.RadialPotential
open Set
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma logGradientProfile_scale {r s : ℝ} (hr : 0 < r) (z v : E) :
    r * logGradientProfile (r*s) (r • z) v = logGradientProfile s z v := by
  simp only [logGradientProfile,norm_smul,Real.norm_of_nonneg (le_of_lt hr),real_inner_smul_left]
  rw [show (r*s)^2+(r*‖z‖)^2 = r^2*(s^2+‖z‖^2) by ring,mul_inv_rev]
  field_simp

end TamingCompatibility.RadialPotential
end
end

end

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

lemma shellCutoff_compact [ProperSpace E] {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (shellCutoff r : E → ℝ) :=
  (isCompact_closedBall (0:E) (4*r)).of_isClosed_subset (isClosed_tsupport _)
    (fun _z hz => (shellCutoff_tsupport hr hz).1)

lemma scaledCutoff_scale {r : ℝ} (hr : r ≠ 0) (a : ℝ) (z : E) :
    scaledCutoff (r*a) (r • z) = scaledCutoff a z := by
  dsimp only [scaledCutoff]
  congr 1
  rw [smul_smul, mul_inv_rev]
  field_simp

lemma shellCutoff_scale {r : ℝ} (hr : r ≠ 0) (z : E) :
    shellCutoff r (r • z) = shellCutoff 1 z := by
  dsimp only [shellCutoff]
  rw [mul_comm (2:ℝ) r, scaledCutoff_scale hr]
  have h := scaledCutoff_scale hr (1:ℝ) z
  simpa using congrArg (fun a => scaledCutoff (2:ℝ) z - a) h

lemma dyadic_cutoff_telescope (r : ℝ) (N : ℕ) (z : E) :
    scaledCutoff r z + ∑ j ∈ Finset.range N, shellCutoff (r*2^j) z =
      scaledCutoff (r*2^N) z := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    simp only [shellCutoff, pow_succ]
    rw [show 2*(r*2^N) = r*(2^N*2) by ring]
    ring

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma exists_dyadic_reconstruction_scale {r : ℝ} (hr : 0 < r) (R : ℝ) :
    ∃ N : ℕ, R ≤ r*2^N := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R/r) (by norm_num : (1:ℝ) < 2)
  exact ⟨N, by simpa [mul_comm] using (div_le_iff₀ hr).mp (le_of_lt hN)⟩

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RadialParameterJets
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter
open scoped ContDiff Topology
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cutoff_parameter_smooth (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (h0 : (0:E) ∉ tsupport χ) (f : P → E → ℝ)
    (hf : ∀ p : P × E, p.2 ≠ 0 → ContDiffAt ℝ ∞ (fun q : P × E => f q.1 q.2) p) :
    ContDiff ℝ ∞ (fun p : P × E => χ p.2 * f p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 = 0
  · have hz : χ =ᶠ[𝓝 p.2] 0 := by
      rw [hp]
      exact notMem_tsupport_iff_eventuallyEq.mp h0
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : P × E => (0:ℝ)) p).congr_of_eventuallyEq
    filter_upwards [hz.comp_tendsto continuous_snd.continuousAt] with q hq
    change χ q.2 = 0 at hq
    rw [hq,zero_mul]
  · exact (hχ.comp contDiff_snd).contDiffAt.mul (hf p hp)

lemma norm_iteratedFDeriv_parameter_slice_le (f : P × E → ℝ) (hf : ContDiff ℝ ∞ f)
    (a : P) (z : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f (a,x)) z‖ ≤ ‖iteratedFDeriv ℝ n f (a,z)‖ := by
  let L := ContinuousLinearMap.inr ℝ P E
  have he : (fun x : E => f (a,x)) = (fun q : P × E => f ((a,0)+q)) ∘ L := by
    funext x
    simp [L]
  have hshift : ContDiff ℝ ∞ (fun q : P × E => f ((a,0)+q)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [he,L.iteratedFDeriv_comp_right hshift z
    (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n (fun q : P × E => f ((a,0)+q)) (L z)) (fun _ : Fin n => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hnorm
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ P E
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun q : P × E => f ((a,0)+q)) (L z)‖ * ‖L‖^n := hnorm
    _ ≤ ‖iteratedFDeriv ℝ n (fun q : P × E => f ((a,0)+q)) (L z)‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg L) hL) (norm_nonneg _)
    _ = _ := by rw [iteratedFDeriv_comp_add_left]; simp [L]

lemma parameter_slice_derivatives_bounded (f : P × E → ℝ) (hf : ContDiff ℝ ∞ f)
    {K : Set P} (hK : IsCompact K) {S : Set E} (hS : IsCompact S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ z ∈ S,
      ‖iteratedFDeriv ℝ n (fun x => f (a,x)) z‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hK.prod hS).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := n) (WithTop.coe_le_coe.mpr le_top)).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro a ha z hz
  exact (norm_iteratedFDeriv_parameter_slice_le f hf a z n).trans
    ((hC (a,z) ⟨ha,hz⟩).trans (le_max_left _ _))

lemma compact_parameter_family_derivatives_bounded (f : P → E → ℝ)
    (hf : ContDiff ℝ ∞ (fun p : P × E => f p.1 p.2))
    {K : Set P} (hK : IsCompact K) {S : Set E} (hS : IsCompact S)
    (hsupp : ∀ a ∈ K, tsupport (f a) ⊆ S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (f a) z‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := parameter_slice_derivatives_bounded
    (fun p : P × E => f p.1 p.2) hf hK hS n
  refine ⟨C,hC,?_⟩
  intro a ha z
  by_cases hz : z ∈ S
  · exact hbound a ha z hz
  · have hz' : z ∉ tsupport (iteratedFDeriv ℝ n (f a)) := by
      intro h
      exact hz (hsupp a ha ((tsupport_iteratedFDeriv_subset n) h))
    rw [image_eq_zero_of_notMem_tsupport hz',norm_zero]
    exact hC

lemma compact_parameter_cutoff_derivatives_bounded (χ : E → ℝ)
    (hχc : HasCompactSupport χ) (f : P → E → ℝ)
    (hf : ContDiff ℝ ∞ (fun p : P × E => χ p.2 * f p.1 p.2))
    {K : Set P} (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (fun x => χ x * f a x) z‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := parameter_slice_derivatives_bounded
    (fun p : P × E => χ p.2 * f p.1 p.2) hf hK hχc n
  refine ⟨C,hC,?_⟩
  intro a ha z
  by_cases hz : z ∈ tsupport χ
  · exact hbound a ha z hz
  · have hz' : z ∉ tsupport (iteratedFDeriv ℝ n (fun x => χ x * f a x)) := by
      intro h
      exact hz (tsupport_mul_subset_left ((tsupport_iteratedFDeriv_subset n) h))
    rw [image_eq_zero_of_notMem_tsupport hz',norm_zero]
    exact hC
end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]

lemma cutoffLogError_derivatives_bounded [ProperSpace E]
    (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) {R : ℝ} (hR : 0 < R)
    {K : Set E} (hK : IsCompact K) (S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (cutoffLogError W V R (s,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_family_derivatives_bounded (cutoffLogError W V R)
    (cutoffLogError_smooth W V hW hV hR) (isCompact_Icc.prod hK) (isCompact_closedBall (0:E) (2*R))
    (fun p _hp => cutoffLogError_tsupport W V hR p) n
  exact ⟨C,hC,fun s hs b hb z => h (s,b) ⟨hs,hb⟩ z⟩

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialDilations
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Function
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma norm_iteratedFDeriv_dilate_le (f : E → F) (hf : ContDiff ℝ ∞ f)
    {r : ℝ} (hr : 0 < r) (b x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => f (r⁻¹ • (z-b))) x‖ ≤
      ‖iteratedFDeriv ℝ n f (r⁻¹ • (x-b))‖ / r^n := by
  let L : E →L[ℝ] E := r⁻¹ • ContinuousLinearMap.id ℝ E
  have hd : (fun z => f (r⁻¹ • (z-b))) = (fun z => (f ∘ L) (z-b)) := rfl
  rw [hd,iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right hf (x-b)
    (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  have hL : ‖L‖ ≤ r⁻¹ := by
    calc
      _ = ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ E‖ := norm_smul _ _
      _ ≤ r⁻¹ * 1 := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (L (x-b))‖ * ∏ _i : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n f (L (x-b))‖ * ‖L‖^n := by simp
    _ ≤ ‖iteratedFDeriv ℝ n f (L (x-b))‖ * (r⁻¹)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL n) (norm_nonneg _)
    _ = _ := by simp [L,div_eq_mul_inv]

lemma norm_iteratedFDeriv_scaled_dilate_le (f : E → F) (hf : ContDiff ℝ ∞ f)
    {r : ℝ} (hr : 0 < r) (A : ℝ) (b x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => A • f (r⁻¹ • (z-b))) x‖ ≤
      |A| * ‖iteratedFDeriv ℝ n f (r⁻¹ • (x-b))‖ / r^n := by
  have hcomp : ContDiff ℝ ∞ (fun z : E => f (r⁻¹ • (z-b))) :=
    hf.comp (contDiff_const.smul (contDiff_id.sub contDiff_const))
  rw [iteratedFDeriv_const_smul_apply' (hcomp.of_le
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |A| * (‖iteratedFDeriv ℝ n f (r⁻¹ • (x-b))‖ / r^n) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_dilate_le f hf hr b x n) (abs_nonneg _)
    _ = _ := by ring

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialVariableProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [HasContDiffBump E]
lemma shellCutoff_origin_not_tsupport {r : ℝ} (hr : 0 < r) :
    (0:E) ∉ tsupport (shellCutoff r : E → ℝ) := by
  intro h
  exact (shellCutoff_tsupport hr h).2 (by simpa using hr)

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialJetConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential

lemma finite_radialJet_constant (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (D₀ : ℝ) (hD₀ : 0 ≤ D₀) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ D₀ ≤ C ∧ ∀ k ≤ N, D k ≤ C/(5:ℝ)^k := by
  let C := D₀ + ∑ k ∈ Finset.range (N+1), D k * (5:ℝ)^k
  have hc : D₀ ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => mul_nonneg (hD k) (pow_nonneg (by norm_num) k)))
  refine ⟨C,hD₀.trans hc,hc,?_⟩
  intro k hk
  apply (le_div_iff₀ (by positivity : 0 < (5:ℝ)^k)).mpr
  have hkC : D k * (5:ℝ)^k ≤ ∑ i ∈ Finset.range (N+1), D i * (5:ℝ)^i :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hD i) (pow_nonneg (by norm_num) i))
      (Finset.mem_range.mpr (by omega))
  exact hkC.trans (le_add_of_nonneg_left hD₀)

lemma radialJet_rescale {C D r : ℝ} (hr : 0 < r) (k d : ℕ)
    (h : D ≤ C/(5:ℝ)^k) :
    D/r^(k+d) ≤ (C/r^d)/(5*r)^k := by
  calc
    _ ≤ (C/(5:ℝ)^k)/r^(k+d) := div_le_div_of_nonneg_right h (pow_nonneg hr.le _)
    _ = _ := by rw [mul_pow,pow_add]; field_simp
end TamingCompatibility.RadialPotential

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

local instance instFactLeENNRealOfNatOfRealHDivReal_solutions_2_r5f3bf5_1 : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialMixedDyadic
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped BigOperators

lemma sum_dyadic_square_le {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    ∑ j ∈ Finset.range N, (s*2^j)^2 ≤ (s*2^N)^2 := by
  induction N with
  | zero => simpa using pow_nonneg hs 2
  | succ N ih =>
    rw [Finset.sum_range_succ,pow_succ (2:ℝ)]
    nlinarith [sq_nonneg (s*2^N)]

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialMixedLogDyadic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential

lemma exists_minimal_dyadic_scale {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) :
    ∃ N : ℕ, R ≤ s*2^N ∧ s*2^N ≤ 2*R ∧ ∀ j < N, s*2^j < R := by
  let h := exists_dyadic_reconstruction_scale hs R
  let N := Nat.find h
  have hN : R ≤ s*2^N := Nat.find_spec h
  have hmin : ∀ j < N, s*2^j < R := by
    intro j hj
    exact lt_of_not_ge (Nat.find_min h hj)
  refine ⟨N,hN,?_,hmin⟩
  cases hNe : N with
  | zero => simpa using (show s ≤ 2*R by linarith)
  | succ n =>
    rw [pow_succ]
    have hn := hmin n (by simpa only [hNe] using Nat.lt_succ_self n)
    nlinarith

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hermitianLogGradient_scale (K : E →L[ℝ] E) {r s : ℝ} (hr : 0 < r) (z v : E) :
    r * hermitianLogGradientProfile K (r*s) (r • z) v = hermitianLogGradientProfile K s z v := by
  simp only [hermitianLogGradient_eq,map_smul]
  exact logGradientProfile_scale hr _ _

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E]
variable (K : E →L[ℝ] E)

lemma firstOrderSource_cutoffLog (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (z : E) :
    firstOrderSource V (cutoffLogPotential K R s) z =
      scaledCutoff R z * hermitianLogGradientProfile K s z (V z) +
      hermitianLogPotential K s z * fderiv ℝ (scaledCutoff R) z (V z) := by
  change fderiv ℝ (fun x => scaledCutoff R x * hermitianLogPotential K s x) z (V z) = _
  rw [fderiv_fun_mul ((scaledCutoff_smooth R).differentiable (by simp) z)
      ((hermitianLogPotential_smooth K hs).differentiable (by simp) z)]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  rw [← hermitianLogGradient_eq_fderiv K hs]

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianVariableProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma variableLogProfile_smooth (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ) (h0 : (0:E) ∉ tsupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => variableLogProfile W χ a V q.1 q.2) := by
  unfold variableLogProfile
  refine cutoff_parameter_smooth χ hχ h0
    (fun (p : ℝ × ℝ × E) z => a (p.2.1•z) * hermitianLogGradientProfile (W p.2.2) p.1 z
      (V (p.2.2+p.2.1•z))) ?_
  intro p hp
  have hpos : 0 < p.1.1^2+‖p.2‖^2+‖W p.1.2.2 p.2‖^2 := by
    have hz := norm_pos_iff.mpr hp
    nlinarith [sq_nonneg p.1.1,sq_nonneg ‖W p.1.2.2 p.2‖]
  have hscale : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => q.1.2.1 • q.2) :=
    contDiff_fst.snd.fst.smul contDiff_snd
  have hpoint : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => q.1.2.2+q.1.2.1•q.2) :=
    contDiff_fst.snd.snd.add hscale
  have hmetric : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => W q.1.2.2) :=
    hW.comp contDiff_fst.snd.snd
  have hden : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E =>
      q.1.1^2+‖q.2‖^2+‖W q.1.2.2 q.2‖^2) :=
    ((contDiff_fst.fst.pow 2).add ((contDiff_norm_sq ℝ).comp contDiff_snd)).add
      ((contDiff_norm_sq ℝ).comp (hmetric.clm_apply contDiff_snd))
  have hnum : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E =>
      ⟪q.2,V (q.1.2.2+q.1.2.1•q.2)⟫+
        ⟪W q.1.2.2 q.2,W q.1.2.2 (V (q.1.2.2+q.1.2.1•q.2))⟫) :=
    (contDiff_snd.inner ℝ (hV.comp hpoint)).add
      ((hmetric.clm_apply contDiff_snd).inner ℝ (hmetric.clm_apply (hV.comp hpoint)))
  exact (ha.comp hscale).contDiffAt.mul ((hden.contDiffAt.inv hpos.ne').mul hnum.contDiffAt)

lemma variableLogProfile_derivatives_bounded (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (h0 : (0:E) ∉ tsupport χ) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) R, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (variableLogProfile W χ a V (t,r,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_cutoff_derivatives_bounded χ hχc
    (fun (p : ℝ × ℝ × E) z => a (p.2.1•z) * hermitianLogGradientProfile (W p.2.2) p.1 z
      (V (p.2.2+p.2.1•z)))
    (variableLogProfile_smooth W χ a V hW hχ h0 ha hV)
    (isCompact_Icc.prod (isCompact_Icc.prod hK)) n
  exact ⟨C,hC,fun t ht r hr b hb z => h (t,r,b) ⟨ht,hr,hb⟩ z⟩

variable [HasContDiffBump E]
lemma variableLogProfile_shell_scale (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {r s : ℝ} (hr : 0 < r) (b z : E) :
    r * (shellCutoff r (r•z) * (a (r•z) * hermitianLogGradientProfile (W b) s (r•z) (V (b+r•z)))) =
      variableLogProfile W (shellCutoff 1) a V (s/r,r,b) z := by
  rw [shellCutoff_scale hr.ne']
  have h := hermitianLogGradient_scale (W b) hr (s := s/r) z (V (b+r•z))
  rw [mul_div_cancel₀ s hr.ne'] at h
  dsimp only [variableLogProfile]
  calc
    _ = shellCutoff 1 z * (a (r•z) * (r * hermitianLogGradientProfile (W b) s (r•z) (V (b+r•z)))) := by ring
    _ = _ := by rw [h]

end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma innerLogProfile_smooth (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun q : (ℝ × E) × E => variableLogProfile W χ a V (1,q.1.1,q.1.2) q.2) := by
  have hscale : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => q.1.1 • q.2) :=
    contDiff_fst.fst.smul contDiff_snd
  have hpoint : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => q.1.2 + q.1.1 • q.2) :=
    contDiff_fst.snd.add hscale
  have hmetric : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => W q.1.2) :=
    hW.comp contDiff_fst.snd
  have hden : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => (1:ℝ)^2 + ‖q.2‖^2 + ‖W q.1.2 q.2‖^2) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_snd)).add
      ((contDiff_norm_sq ℝ).comp (hmetric.clm_apply contDiff_snd))
  have hpos : ∀ q : (ℝ × E) × E, 0 < (1:ℝ)^2 + ‖q.2‖^2 + ‖W q.1.2 q.2‖^2 := by
    intro q; nlinarith [sq_nonneg ‖q.2‖,sq_nonneg ‖W q.1.2 q.2‖]
  have hnum : ContDiff ℝ ∞ (fun q : (ℝ × E) × E =>
      ⟪q.2,V (q.1.2+q.1.1•q.2)⟫ + ⟪W q.1.2 q.2,W q.1.2 (V (q.1.2+q.1.1•q.2))⟫) :=
    (contDiff_snd.inner ℝ (hV.comp hpoint)).add
      ((hmetric.clm_apply contDiff_snd).inner ℝ (hmetric.clm_apply (hV.comp hpoint)))
  exact (hχ.comp contDiff_snd).mul ((ha.comp hscale).mul
    ((hden.inv (fun q => (hpos q).ne')).mul hnum))

lemma innerLogProfile_derivatives_bounded (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) R, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (variableLogProfile W χ a V (1,r,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_cutoff_derivatives_bounded χ hχc
    (fun (p : ℝ × E) z => a (p.1 • z) * hermitianLogGradientProfile (W p.2) 1 z (V (p.2 + p.1 • z)))
    (innerLogProfile_smooth W χ a V hW hχ ha hV) (isCompact_Icc.prod hK) n
  exact ⟨C,hC,fun r hr b hb z => h (r,b) ⟨hr,hb⟩ z⟩

variable [HasContDiffBump E]
lemma variableLogProfile_inner_scale (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b z : E) :
    s * (scaledCutoff s (s • z) * (a (s • z) * hermitianLogGradientProfile (W b) s (s • z) (V (b+s•z)))) =
      variableLogProfile W (scaledCutoff 1) a V (1,s,b) z := by
  have hc : scaledCutoff s (s • z) = scaledCutoff 1 z := by
    simpa using scaledCutoff_scale hs.ne' 1 z
  rw [hc]
  have h := hermitianLogGradient_scale (W b) hs (s := 1) z (V (b+s•z))
  rw [mul_one] at h
  dsimp only [variableLogProfile]
  calc
    _ = scaledCutoff 1 z * (a (s • z) * (s * hermitianLogGradientProfile (W b) s (s • z) (V (b+s•z)))) := by ring
    _ = _ := by rw [h]

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianPhysicalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [ProperSpace E] in
lemma logShell_eq_normalized (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {r s : ℝ} (hr : 0 < r) (b x : E) :
    shellCutoff r x * logSingularSource W a V s b x =
      r⁻¹ • variableLogProfile W (shellCutoff 1) a V (s/r,r,b) (r⁻¹ • (x-0)) := by
  have h := variableLogProfile_shell_scale W a V (s := s) hr b (r⁻¹ • x)
  simp only [smul_smul,mul_inv_cancel₀ hr.ne',one_smul] at h
  rw [sub_zero,← h]
  simp [logSingularSource,smul_eq_mul,← mul_assoc,hr.ne']

omit [ProperSpace E] in
lemma logInner_eq_normalized (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b x : E) :
    scaledCutoff s x * logSingularSource W a V s b x =
      s⁻¹ • variableLogProfile W (scaledCutoff 1) a V (1,s,b) (s⁻¹ • (x-0)) := by
  have h := variableLogProfile_inner_scale W a V hs b (s⁻¹ • x)
  simp only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] at h
  rw [sub_zero,← h]
  simp [logSingularSource,smul_eq_mul,← mul_assoc,hs.ne']

lemma logShell_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (fun z => shellCutoff r z * logSingularSource W a V s b z) x‖ ≤
        C / r^(n+1) := by
  obtain ⟨C,hC,hbound⟩ := variableLogProfile_derivatives_bounded W (shellCutoff 1) a V
    hW (shellCutoff_smooth _) (shellCutoff_compact (by norm_num))
    (shellCutoff_origin_not_tsupport (by norm_num)) ha hV hK R n
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hb x
  have hsr : s/r ∈ Icc (0:ℝ) 1 := ⟨div_nonneg hs.1 hr.1.le,(div_le_one hr.1).mpr hs.2⟩
  have hf : ContDiff ℝ ∞ (variableLogProfile W (shellCutoff 1) a V (s/r,r,b)) :=
    (variableLogProfile_smooth W (shellCutoff 1) a V hW (shellCutoff_smooth _)
      (shellCutoff_origin_not_tsupport (by norm_num)) ha hV).comp (contDiff_const.prodMk contDiff_id)
  have he : (fun z => shellCutoff r z * logSingularSource W a V s b z) =
      fun z => r⁻¹ • variableLogProfile W (shellCutoff 1) a V (s/r,r,b) (r⁻¹ • (z-0)) :=
    funext (logShell_eq_normalized W a V hr.1 b)
  rw [he]
  calc
    _ ≤ |r⁻¹| * ‖iteratedFDeriv ℝ n (variableLogProfile W (shellCutoff 1) a V (s/r,r,b))
        (r⁻¹ • (x-0))‖ / r^n := norm_iteratedFDeriv_scaled_dilate_le _ hf hr.1 r⁻¹ 0 x n
    _ ≤ |r⁻¹| * C / r^n := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound _ hsr r ⟨hr.1.le,hr.2⟩ b hb _) (abs_nonneg _))
      (pow_nonneg hr.1.le n)
    _ = _ := by rw [abs_of_pos (inv_pos.mpr hr.1),pow_succ]; field_simp

lemma logInner_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (fun z => scaledCutoff s z * logSingularSource W a V s b z) x‖ ≤
        C / s^(n+1) := by
  obtain ⟨C,hC,hbound⟩ := innerLogProfile_derivatives_bounded W (scaledCutoff 1) a V
    hW (scaledCutoff_smooth _) (scaledCutoff_compact (by norm_num)) ha hV hK R n
  refine ⟨C,hC,?_⟩
  intro s hs b hb x
  have hf : ContDiff ℝ ∞ (variableLogProfile W (scaledCutoff 1) a V (1,s,b)) :=
    (innerLogProfile_smooth W (scaledCutoff 1) a V hW (scaledCutoff_smooth _) ha hV).comp
      ((show ContDiff ℝ ∞ (fun _ : E => (s,b)) from contDiff_const).prodMk contDiff_id)
  have he : (fun z => scaledCutoff s z * logSingularSource W a V s b z) =
      fun z => s⁻¹ • variableLogProfile W (scaledCutoff 1) a V (1,s,b) (s⁻¹ • (z-0)) :=
    funext (logInner_eq_normalized W a V hs.1 b)
  rw [he]
  calc
    _ ≤ |s⁻¹| * ‖iteratedFDeriv ℝ n (variableLogProfile W (scaledCutoff 1) a V (1,s,b))
        (s⁻¹ • (x-0))‖ / s^n := norm_iteratedFDeriv_scaled_dilate_le _ hf hs.1 s⁻¹ 0 x n
    _ ≤ |s⁻¹| * C / s^n := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound s ⟨hs.1.le,hs.2⟩ b hb _) (abs_nonneg _))
      (pow_nonneg hs.1.le n)
    _ = _ := by rw [abs_of_pos (inv_pos.mpr hs.1),pow_succ]; field_simp

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianShiftedSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [ProperSpace E] in
lemma shiftedLogShell_weight (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) :
    ρ z * shiftedLogShell W a V r s b z =
      shiftedLogShell W a (fun w => ρ w • V w) r s b z := by
  simp [shiftedLogShell,shiftedLogSource,logSingularSource,hermitianLogGradientProfile,map_smul,
    real_inner_smul_right]
  ring
omit [ProperSpace E] in
lemma shiftedLogInner_weight (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E) (s : ℝ) (b z : E) :
    ρ z * shiftedLogInner W a V s b z =
      shiftedLogInner W a (fun w => ρ w • V w) s b z := by
  simp [shiftedLogInner,shiftedLogSource,logSingularSource,hermitianLogGradientProfile,map_smul,
    real_inner_smul_right]
  ring

lemma shiftedLogShell_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedLogShell W a V r s b) x‖ ≤ C/r^(n+1) := by
  obtain ⟨C,hC,hb⟩ := logShell_derivatives_bounded W a V hW ha hV hK R n
  refine ⟨C,hC,fun r hr s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => shellCutoff r y * logSingularSource W a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => shellCutoff r y * logSingularSource W a V s b y) n b x]
  exact hb r hr s hs b hbK (x-b)
lemma shiftedLogInner_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedLogInner W a V s b) x‖ ≤ C/s^(n+1) := by
  obtain ⟨C,hC,hb⟩ := logInner_derivatives_bounded W a V hW ha hV hK R n
  refine ⟨C,hC,fun s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => scaledCutoff s y * logSingularSource W a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => scaledCutoff s y * logSingularSource W a V s b y) n b x]
  exact hb s hs b hbK (x-b)

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianErrorSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [ProperSpace E] in
lemma shiftedLogError_weight (ρ : E → ℝ) (W : E → E →L[ℝ] E) (V : E → E) (R s : ℝ) (b z : E) :
    ρ z * shiftedLogError W V R s b z = shiftedLogError W (fun w => ρ w • V w) R s b z := by
  simp only [shiftedLogError,cutoffLogError,add_sub_cancel,ContinuousLinearMap.map_smul,smul_eq_mul]
  ring

lemma shiftedLogError_derivatives_bounded (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) {K : Set E} (hK : IsCompact K) (S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (shiftedLogError W V R s b) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := cutoffLogError_derivatives_bounded W V hW hV hR hK S n
  refine ⟨C,hC,fun s hs b hbK z => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => cutoffLogError W V R (s,b) (z-b)) z‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  exact hb s hs b hbK (z-b)

variable (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) {R : ℝ} (hR : 0 < R)

lemma logErrorSchwartz_uniform_inputs (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    {K : Set E} (hK : IsCompact K) (S : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K,
      (∀ z, |logErrorSchwartz W V hW hV hR s b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n (fun z => ρ z * logErrorSchwartz W V hW hV hR s b z) z‖ ≤ C) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogError_derivatives_bounded W V hW hV hR hK S 0
  choose D hD hb using fun n => shiftedLogError_derivatives_bounded W
    (fun w => ρ w • V w) hW (hρ.smul hV) hR hK S n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
    exact h.trans hC₀
  · intro n hn z
    have he : (fun z => ρ z * logErrorSchwartz W V hW hV hR s b z) =
        shiftedLogError W (fun w => ρ w • V w) R s b :=
      funext (shiftedLogError_weight ρ W V R s b)
    rw [he]
    exact (hb n s hs b hbK z).trans ((hCD n hn).trans
      (div_le_self hC (one_le_pow₀ (by norm_num))))

end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R)

lemma logSourceSchwartz_reconstruction {s : ℝ} (hs : 0 < s) (b : E)
    (N : ℕ) (hN : R ≤ s*2^N) :
    logSourceSchwartz W a V ha hV R haR hs b = logInnerSchwartz W a V ha hV hs b +
    ∑ j ∈ Finset.range N, logShellSchwartz W a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b := by
  apply SchwartzMap.ext
  intro z
  change shiftedLogSource W a V s b z = shiftedLogInner W a V s b z +
    (∑ j ∈ Finset.range N, logShellSchwartz W a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b) z
  rw [sum_apply]
  change shiftedLogSource W a V s b z = scaledCutoff s (z-b) * shiftedLogSource W a V s b z +
    ∑ j ∈ Finset.range N, shellCutoff (s*2^j) (z-b) * shiftedLogSource W a V s b z
  rw [← Finset.sum_mul,← add_mul,dyadic_cutoff_telescope]
  by_cases hz : ‖z-b‖ ≤ s*2^N
  · rw [scaledCutoff_one (mul_pos hs (by positivity)) hz,one_mul]
  · have ha0 : a (z-b) = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
      have hh := haR h
      simp only [mem_closedBall,dist_zero_right] at hh
      exact hz (hh.trans hN))
    simp [shiftedLogSource,logSingularSource,ha0]

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianSupportedSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) (K : Set E)

lemma logSupported_reconstruction {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K)
    (N : ℕ) (hN : R ≤ s*2^N) :
    logSourceSupported W a V ha hV R haR K hs b hb =
      logInnerSupported W a V ha hV R haR K hs b hb +
      ∑ j ∈ Finset.range N, logShellSupported W a V ha hV R haR K
        (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b hb := by
  apply Subtype.ext
  simpa only [Submodule.coe_add,Submodule.coe_sum,logSourceSupported,logInnerSupported,logShellSupported] using
    logSourceSchwartz_reconstruction W a V ha hV R haR hs b N hN

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E)

omit [ProperSpace E] in
lemma firstOrderSource_translatedCutoffLog (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (b z : E) :
    firstOrderSource V (translatedCutoffLog W R s b) z =
      shiftedLogSource W (scaledCutoff R) V s b z + shiftedLogError W V R s b z := by
  change fderiv ℝ (fun z => cutoffLogPotential (W b) R s (z-b)) z (V z) = _
  rw [fderiv_comp_sub]
  simpa [firstOrderSource,shiftedLogSource,logSingularSource,shiftedLogError,cutoffLogError] using
    firstOrderSource_cutoffLog (W b) (fun w => V (b+w)) R hs (z-b)

variable (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)

lemma logCutoffSourceSupported_eq (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    logCutoffSourceSupported W V hV hR hs K b hb =
      logSourceSupported W (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hs b hb + logErrorSupported W V hW hV hR K s b hb := by
  apply Subtype.ext
  ext z
  exact firstOrderSource_translatedCutoffLog W V R hs b z

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianUniformInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E)
  (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hρ : ContDiff ℝ ∞ ρ) (hV : ContDiff ℝ ∞ V)

include hW hρ in

lemma logShellSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) r, ∀ b ∈ K,
      (∀ z, |logShellSchwartz W a V ha hV hr.1 hs.1 b z| ≤ C/r) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * logShellSchwartz W a V ha hV hr.1 hs.1 b z) z‖ ≤ (C/r)/(5*r)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogShell_derivatives_bounded W a V hW ha hV hK R 0
  choose D hD hb using fun n => shiftedLogShell_derivatives_bounded W a
    (fun w => ρ w • V w) hW ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hbK
  constructor
  · intro z
    have h := hb₀ r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,zero_add,pow_one] at h
    exact h.trans (by simpa using div_le_div_of_nonneg_right hC₀ (show 0 ≤ r from hr.1.le))
  · intro n hn z
    have he : (fun z => ρ z * logShellSchwartz W a V ha hV hr.1 hs.1 b z) =
        shiftedLogShell W a (fun w => ρ w • V w) r s b :=
      funext (shiftedLogShell_weight W a ρ V r s b)
    rw [he]
    have h := hb n r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hr.1) n 1 (hCD n hn)

include hW hρ in

lemma logInnerSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) R, ∀ b ∈ K,
      (∀ z, |logInnerSchwartz W a V ha hV hs.1 b z| ≤ C/s) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * logInnerSchwartz W a V ha hV hs.1 b z) z‖ ≤ (C/s)/(5*s)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogInner_derivatives_bounded W a V hW ha hV hK R 0
  choose D hD hb using fun n => shiftedLogInner_derivatives_bounded W a
    (fun w => ρ w • V w) hW ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,zero_add,pow_one] at h
    exact h.trans (by simpa using div_le_div_of_nonneg_right hC₀ (show 0 ≤ s from hs.1.le))
  · intro n hn z
    have he : (fun z => ρ z * logInnerSchwartz W a V ha hV hs.1 b z) =
        shiftedLogInner W a (fun w => ρ w • V w) s b :=
      funext (shiftedLogInner_weight W a ρ V s b)
    rw [he]
    have h := hb n s hs b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hs.1) n 1 (hCD n hn)

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RadialEnergyDual
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
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma scalarEnergyDualLM_scaled_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) (f : supportedSchwartz K)
      (b : Space) (r M : ℝ), 0 ≤ r → 0 ≤ M →
      tsupport f.val ⊆ Metric.ball b r → (∀ z, |f.val z| ≤ M) →
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j f‖ ≤ C*M*r^3 := by
  obtain ⟨C,hC,hpair⟩ := critical_chart_pairing A J α hs ht D hD p τ hKD hτ
  obtain ⟨C',hC',hscale⟩ := densityTest_scale_bound A J α hs ht D p hK hKD
  refine ⟨C*C',mul_nonneg hC hC',?_⟩
  intro j f b r M hr hM hsupport hval
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hp := hpair f.val (supportedSchwartz_compact hK f) f.property j v
  have hg := hscale f.val (supportedSchwartz_compact hK f) f.property b r M hr hM hsupport hval
  change |⟪smoothL2 A J α hs ht true (scalarTestLM A J α hs ht D p K hK hKD j f).val,
    energyInclusion A J α hs ht v⟫| ≤ _
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hC) (norm_nonneg v)
  exact hp.trans (by nlinarith only [hb])

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_HermitianDualBounds
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (W : Space → Space →L[ℝ] Space) (hW : ContDiff ℝ ∞ W)

include hD hW in

theorem scalarEnergyDual_logSource_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (HermitianRadial.logSourceSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C := by
  obtain ⟨c,hc,hbound⟩ := scalarEnergyDualLM_scaled_bound A J α hs ht D hD p τ K hK hKD hτ
  obtain ⟨E₀,hE₀,hinner⟩ := HermitianRadial.logInnerSchwartz_uniform_inputs W a (fun _ => 1) V hW ha contDiff_const hV hK₀ R 0
  obtain ⟨E₁,hE₁,hshell⟩ := HermitianRadial.logShellSchwartz_uniform_inputs W a (fun _ => 1) V hW ha contDiff_const hV hK₀ R 0
  refine ⟨125*c*(E₀+4*E₁)*R^2,by positivity,?_⟩
  intro j s hsr b hb
  have hs0 : 0 < s := hsr.1
  obtain ⟨N,hN,hN2,hmin⟩ := exists_minimal_dyadic_scale hsr.1 hsr.2
  let L := scalarEnergyDualLM A J α hs ht D p K hK hKD j
  have h₀ : ‖L (HermitianRadial.logInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ 125*c*E₀*s^2 := by
    have h := hbound j (HermitianRadial.logInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))
      b (5*s) (E₀/s) (by positivity) (by positivity)
      ((HermitianRadial.shiftedLogInner_support W a V hsr.1 b).trans
        (Metric.closedBall_subset_ball (by linarith [hsr.1] : 2*s < 5*s)))
      (hinner s hsr b hb).1
    apply h.trans_eq
    field_simp [hsr.1.ne']
    ring
  have h₁ : ∀ k < N,
      ‖L (HermitianRadial.logShellSupported W a V ha hV R haR K (mul_pos hsr.1 (by positivity : 0 < (2:ℝ)^k))
        hsr.1 b (hcenters b hb))‖ ≤ 125*c*E₁*(s*2^k)^2 := by
    intro k hk
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hr0 : 0 < s*2^k := hr.1
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hsr.1,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    have h := hbound j (HermitianRadial.logShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))
      b (5*(s*2^k)) (E₁/(s*2^k)) (by positivity) (by positivity)
      ((HermitianRadial.shiftedLogShell_support W a V hr.1 s b).trans
        (Metric.closedBall_subset_ball (by linarith [hr.1] : 4*(s*2^k) < 5*(s*2^k))))
      (hshell (s*2^k) hr s hsr' b hb).1
    apply h.trans_eq
    field_simp [hr.1.ne']
    ring
  change ‖L _‖ ≤ _
  rw [HermitianRadial.logSupported_reconstruction W a V ha hV R haR K hsr.1 b (hcenters b hb) N hN,map_add,map_sum]
  apply (norm_add_le (L (HermitianRadial.logInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))) _).trans
  apply (add_le_add h₀ ((norm_sum_le (Finset.range N) (fun k => L (HermitianRadial.logShellSupported W a V ha hV R haR K
    (mul_pos hs0 (by positivity : 0 < (2:ℝ)^k)) hs0 b (hcenters b hb)))).trans (Finset.sum_le_sum
    (fun k hk => h₁ k (Finset.mem_range.mp hk))))).trans
  rw [← Finset.mul_sum]
  have hi : s^2 ≤ R^2 := by nlinarith [hsr.1,hsr.2]
  have ht' : (s*2^N)^2 ≤ (2*R)^2 := by nlinarith [hN2,show 0 < s*2^N by positivity]
  have hsum := (sum_dyadic_square_le hsr.1.le N).trans ht'
  calc
    _ ≤ 125*c*E₀*R^2 + 125*c*E₁*(2*R)^2 := by gcongr
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_HermitianCutoffDualBounds
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
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (W : Space → Space →L[ℝ] Space) (hW : ContDiff ℝ ∞ W)

include hD hW in

theorem scalarEnergyDual_logError_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ _hsr : s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (HermitianRadial.logErrorSupported W V hW hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨c,hc,hbound⟩ := scalarEnergyDualLM_scaled_bound A J α hs ht D hD p τ K hK hKD hτ
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.logErrorSchwartz_uniform_inputs W V hW hV hR
    (fun _ => 1) contDiff_const hK₀ S 0
  refine ⟨c*E*(3*R)^3,by positivity,?_⟩
  intro j s hsr b hb
  exact hbound j (HermitianRadial.logErrorSupported W V hW hV hR K s b (hcenters b hb)) b (3*R) E
    (by positivity) hE
    ((HermitianRadial.shiftedLogError_support W V hR s b).trans
      (Metric.closedBall_subset_ball (by linarith : 2*R < 3*R)))
    (hinput s hsr b hb).1

include hD hW in

theorem scalarEnergyDual_cutoffLog_bound_oai
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (HermitianRadial.logCutoffSourceSupported W V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := scalarEnergyDual_logSource_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (scaledCutoff R) V (scaledCutoff_smooth R) hV (2*R)
    (by positivity) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,herror⟩ := scalarEnergyDual_logError_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ V hV R hR (2*R) K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro j s hsr b hb
  rw [HermitianRadial.logCutoffSourceSupported_eq W V hW hV,map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD j
      (HermitianRadial.logSourceSupported W (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hsr.1 b (hcenters b hb))) _).trans
    (add_le_add (hsource j s hsr b hb) (herror j s ⟨hsr.1.le,hsr.2⟩ b hb))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffLog_bound_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffLog_bound_oai.{u_1}
