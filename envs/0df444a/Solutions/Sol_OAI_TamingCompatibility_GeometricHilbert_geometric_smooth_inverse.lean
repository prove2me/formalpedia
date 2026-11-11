-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:37:29.499597+00:00
-- url     : https://prove2.me/submissions/8630c4b3-50c4-43c0-bbd4-94313e619d72

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc029
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_raw_smooth_near

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RawNormal
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma rawScalar_smooth {a : TwoForm X} (ha : IsSmooth a) (j : Fin 4) :
    ContDiffOn ℝ ∞ (rawScalar J α ht p D a j) D.domain := by
  exact FormSmooth.contDiffOn_apply_two ((smooth_chart a ha p).mono D.domain_subset)
    (D.frame_smooth 0) (D.frame_smooth j)

lemma rawPair_smooth {a : TwoForm X} (ha : IsSmooth a) :
    ContDiffOn ℝ ∞ (rawPair J α ht p D a) D.domain := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact rawScalar_smooth J α ht p D ha 2
  · exact rawScalar_smooth J α ht p D ha 3

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartReconstruction
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma manifoldTest_eq {b : TwoForm X} (hb : antiInvariantPart J b = b)
    (q : Space → EuclideanEnergy.Pair) (hqD : tsupport q ⊆ D.domain)
    (hraw : ∀ z ∈ D.domain, q z = rawPair J α ht p D b z)
    (hbzero : ∀ x ∉ (extChartAt Model p).symm '' D.domain, b x = 0) :
    manifoldTest J α ht p D q = b := by
  funext x
  by_cases hx : x ∈ (extChartAt Model p).symm '' D.domain
  · obtain ⟨z,hz,rfl⟩ := hx
    apply form_eq_of_chart_pullback p _ _ ((extChartAt Model p).map_target (D.domain_subset hz))
    rw [(extChartAt Model p).right_inv (D.domain_subset hz)]
    change TamingCompatibility.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z =
      TamingCompatibility.pullback b (extChartAt Model p).symm z
    rw [pullback_manifoldTest J α ht p D hqD (D.domain_subset hz)]
    have he : TamingCompatibility.pullback b (extChartAt Model p).symm z =
        coordinateTest J α ht p D (rawPair J α ht p D b) z :=
      rawScalar_expansion J α ht p D hb hz
    rw [he]
    simp only [coordinateTest,LocalMatrixOperator.frameTest,hraw z hz]
  · rw [hbzero x hx,manifoldTest_zero_off J α ht p D q]
    exact fun h => hx ((image_mono hqD) h)
end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_ChartGarding
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
namespace TamingCompatibility.EuclideanEnergy
open _root_.MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma norm_smul_sq_bound (s : ℝ) (u : F) {C : ℝ} (_hC : 0 ≤ C) (hu : ‖u‖ ≤ C) :
    ‖s • u‖^2 ≤ C^2*s^2 := by
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) hu 2) (sq_nonneg s)).trans_eq (mul_comm _ _)

lemma two_frame_norm_bound {P Q u : V → F} {C : ℝ} (hC : 0 ≤ C)
    (s t : S) (he : u = fun x => s x • P x + t x • Q x)
    {x : V} (hP : ‖P x‖ ≤ C) (hQ : ‖Q x‖ ≤ C) :
    ‖u x‖^2 ≤ 2*C^2*((s x)^2+(t x)^2) := by
  rw [he]
  have h := norm_add_sq_bound (s x • P x) (t x • Q x)
  have h₁ := norm_smul_sq_bound (s x) (P x) hC hP
  have h₂ := norm_smul_sq_bound (t x) (Q x) hC hQ
  nlinarith

lemma two_frame_deriv_bound {P Q u : V → F} {C : ℝ} (hC : 0 ≤ C)
    (s t : S) (he : u = fun x => s x • P x + t x • Q x)
    {x : V} (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x)
    (hbP : ‖P x‖ ≤ C) (hbQ : ‖Q x‖ ≤ C)
    (hdP : ‖fderiv ℝ P x‖ ≤ C) (hdQ : ‖fderiv ℝ Q x‖ ≤ C) (i : Fin 4) :
    ‖fderiv ℝ u x (e i)‖^2 ≤ 8*C^2*(gradientEnergy s t x + (s x)^2+(t x)^2) := by
  have hs := (s.smooth 1).differentiable (by norm_num) x
  have ht := (t.smooth 1).differentiable (by norm_num) x
  have hder : fderiv ℝ u x (e i) =
      coordinateDeriv i s x • P x + s x • fderiv ℝ P x (e i) +
        (coordinateDeriv i t x • Q x + t x • fderiv ℝ Q x (e i)) := by
    rw [he]
    change (fderiv ℝ (⇑s • P + ⇑t • Q) x) (e i) = _
    rw [fderiv_add (hs.smul hP) (ht.smul hQ),fderiv_smul hs hP,fderiv_smul ht hQ]
    simp only [add_apply,ContinuousLinearMap.smulRight_apply,
      smul_apply,coordinateDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv]
    abel
  have heN : ‖e i‖ = 1 := by simp [e]
  have hdp : ‖fderiv ℝ P x (e i)‖ ≤ C := by
    simpa only [heN,mul_one] using (fderiv ℝ P x).le_opNorm (e i) |>.trans
      (mul_le_mul_of_nonneg_right hdP (norm_nonneg (e i)))
  have hdq : ‖fderiv ℝ Q x (e i)‖ ≤ C := by
    simpa only [heN,mul_one] using (fderiv ℝ Q x).le_opNorm (e i) |>.trans
      (mul_le_mul_of_nonneg_right hdQ (norm_nonneg (e i)))
  have hp := norm_add_sq_bound (coordinateDeriv i s x • P x) (s x • fderiv ℝ P x (e i))
  have hq := norm_add_sq_bound (coordinateDeriv i t x • Q x) (t x • fderiv ℝ Q x (e i))
  have hp₁ := norm_smul_sq_bound (coordinateDeriv i s x) (P x) hC hbP
  have hp₂ := norm_smul_sq_bound (s x) (fderiv ℝ P x (e i)) hC hdp
  have hq₁ := norm_smul_sq_bound (coordinateDeriv i t x) (Q x) hC hbQ
  have hq₂ := norm_smul_sq_bound (t x) (fderiv ℝ Q x (e i)) hC hdq
  have hg : (coordinateDeriv i s x)^2+(coordinateDeriv i t x)^2 ≤ gradientEnergy s t x := by
    unfold gradientEnergy
    exact Finset.single_le_sum (fun j _ => add_nonneg (sq_nonneg (coordinateDeriv j s x)) (sq_nonneg (coordinateDeriv j t x))) (Finset.mem_univ i)
  have hg' := mul_le_mul_of_nonneg_left hg (sq_nonneg C)
  have hn := norm_add_sq_bound (coordinateDeriv i s x • P x + s x • fderiv ℝ P x (e i))
    (coordinateDeriv i t x • Q x + t x • fderiv ℝ Q x (e i))
  rw [hder]
  have hg0 : 0 ≤ gradientEnergy s t x := Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc₁ := mul_nonneg (sq_nonneg C) (sq_nonneg (s x))
  have hc₂ := mul_nonneg (sq_nonneg C) (sq_nonneg (t x))
  have hc₃ := mul_nonneg (sq_nonneg C) hg0
  nlinarith
end TamingCompatibility.EuclideanEnergy

namespace TamingCompatibility.EuclideanEnergy
open _root_.MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem frame_h1_bound {U K : Set V} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (P Q : V → F) (hP : ContDiffOn ℝ ∞ P U) (hQ : ContDiffOn ℝ ∞ Q U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : S) (u : 𝓢(V,F)), tsupport u ⊆ K →
      (⇑u = fun x => s x • P x + t x • Q x) →
      ((∫ x, ‖u x‖^2) ≤ C*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2))) ∧
      (∀ i : Fin 4, (∫ x, ‖(∂_{e i} u) x‖^2) ≤
        C*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2))) := by
  have hdP : ContinuousOn (fderiv ℝ P) K := fun x hx =>
    ((hP.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousWithinAt
  have hdQ : ContinuousOn (fderiv ℝ Q) K := fun x hx =>
    ((hQ.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousWithinAt
  obtain ⟨B₁,h₁⟩ := hK.exists_bound_of_continuousOn (hP.continuousOn.mono hKU)
  obtain ⟨B₂,h₂⟩ := hK.exists_bound_of_continuousOn (hQ.continuousOn.mono hKU)
  obtain ⟨B₃,h₃⟩ := hK.exists_bound_of_continuousOn hdP
  obtain ⟨B₄,h₄⟩ := hK.exists_bound_of_continuousOn hdQ
  let B := max 1 (max B₁ (max B₂ (max B₃ B₄)))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb₁ : B₁ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hb₂ : B₂ ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hb₃ : B₃ ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hb₄ : B₄ ≤ B := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨8*B^2,by positivity,?_⟩
  intro s t u hsu he
  have hg (x : V) : 0 ≤ gradientEnergy s t x :=
    Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hint : Integrable (fun x => 8*B^2*(gradientEnergy s t x+(s x)^2+(t x)^2)) :=
    (((gradientEnergy_integrable s t).add (schwartz_sq_integrable s)).add (schwartz_sq_integrable t)).const_mul _
  have hformula : (∫ x, 8*B^2*(gradientEnergy s t x+(s x)^2+(t x)^2)) =
      8*B^2*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2)) := by
    rw [integral_const_mul]
    congr 1
    calc (∫ x, gradientEnergy s t x+(s x)^2+(t x)^2) =
        ∫ x, gradientEnergy s t x+((s x)^2+(t x)^2) := by
          congr 1; funext x; ring
      _ = _ := integral_add (gradientEnergy_integrable s t)
        ((schwartz_sq_integrable s).add (schwartz_sq_integrable t))
  constructor
  · refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint
      (Filter.Eventually.of_forall (fun x => ?_))).trans_eq hformula
    by_cases hx : x ∈ K
    · have h := two_frame_norm_bound hB.le s t he ((h₁ x hx).trans hb₁) ((h₂ x hx).trans hb₂)
      have hgn := mul_nonneg (sq_nonneg B) (hg x)
      have hsn := mul_nonneg (sq_nonneg B) (sq_nonneg (s x))
      have htn := mul_nonneg (sq_nonneg B) (sq_nonneg (t x))
      nlinarith
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsu h)),norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (by positivity) (add_nonneg (add_nonneg (hg x) (sq_nonneg _)) (sq_nonneg _))
  · intro i
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint
      (Filter.Eventually.of_forall (fun x => ?_))).trans_eq hformula
    by_cases hx : x ∈ K
    · rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact two_frame_deriv_bound hB.le s t he
        ((hP.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        ((hQ.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        ((h₁ x hx).trans hb₁) ((h₂ x hx).trans hb₂) ((h₃ x hx).trans hb₃) ((h₄ x hx).trans hb₄) i
    · rw [image_eq_zero_of_notMem_tsupport
        (fun h => hx (hsu (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))),norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (by positivity) (add_nonneg (add_nonneg (hg x) (sq_nonneg _)) (sq_nonneg _))
end TamingCompatibility.EuclideanEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DirectionH1
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume LocalMatrixOperator EuclideanEnergy
open Set _root_.MeasureTheory AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hs hD in
omit [T2Space X] in

theorem localized_jet_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : smoothForms X 2, antiInvariantPart J a.val = a.val →
      ∀ j : DerivativeIndex, ‖localizeH1 A 2 a j p‖^2 ≤
        C * ((∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) +
          (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
            (codifferential J α ht a.val) x ∂geometricVolume A J α)) := by
  let P : Space → CoordinateFiber 2 := fun x => formCoordinates 2
    (realPart (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x))
  let Q : Space → CoordinateFiber 2 := fun x => formCoordinates 2
    (imagPart (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x))
  have hg := (coordinateMetric_smooth J α hs ht p.val).mono (D p).domain_subset
  have hP : ContDiffOn ℝ ∞ P (D p).domain :=
    ContDiffOn.continuousLinearMap_comp (formCoordinates 2) (realPart_smooth hg (D p).frame_smooth)
  have hQ : ContDiffOn ℝ ∞ Q (D p).domain :=
    ContDiffOn.continuousLinearMap_comp (formCoordinates 2) (imagPart_smooth hg (D p).frame_smooth)
  obtain ⟨C,hC,hframe⟩ := frame_h1_bound (D p).domain_open (coordinateSupport_compact A p)
    (coordinateSupport_domain A J α ht D hD p) P Q hP hQ
  obtain ⟨K,hK,hgard⟩ := scalar_garding A J α hs ht D hD p
  refine ⟨16*(C*K),mul_pos (by norm_num) (mul_pos hC hK),?_⟩
  intro a hanti j
  let s := scalarSchwartz A J α ht D hD p a.val a.property 2
  let t := scalarSchwartz A J α ht D hD p a.val a.property 3
  have he : (⇑(localizedLinear A 2 p a)) = fun x => s x • P x + t x • Q x := by
    funext x
    change formCoordinates 2 (localizedFunction A p a.val x) = _
    rw [scalar_expansion A J α ht D hD p hanti x,map_add,map_smul,map_smul]
    rfl
  have hb := hframe s t (localizedLinear A 2 p a) (localizedLinear_support A p a) he
  have hga := hgard a.val a.property hanti
  rw [localizeH1_apply,schwartz_l2_norm_sq]
  have hbound : C*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2)) ≤
      C*K*((∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) +
          (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
            (codifferential J α ht a.val) x ∂geometricVolume A J α)) := by
    exact (mul_le_mul_of_nonneg_left hga hC.le).trans_eq (mul_assoc _ _ _).symm
  have hnonneg : 0 ≤ C*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2)) :=
    (integral_nonneg fun x => sq_nonneg ‖localizedLinear A 2 p a x‖).trans hb.1
  have htarget := mul_le_mul_of_nonneg_left hbound (show (0:ℝ) ≤ 16 by norm_num)
  cases j with
  | none => exact (hb.1.trans (by nlinarith : _ ≤ 16*(C*((∫ x, gradientEnergy s t x)+
        (∫ x, (s x)^2+(t x)^2))))).trans (by simpa only [mul_assoc] using htarget)
  | some i =>
    change (∫ x, ‖(∂_{stdOrthonormalBasis ℝ Space i} (localizedLinear A 2 p a)) x‖^2) ≤ _
    have hv : ‖stdOrthonormalBasis ℝ Space i‖ ≤ 1 := le_of_eq
      ((stdOrthonormalBasis ℝ Space).orthonormal.norm_eq_one i)
    have hd := direction_integral_bound (localizedLinear A 2 p a)
      (stdOrthonormalBasis ℝ Space i) hv
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb.2 k)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_ofNat] at hsum
    exact (hd.trans (by nlinarith : _ ≤ 16*(C*((∫ x, gradientEnergy s t x)+
        (∫ x, (s x)^2+(t x)^2))))).trans (by simpa only [mul_assoc] using htarget)
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_AntiChartH1
attribute [-instance] _root_.OAI.TamingCompatibility.Fredholm.instCompleteSpaceSubtypeMemSubmoduleRealNullspace _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma antiToH1_bound : ∃ C : ℝ, ∀ a : antiPre A J α hs ht,
    ‖antiToH1 A J α hs ht a‖ ≤ C * ‖antiToEnergy A J α hs ht a‖ := by
  classical
  choose C hC hb using localized_jet_bound A J α hs ht D hD
  let B : ℝ := 1 + ∑ p : A.centers, C p
  have hB : 0 < B := by
    have hsum : 0 ≤ ∑ p : A.centers, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hcB (p : A.centers) : C p ≤ B :=
    (Finset.single_le_sum (fun p _ => (hC p).le) (Finset.mem_univ p)).trans
      (by change (∑ p : A.centers, C p) ≤ 1 + (∑ p : A.centers, C p); linarith)
  let N : ℝ := Fintype.card DerivativeIndex * Fintype.card A.centers
  have hN : 0 ≤ N := by dsimp [N] <;> positivity
  refine ⟨Real.sqrt (N*B),fun a => ?_⟩
  have hsq : ‖antiToH1 A J α hs ht a‖^2 ≤ N*B*‖antiToEnergy A J α hs ht a‖^2 := by
    change ‖localizeH1 A 2 a.val‖^2 ≤ N*B*‖antiGraph A J α hs ht a‖^2
    simp only [PiLp.norm_sq_eq_of_L2]
    have hlocal (j : DerivativeIndex) (p : A.centers) :
        ‖localizeH1 A 2 a.val j p‖^2 ≤ B*‖antiGraph A J α hs ht a‖^2 := by
      have h := hb p a.val a.property j
      rw [← antiGraph_norm_sq A J α hs ht a] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hcB p) (sq_nonneg _))
    calc
      _ ≤ ∑ j : DerivativeIndex, ∑ p : A.centers, B*‖antiGraph A J α hs ht a‖^2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun p _ => hlocal j p
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [N] <;> ring
  have hroot : (Real.sqrt (N*B)*‖antiToEnergy A J α hs ht a‖)^2 =
      N*B*‖antiToEnergy A J α hs ht a‖^2 := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hN hB.le)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp (hsq.trans_eq hroot.symm)

include hD in
lemma energyToH1_smooth (a : antiPre A J α hs ht) :
    energyToH1 A J α hs ht (antiToEnergy A J α hs ht a) = antiToH1 A J α hs ht a :=
  LinearMap.extendOfNorm_eq (antiToEnergy_dense A J α hs ht) (antiToH1_bound A J α hs ht D hD) a
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiEnergyWeak
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma antiGraph_weak (a : antiPre A J α hs ht) (b : PreL2 A J α hs ht false) :
    inner ℝ (testDerivative A J α hs ht b) (antiGraph A J α hs ht a).fst =
      inner ℝ (smoothL2 A J α hs ht false b) (antiGraph A J α hs ht a).snd := by
  let db : PreL2 A J α hs ht true := ⟨exteriorDerivative b.val,b.property.exteriorDerivative⟩
  have h := GeometricAdjoint.formal_adjoint A J α hs ht b.property a.val.property
  have he : l2Pairing A J α ht db a.val = l2Pairing A J α ht b (antiDelta A J α hs ht a) := h
  exact ((smoothL2 A J α hs ht true).inner_map_map db a.val).trans
    ((preL2_inner A J α hs ht true db a.val).trans (he.trans
      (((smoothL2 A J α hs ht false).inner_map_map b (antiDelta A J α hs ht a)).trans
        (preL2_inner A J α hs ht false b (antiDelta A J α hs ht a))).symm))

lemma antiEnergy_weak (u : antiEnergy A J α hs ht) (b : PreL2 A J α hs ht false) :
    inner ℝ (testDerivative A J α hs ht b) u.val.fst =
      inner ℝ (smoothL2 A J α hs ht false b) u.val.snd := by
  let S : Set (WithLp 2 (L2 A J α hs ht true × L2 A J α hs ht false)) :=
    {v | inner ℝ (testDerivative A J α hs ht b) v.fst =
      inner ℝ (smoothL2 A J α hs ht false b) v.snd}
  have hc : _root_.IsClosed S := isClosed_eq
    (continuous_const.inner (WithLp.fstL 2 ℝ _ _).continuous)
    (continuous_const.inner (WithLp.sndL 2 ℝ _ _).continuous)
  have hr : (LinearMap.range (antiGraph A J α hs ht) : Set _) ⊆ S := by
    rintro _ ⟨a,rfl⟩
    exact antiGraph_weak A J α hs ht a b
  exact (closure_minimal hr hc) u.property

lemma antiEnergy_fst_injective : Function.Injective
    (fun u : antiEnergy A J α hs ht => u.val.fst) := by
  suffices hz : ∀ u : antiEnergy A J α hs ht, u.val.fst = 0 → u = 0 by
    intro u v huv
    have he : u-v=0 := hz (u-v) (by change u.val.fst - v.val.fst = 0; exact sub_eq_zero.mpr huv)
    exact sub_eq_zero.mp he
  intro u hu
  have htest (b : PreL2 A J α hs ht false) :
      inner ℝ (smoothL2 A J α hs ht false b) u.val.snd = 0 := by
    rw [← antiEnergy_weak A J α hs ht u b,hu,inner_zero_right]
  have hall : ∀ v : L2 A J α hs ht false, inner ℝ v u.val.snd = 0 := by
    intro v
    exact (smoothL2_dense A J α hs ht false).induction_on v
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) htest
  have hz : u.val.snd = 0 := inner_self_eq_zero.mp (hall u.val.snd)
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℝ (L2 A J α hs ht true × L2 A J α hs ht false)).injective
  exact Prod.ext hu hz
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricCompact
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma energyInclusion_injective : Function.Injective (energyInclusion A J α hs ht) :=
  antiEnergy_fst_injective A J α hs ht

include hD in
lemma energyInclusion_factor : energyInclusion A J α hs ht =
    chartToMetric A J α hs ht ∘L h1ToL2 A 2 ∘L energyToH1 A J α hs ht := by
  apply DFunLike.coe_injective
  apply (antiToEnergy_dense A J α hs ht).equalizer
    (energyInclusion A J α hs ht).continuous
    (chartToMetric A J α hs ht ∘L h1ToL2 A 2 ∘L energyToH1 A J α hs ht).continuous
  funext a
  change smoothL2 A J α hs ht true a.val =
    chartToMetric A J α hs ht (h1ToL2 A 2 (energyToH1 A J α hs ht (antiToEnergy A J α hs ht a)))
  rw [energyToH1_smooth A J α hs ht D hD]
  exact (chartToMetric_smooth A J α hs ht D hD a.val).symm

include hD in

theorem energyInclusion_compact : IsCompactOperator (energyInclusion A J α hs ht) := by
  rw [energyInclusion_factor A J α hs ht D hD]
  exact ((h1ToL2_compact A 2).comp_clm (energyToH1 A J α hs ht)).clm_comp
    (chartToMetric A J α hs ht)

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

lemma raw_component_pair (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) (u : antiEnergy A J α hs ht) :
    (rawDistribution A J α hs ht D hD p τ u
      (SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD)))) j =
    (⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD))
  let v := testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))
  have hLc : Continuous (fun w => (rawDistribution A J α hs ht D hD p τ w ψ) j) := by
    generalize rawDistribution A J α hs ht D hD p τ = L
    exact (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp
      ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) (C 2) ψ).continuous.comp L.continuous)
  have hRc : Continuous (fun w => (⟪energyInclusion A J α hs ht w,
      energyInclusion A J α hs ht (antiToEnergy A J α hs ht v)⟫ : ℂ)) :=
    Complex.continuous_ofReal.comp ((energyInclusion A J α hs ht).continuous.inner continuous_const)
  exact (antiToEnergy_dense A J α hs ht).induction_on u (isClosed_eq hLc hRc)
    (fun w => smooth_raw_component_pair A J α hs ht D hD p τ hUD hτ φ hc hφU j w)

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalSmoothPairing
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma local_pairing_eq (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (u : antiEnergy A J α hs ht) (g : Space →ᵇ C 2)
    (hg : ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ U →
      rawDistribution A J α hs ht D hD p τ u χ = EuclideanSobolev.boundedDistribution g χ)
    (w : antiPre A J α hs ht) (hw : ∀ z ∈ U,
      rawPair J α ht p.val (D p) w.val.val z = retract 2 (g z))
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) :
    ⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ =
    ⟪smoothL2 A J α hs ht true w.val,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ := by
  let θ := densityTest A J α hs ht D p φ hc (hφU.trans hUD)
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM θ
  have hθ : tsupport θ ⊆ tsupport φ := densityTest_support A J α hs ht D p φ hc (hφU.trans hUD)
  have hψ : tsupport ψ ⊆ tsupport θ := tsupport_comp_subset (map_zero Complex.ofRealCLM) θ
  have he := hg ψ (hc.of_isClosed_subset (isClosed_tsupport ψ) (hψ.trans hθ))
    (hψ.trans (hθ.trans hφU))
  have hp := raw_component_pair A J α hs ht D hD p τ hUD hτ φ hc hφU j u
  change (rawDistribution A J α hs ht D hD p τ u ψ) j = _ at hp
  rw [he] at hp
  have hr := congrArg Complex.re hp
  rw [bounded_real_component,Complex.ofReal_re] at hr
  rw [← hr,smooth_energy_pair]
  change _ = ∫ x, GeometricAdjoint.pairing J α ht w.val.val
    (manifoldTest J α ht p.val (D p) (componentTest j φ)) x ∂geometricVolume A J α
  rw [pairing_manifoldTest_integral J α ht p.val (D p) A hs w.val.property w.property
    ((componentTest j φ).smooth ⊤) (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  change (φ z * (2*chartDensity J α p.val z)) * (g z j).re = _
  by_cases hz : z ∈ tsupport φ
  · have hzraw := congrArg (fun v : EuclideanEnergy.Pair => v j) (hw z (hφU hz))
    rw [← retract_apply 2 (g z) j,← hzraw]
    fin_cases j <;> simp [rawPair,EuclideanEnergy.pair,componentTest_apply] <;> ring
  · simp [image_eq_zero_of_notMem_tsupport hz,componentTest_apply]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiSmoothMultiply
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma rawPair_fun_smul (ρ : X → ℝ) (a : TwoForm X) (z : Space) :
    rawPair J α ht p D (fun x => ρ x • a x) z =
      ρ ((extChartAt Model p).symm z) • rawPair J α ht p D a z := by
  ext j
  fin_cases j <;> rfl
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)

lemma supported_anti_test (p : A.centers) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (hρU : ∀ x ∈ tsupport ρ, x ∈ (extChartAt Model p.val).source ∧ extChartAt Model p.val x ∈ U)
    (a : antiPre A J α hs ht) :
    ∃ q : 𝓢(Space,EuclideanEnergy.Pair), ∃ hc : HasCompactSupport (q : Space → EuclideanEnergy.Pair),
      ∃ hqU : tsupport q ⊆ U,
        testAnti A J α hs ht D p q hc (hqU.trans hUD) = antiMultiply A J α hs ht ρ hρ a := by
  let K := (extChartAt Model p.val) '' tsupport ρ
  have hK : IsCompact K := (isClosed_tsupport ρ).isCompact.image_of_continuousOn
    ((continuousOn_extChartAt p.val).mono (fun x hx => (hρU x hx).1))
  have hKU : K ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact (hρU x hx).2
  obtain ⟨η,hηc,hηU,hηone⟩ := SchwartzCutoff.exists_one_on_compact hK hU hKU
  let b := antiMultiply A J α hs ht ρ hρ a
  let q := SchwartzCutoff.schwartz (D p).domain_open (rawPair_smooth J α ht p.val (D p) b.val.property)
    (η.smooth ⊤) hηc (hηU.trans hUD)
  have hqc : HasCompactSupport (q : Space → EuclideanEnergy.Pair) := SchwartzCutoff.compact hηc
  have hqU : tsupport q ⊆ U := (tsupport_smul_subset_left _ _).trans hηU
  refine ⟨q,hqc,hqU,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change manifoldTest J α ht p.val (D p) q = b.val.val
  apply manifoldTest_eq J α ht p.val (D p) b.property q (hqU.trans hUD)
  · intro z hz
    change η z • rawPair J α ht p.val (D p) (fun x => ρ x • a.val.val x) z =
      rawPair J α ht p.val (D p) (fun x => ρ x • a.val.val x) z
    rw [rawPair_fun_smul]
    by_cases hr : ρ ((extChartAt Model p.val).symm z) = 0
    · change ρ ((chartAt Space p.val).symm z) = 0 at hr
      simp [hr]
    · rw [hηone z ⟨(extChartAt Model p.val).symm z,subset_closure hr,
        (extChartAt Model p.val).right_inv ((D p).domain_subset hz)⟩,one_smul]
  · intro x hx
    change ρ x • a.val.val x = 0
    have hz : ρ x = 0 := by
      by_contra hn
      have hh := hρU x (subset_closure hn)
      exact hx ⟨extChartAt Model p.val x,hUD hh.2,(extChartAt Model p.val).left_inv hh.1⟩
    rw [hz,zero_smul]

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TestLinear
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

namespace TamingCompatibility.ComplexMatrix
open Set
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma pair_decompose (q : 𝓢(E,R 2)) :
    (q : E → R 2) = componentTest (0 : Fin 2) (realComponent q 0) + componentTest (1 : Fin 2) (realComponent q 1) := by
  ext x j
  fin_cases j <;> simp [componentTest_apply,EuclideanSpace.single]
end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)

lemma pair_all_tests_eq (p : A.centers) {U : Set Space} (hUD : U ⊆ (D p).domain)
    (u v : L2 A J α hs ht true)
    (h : ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
      (hφU : tsupport φ ⊆ U) (j : Fin 2),
      ⟪u,smoothL2 A J α hs ht true
        (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
          ((componentTest_support j φ).trans (hφU.trans hUD))).val⟫ =
      ⟪v,smoothL2 A J α hs ht true
        (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
          ((componentTest_support j φ).trans (hφU.trans hUD))).val⟫)
    (q : 𝓢(Space,EuclideanEnergy.Pair)) (hc : HasCompactSupport (q : Space → EuclideanEnergy.Pair))
    (hqU : tsupport q ⊆ U) :
    ⟪u,smoothL2 A J α hs ht true (testAnti A J α hs ht D p q hc (hqU.trans hUD)).val⟫ =
    ⟪v,smoothL2 A J α hs ht true (testAnti A J α hs ht D p q hc (hqU.trans hUD)).val⟫ := by
  let φ (j : Fin 2) := realComponent q j
  have hφc (j : Fin 2) : HasCompactSupport (φ j : Space → ℝ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (realComponent_support q j)
  have hφU (j : Fin 2) : tsupport (φ j) ⊆ U := (realComponent_support q j).trans hqU
  let w (j : Fin 2) := testAnti A J α hs ht D p (componentTest j (φ j))
    (componentTest_compact j (φ j) (hφc j)) ((componentTest_support j (φ j)).trans ((hφU j).trans hUD))
  have he : testAnti A J α hs ht D p q hc (hqU.trans hUD) = w 0 + w 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p) q =
      manifoldTest J α ht p.val (D p) (componentTest 0 (φ 0)) +
      manifoldTest J α ht p.val (D p) (componentTest 1 (φ 1))
    rw [← manifoldTest_add]
    exact congrArg (manifoldTest J α ht p.val (D p)) (pair_decompose q)
  rw [he]
  change ⟪u,smoothL2 A J α hs ht true ((w 0).val + (w 1).val)⟫ =
    ⟪v,smoothL2 A J α hs ht true ((w 0).val + (w 1).val)⟫
  rw [map_add,inner_add_right,inner_add_right]
  exact congrArg₂ (·+·) (h (φ 0) (hφc 0) (hφU 0) 0) (h (φ 1) (hφc 1) (hφU 1) 1)

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_LocalPatchConstruction
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_patch (p : A.centers) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    {z : Space} (hz : z ∈ U) (g : Space →ᵇ C 2) (hg : ContDiff ℝ ∞ (g : Space → C 2)) :
    ∃ W : Set Space, IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧ ∃ w : antiPre A J α hs ht,
      ∀ y ∈ W, rawPair J α ht p.val (D p) w.val.val y = retract 2 (g y) := by
  obtain ⟨η,hc,hηU,W,hW,hzW,hWU,hη⟩ := SchwartzCutoff.exists_one_near hU hz
  let q : Space → EuclideanEnergy.Pair := fun y => η y • retract 2 (g y)
  have hq : ContDiff ℝ ∞ q := (η.smooth ⊤).smul ((retract 2).contDiff.comp hg)
  have hqs : tsupport q ⊆ tsupport η := tsupport_smul_subset_left _ _
  have hqc : HasCompactSupport q := hc.of_isClosed_subset (isClosed_tsupport q) hqs
  let ψ := hqc.toSchwartzMap hq
  let w := testAnti A J α hs ht D p ψ hqc (hqs.trans (hηU.trans hUD))
  refine ⟨W,hW,hzW,hWU,w,fun y hy => ?_⟩
  change rawPair J α ht p.val (D p) (manifoldTest J α ht p.val (D p) q) y = _
  rw [rawPair_manifoldTest J α ht p.val (D p) (hqs.trans (hηU.trans hUD)) (hUD (hWU hy))]
  change η y • retract 2 (g y) = _
  rw [hη y hy,one_smul]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalWeakPatch
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma exists_weak_patch (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ w : antiPre A J α hs ht,
      ∀ (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ), tsupport ρ ⊆ V →
        ∀ a : antiPre A J α hs ht,
          ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ =
          ⟪smoothL2 A J α hs ht true w.val,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht D hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,U,hU,hxU,hUD,hτ,g,hgs,hgd⟩ := raw_smooth_near A J α hs ht D hD p
    (extChartAt Model p.val x) hxp hw f u heq
  obtain ⟨W,hW,hxW,hWU,w,hw⟩ := exists_patch A J α hs ht D p hU hUD hxU g hgs
  let V := (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' W
  have hV : IsOpen V := (continuousOn_extChartAt p.val).isOpen_inter_preimage (isOpen_extChartAt_source p.val) hW
  refine ⟨V,hV,⟨hxs,hxW⟩,w,fun ρ hρ hρV a => ?_⟩
  obtain ⟨q,hqc,hqW,hq⟩ := supported_anti_test A J α hs ht D p hW (hWU.trans hUD) ρ hρ hρV a
  rw [← hq]
  refine pair_all_tests_eq A J α hs ht D p (hWU.trans hUD) _ _ ?_ q hqc hqW
  intro φ hc hφW j
  exact local_pairing_eq A J α hs ht D hD p τ (hWU.trans hUD)
    (fun z hz => hτ z (hWU hz)) u g (fun χ hc hχ => hgd χ hc (hχ.trans hWU))
    w hw φ hc hφW j

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_VariationalResolvent
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped RealInnerProductSpace

namespace TamingCompatibility.Fredholm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in

theorem finiteDimensional_nullspace (K : H →L[ℝ] H) (hK : IsCompactOperator K) :
    FiniteDimensional ℝ (nullspace K) := by
  have hinv : ∀ x ∈ nullspace K, K.toLinearMap x ∈ nullspace K := by
    intro x hx
    simpa only [ContinuousLinearMap.coe_coe, (mem_nullspace K x).mp hx] using hx
  have hc := hK.restrict hinv (1 - K).isClosed_ker
  have heq : K.toLinearMap.restrict hinv = LinearMap.id := by
    ext x
    exact (mem_nullspace K x).mp x.2
  rw [heq] at hc
  exact isCompactOperator_id_iff_finiteDimensional.mp hc

theorem exists_inverse_on_complement (K : H →L[ℝ] H)
    (hK : IsCompactOperator K) (hs : K.toLinearMap.IsSymmetric) :
    ∃ U : ((nullspace K)ᗮ →L[ℝ] (nullspace K)ᗮ),
      (1 - K.restrict (map_orthogonal_nullspace K hs)) * U = 1 ∧
      U * (1 - K.restrict (map_orthogonal_nullspace K hs)) = 1 := by
  let V := (nullspace K)ᗮ
  let A : V →L[ℝ] V := K.restrict (map_orthogonal_nullspace K hs)
  have hAc : IsCompactOperator A :=
    hK.restrict (map_orthogonal_nullspace K hs) (nullspace K).isClosed_orthogonal
  have hne : ¬ Module.End.HasEigenvalue A.toLinearMap 1 := by
    intro he
    obtain ⟨x, hx⟩ := he.exists_hasEigenvector
    have hxx : K (x : H) = x := by
      have ht := congrArg (fun v : V => (v : H)) hx.apply_eq_smul
      change K (x : H) = (1 : ℝ) • (x : H) at ht
      simpa only [one_smul] using ht
    have hxN : (x : H) ∈ nullspace K := (mem_nullspace K x).mpr hxx
    have hzero : (x : H) = 0 := by
      have hi := (Submodule.mem_orthogonal (nullspace K) x).mp x.2 x hxN
      exact inner_self_eq_zero.mp hi
    exact hx.2 (Subtype.ext hzero)
  have hr : (1 : ℝ) ∈ resolventSet ℝ A :=
    (hAc.hasEigenvalue_or_mem_resolventSet one_ne_zero).resolve_left hne
  have hu : IsUnit (1 - A) := by
    simpa only [spectrum.mem_resolventSet_iff, map_one] using hr
  obtain ⟨u, hu⟩ := hu
  refine ⟨↑u⁻¹, ?_, ?_⟩
  · change (1 - A) * ↑u⁻¹ = 1
    rw [← hu]
    exact u.val_inv
  · change ↑u⁻¹ * (1 - A) = 1
    rw [← hu]
    exact u.inv_val

theorem exists_generalized_inverse (K : H →L[ℝ] H)
    (hK : IsCompactOperator K) (hs : K.toLinearMap.IsSymmetric) :
    ∃ G : H →L[ℝ] H,
      (1 - K) * G = 1 - (nullspace K).starProjection ∧
      G * (1 - K) = 1 - (nullspace K).starProjection ∧
      (∀ x, G x ∈ (nullspace K)ᗮ) ∧
      (∀ x ∈ nullspace K, G x = 0) := by
  obtain ⟨U, hU, hU'⟩ := exists_inverse_on_complement K hK hs
  let N := nullspace K
  let V := Nᗮ
  let A : V →L[ℝ] V := K.restrict (map_orthogonal_nullspace K hs)
  let G : H →L[ℝ] H := V.subtypeL ∘L U ∘L V.orthogonalProjectionOnto
  have hGmem (x : H) : G x ∈ V := (U (V.orthogonalProjectionOnto x)).2
  have hleft (x : H) : (1 - K) (G x) = V.starProjection x := by
    have hv := congrArg (fun T : V →L[ℝ] V => (T (V.orthogonalProjectionOnto x) : H)) hU
    change (U (V.orthogonalProjectionOnto x) : H) -
      K (U (V.orthogonalProjectionOnto x) : H) = (V.orthogonalProjectionOnto x : H) at hv
    exact hv
  have hGzero (x : H) (hx : x ∈ N) : G x = 0 := by
    have hz : V.orthogonalProjectionOnto x = 0 :=
      V.orthogonalProjectionOnto_apply_of_mem_orthogonal (N.le_orthogonal_orthogonal hx)
    change (U (V.orthogonalProjectionOnto x) : H) = 0
    rw [hz, map_zero]
    rfl
  have hTmem (x : H) : (1 - K) x ∈ V := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    change ⟪y, x - K x⟫ = 0
    rw [inner_sub_right]
    have hxy : ⟪y, K x⟫ = ⟪y, x⟫ := by
      change ⟪y, K.toLinearMap x⟫ = _
      rw [← hs y x]
      change ⟪K y, x⟫ = _
      rw [(mem_nullspace K y).mp hy]
    rw [hxy, sub_self]
  have hTproj (x : H) : (1 - K) (V.starProjection x) = (1 - K) x := by
    rw [N.starProjection_orthogonal_val, map_sub]
    have hz : (1 - K) (N.starProjection x) = 0 := (N.orthogonalProjectionOnto x).2
    rw [hz, sub_zero]
  have hright (x : H) : G ((1 - K) x) = V.starProjection x := by
    let y := G ((1 - K) x) - V.starProjection x
    have hyV : y ∈ V := V.sub_mem (hGmem _) (V.orthogonalProjectionOnto x).2
    have hyN : y ∈ N := by
      show (1 - K) y = 0
      rw [map_sub, hleft, hTproj,
        V.starProjection_eq_self_iff.mpr (hTmem x), sub_self]
    have hi := (Submodule.mem_orthogonal N y).mp hyV y hyN
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hi)
  refine ⟨G, ?_, ?_, hGmem, hGzero⟩
  · ext x
    change (1 - K) (G x) = x - N.starProjection x
    rw [hleft, N.starProjection_orthogonal_val]
  · ext x
    change G ((1 - K) x) = x - N.starProjection x
    rw [hright, N.starProjection_orthogonal_val]

end TamingCompatibility.Fredholm

namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma resolvent_compact (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (hi : IsCompactOperator i) :
    IsCompactOperator (resolvent i D hc) := hi.comp_clm _

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

theorem exists_energy_inverse (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (hi : IsCompactOperator i) :
    let N := Fredholm.nullspace (resolvent i D hc)
    FiniteDimensional ℝ N ∧ ∃ G : H →L[ℝ] V,
      (∀ f v, ⟪D (G f), D v⟫ = ⟪f - N.starProjection f, i v⟫) ∧
      (∀ f, i (G f) ∈ Nᗮ) ∧ (∀ f ∈ N, G f = 0) := by
  dsimp only
  let K := resolvent i D hc
  let N := Fredholm.nullspace K
  have hKc := resolvent_compact i D hc hi
  have hKs := resolvent_symmetric i D hc
  refine ⟨Fredholm.finiteDimensional_nullspace K hKc, ?_⟩
  obtain ⟨U, hleft, _, hmem, hzero⟩ := Fredholm.exists_generalized_inverse K hKc hKs
  refine ⟨weakSolution i D hc ∘L U, ?_, ?_, ?_⟩
  · intro f v
    have hw := weakSolution_identity i D hc (U f) v
    have hu := congrArg (fun A : H →L[ℝ] H => A f) hleft
    change U f - K (U f) = f - N.starProjection f at hu
    rw [← hu, inner_sub_left]
    change ⟪D (weakSolution i D hc (U f)), D v⟫ = ⟪U f, i v⟫ - ⟪i (weakSolution i D hc (U f)), i v⟫
    linarith
  · intro f
    exact Fredholm.map_orthogonal_nullspace K hKs (U f) (hmem f)
  · intro f hf
    change weakSolution i D hc (U f) = 0
    rw [hzero f hf, map_zero]

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

theorem geometric_weak_inverse
    (D : ∀ p : A.centers, Data J α ht p.val)
    (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source) :
    FiniteDimensional ℝ (harmonicAnti A J α hs ht) ∧
      ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
        (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
          ⟪f - (harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
        (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
        (∀ f ∈ harmonicAnti A J α hs ht, G f = 0) :=
  Variational.exists_energy_inverse (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht)
    (energyInclusion_compact A J α hs ht D hD)

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothPatchGlue
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma smooth_multiply_pair (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a b : antiPre A J α hs ht) :
    ⟪smoothL2 A J α hs ht true b.val,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ =
    ⟪smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ b).val,smoothL2 A J α hs ht true a.val⟫ := by
  rw [(smoothL2 A J α hs ht true).inner_map_map,(smoothL2 A J α hs ht true).inner_map_map,
    preL2_inner,preL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (MetricForms.pairing_smul_right _ _ _ _).trans (MetricForms.pairing_smul_left _ _ _ _).symm

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma anti_partition_sum {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (a : antiPre A J α hs ht) : ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) a = a := by
  have he := map_sum (((smoothForms X 2).subtype).comp (antiPre A J α hs ht).subtype)
    (fun i => antiMultiply A J α hs ht (ρ i) (hρ i) a) Finset.univ
  apply Subtype.ext
  apply Subtype.ext
  refine he.trans ?_
  funext x
  rw [Finset.sum_apply]
  change (∑ i, ρ i x • a.val.val x) = a.val.val x
  rw [← Finset.sum_smul,h1,one_smul]

lemma energy_eq_of_pair_smooth (u v : antiEnergy A J α hs ht)
    (h : ∀ a : antiPre A J α hs ht,
      ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true a.val⟫ =
      ⟪energyInclusion A J α hs ht v,smoothL2 A J α hs ht true a.val⟫) : u = v := by
  have he : (fun z : antiEnergy A J α hs ht =>
      ⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht z⟫) =
      (fun z : antiEnergy A J α hs ht =>
      ⟪energyInclusion A J α hs ht v,energyInclusion A J α hs ht z⟫) :=
    (antiToEnergy_dense A J α hs ht).equalizer
      (continuous_const.inner (energyInclusion A J α hs ht).continuous)
      (continuous_const.inner (energyInclusion A J α hs ht).continuous) (funext h)
  apply energyInclusion_injective A J α hs ht
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hh := congrFun he (u-v)
  rw [map_sub] at hh
  rw [inner_sub_left,hh,sub_self]

lemma glue_weak_patches {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (u : antiEnergy A J α hs ht) (w : ι → antiPre A J α hs ht)
    (hw : ∀ i a, ⟪energyInclusion A J α hs ht u,
        smoothL2 A J α hs ht true (antiMultiply A J α hs ht (ρ i) (hρ i) a).val⟫ =
      ⟪smoothL2 A J α hs ht true (w i).val,
        smoothL2 A J α hs ht true (antiMultiply A J α hs ht (ρ i) (hρ i) a).val⟫) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  classical
  let b := ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) (w i)
  refine ⟨b,(energy_eq_of_pair_smooth A J α hs ht u (antiToEnergy A J α hs ht b) ?_).symm⟩
  intro a
  have ha := congrArg (fun c : antiPre A J α hs ht => smoothL2 A J α hs ht true c.val)
    (anti_partition_sum A J α hs ht ρ hρ h1 a)
  have hsum (t : ι → antiPre A J α hs ht) :
      smoothL2 A J α hs ht true (∑ i, t i).val = ∑ i, smoothL2 A J α hs ht true (t i).val := by
    exact map_sum ((smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype) t Finset.univ
  rw [hsum] at ha
  change ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true a.val⟫ =
    ⟪smoothL2 A J α hs ht true b.val,smoothL2 A J α hs ht true a.val⟫
  rw [← ha,inner_sum]
  conv_rhs => rw [show b = ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) (w i) from rfl,hsum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [hw,smooth_multiply_pair,ha]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_GlobalSmoothRegularity
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

theorem weak_solution_smooth (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  classical
  choose V hV hxV w hw using exists_weak_patch A J α hs ht D hD f u heq
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion_of_mem x (hxV x))
  have hc : (univ : Set X) ⊆ ⋃ p : s, V p.val := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => V p.val) (fun p => hV p.val) hc
  apply glue_weak_patches A J α hs ht (fun p : s => ρ p) (fun p => (ρ p).contMDiff)
    (fun x => ?_) u (fun p : s => w p.val) (fun p => hw p.val (ρ p) (ρ p).contMDiff (hρ p))
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)

include hD in
lemma weak_kernel_smooth (u : antiEnergy A J α hs ht) (hu : weakDelta A J α hs ht u = 0) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  apply weak_solution_smooth A J α hs ht D hD 0 u
  intro v
  rw [hu,inner_zero_left]
  change 0 = ⟪smoothL2 A J α hs ht true 0,energyInclusion A J α hs ht v⟫
  rw [map_zero,inner_zero_left]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothGeometricInverse
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma harmonicAnti_smooth (f : L2 A J α hs ht true) (hf : f ∈ harmonicAnti A J α hs ht) :
    ∃ b : antiPre A J α hs ht, smoothL2 A J α hs ht true b.val = f ∧
      codifferential J α ht b.val.val = 0 := by
  obtain ⟨u,hu,hd⟩ := (mem_harmonicAnti A J α hs ht f).mp hf
  obtain ⟨b,hb⟩ := weak_kernel_smooth A J α hs ht D hD u hd
  refine ⟨b,?_,?_⟩
  · rw [← hb] at hu
    exact hu
  · rw [← hb] at hd
    change smoothL2 A J α hs ht false (antiDelta A J α hs ht b) = 0 at hd
    have he := (smoothL2 A J α hs ht false).injective (hd.trans (map_zero _).symm)
    exact congrArg Subtype.val he

include hD in

theorem geometric_smooth_inverse_oai :
    FiniteDimensional ℝ (harmonicAnti A J α hs ht) ∧
      ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
        (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
          ⟪f - (harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
        (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
        (∀ f ∈ harmonicAnti A J α hs ht, G f = 0) ∧
        (∀ f : antiPre A J α hs ht, ∃ b : antiPre A J α hs ht,
          antiToEnergy A J α hs ht b = G (smoothL2 A J α hs ht true f.val)) := by
  obtain ⟨hfin,G,hG,horth,hGzero⟩ := geometric_weak_inverse A J α hs ht D hD
  refine ⟨hfin,G,hG,horth,hGzero,fun f => ?_⟩
  obtain ⟨h,hh,-⟩ := harmonicAnti_smooth A J α hs ht D hD
    ((harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
    ((harmonicAnti A J α hs ht).starProjection_apply_mem _)
  apply weak_solution_smooth A J α hs ht D hD (f-h)
  intro v
  rw [hG,← hh]
  change _ = ⟪smoothL2 A J α hs ht true (f.val-h.val),energyInclusion A J α hs ht v⟫
  rw [map_sub]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse_oai.{u_1}
