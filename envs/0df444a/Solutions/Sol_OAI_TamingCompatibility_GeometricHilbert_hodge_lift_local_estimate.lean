-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:08:21.516353+00:00
-- url     : https://prove2.me/submissions/de035ae5-207b-4ad2-b9a6-62c2614996a3

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc032
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_exists_local_ddstar_estimate_on
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_geometric_smooth_inverse
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FiberMap
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv
section FiberMaps

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma toDistribution_fiberOperator (s : ℝ) (L : F →L[ℂ] G) (u : H E F s) :
    toDistribution E G s (fiberOperator s L u) = fiberMap L (toDistribution E F s u) := by
  change besselPotential E G (-s) (L.compLp u : 𝓢'(E,G)) =
    fiberMap L (besselPotential E F (-s) (u : 𝓢'(E,F)))
  rw [fiberMap_bessel, fiberMap_Lp]

end FiberMaps

end TamingCompatibility.HilbertSobolev

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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

end TamingCompatibility.GeometricHilbert

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
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma harmonic_seminorm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : antiPre A J α hs ht →ₗ[ℝ] E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ‖F h‖ ≤ C * ‖smoothL2 A J α hs ht true f.val‖ := by
  classical
  obtain ⟨hfin,-⟩ := geometric_smooth_inverse A J α hs ht D hD
  let := hfin
  let i : antiPre A J α hs ht →ₗ[ℝ] L2 A J α hs ht true :=
    (smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype
  have hi : Function.Injective i := (smoothL2 A J α hs ht true).injective.comp Subtype.val_injective
  have hl : ∀ k : harmonicAnti A J α hs ht, ∃ a : antiPre A J α hs ht, i a = k.val := by
    intro k
    obtain ⟨a,ha,-⟩ := harmonicAnti_smooth A J α hs ht D hD k.val k.property
    exact ⟨a,ha⟩
  let L := InjectiveLinearLift.lift i hi (harmonicAnti A J α hs ht).subtype hl
  let T : harmonicAnti A J α hs ht →L[ℝ] E := LinearMap.toContinuousLinearMap (F.comp L)
  refine ⟨‖T‖,norm_nonneg T,fun f h hh => ?_⟩
  let k : harmonicAnti A J α hs ht := ⟨(harmonicAnti A J α hs ht).starProjection (i f),
    (harmonicAnti A J α hs ht).starProjection_apply_mem (i f)⟩
  have he : L k = h := hi ((InjectiveLinearLift.lift_spec i hi _ hl k).trans hh.symm)
  have hn : ‖k‖ ≤ ‖i f‖ := (harmonicAnti A J α hs ht).norm_starProjection_apply_le (i f)
  calc
    ‖F h‖ = ‖T k‖ := by change ‖F h‖ = ‖F (L k)‖; rw [he]
    _ ≤ ‖T‖ * ‖k‖ := T.le_opNorm k
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (norm_nonneg T)

end TamingCompatibility.GeometricHilbert

end
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
local instance instNormedSpaceRealTangentSpaceSpaceModel_2_r74f3d1_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
attribute [local instance] OAI.TamingCompatibility.instFiniteDimensionalRealTangentSpaceSpaceModel_2
lemma l2JAction_norm (a : L2 A J α hs ht true) : ‖l2JAction A J α hs ht a‖ = ‖a‖ := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq (l2JAction A J α hs ht).continuous.norm continuous_norm) ?_
  intro b
  rw [l2JAction_smooth,(smoothL2 A J α hs ht true).norm_map,
    (preJAction A J α hs ht).norm_map,(smoothL2 A J α hs ht true).norm_map]

lemma l2AntiProjection_smooth (a : PreL2 A J α hs ht true) :
    l2AntiProjection A J α hs ht (smoothL2 A J α hs ht true a) =
      smoothL2 A J α hs ht true ⟨antiInvariantPart J a.val,IsSmooth.antiInvariantPart a.property J⟩ := by
  rw [l2AntiProjection_apply,l2JAction_smooth,← map_sub,← map_smul]
  rfl

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairing
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open GeometricChart ManifoldForms ManifoldLocalization ComplexMatrix Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [CompactSpace X] in
lemma scalar_pair_zero (p : A.centers) (a : TwoForm X) (z : Space) :
    GeometricChart.scalar A J α ht D p a 2 z = HodgeChart.scalar A J α ht D p a 1 z := rfl
omit [CompactSpace X] in
lemma scalar_pair_one (p : A.centers) (a : TwoForm X) (z : Space) :
    GeometricChart.scalar A J α ht D p a 3 z = HodgeChart.scalar A J α ht D p a 2 z := rfl

lemma realPairSchwartz_from_full (p : A.centers) (f : smoothForms X 2) :
    SchwartzMap.postcompCLM (embed 2) (realPairSchwartz A J α ht D hD p f) =
      SchwartzMap.postcompCLM antiPairSelector (scalarVectorLinear A J α ht D hD p f) := by
  rw [← realVectorSchwartz_embed A J α ht D hD p f]
  ext z i
  fin_cases i <;> simp [antiPairSelector,realPairSchwartz_apply,realVectorSchwartz_apply,
    EuclideanEnergy.pair,scalar_pair_zero,scalar_pair_one]
end TamingCompatibility.HodgeChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ComplexMatrix GeometricChart
open TemperedDistribution EuclideanSobolevOperators HilbertSobolev
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma weightedRawRHS_full_distribution (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (f : antiPre A J α hs ht) :
    (SchwartzMap.postcompCLM (embed 2)
      (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ f) : 𝓢'(Space,C 2)) =
      (2:ℂ) • smulLeftCLM (C 2) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
        (fiberMap antiPairSelector
          (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f.val))) := by
  rw [hodgeRawDistribution_smooth,fiberMap_schwartz,product_schwartz,← map_smul]
  congr 1
  ext z i
  have hp := HodgeChart.realPairSchwartz_from_full A J α ht (fun p => (D p).toData) hD p f.val
  rw [← HodgeChart.realVectorSchwartz_embed A J α ht (fun p => (D p).toData) hD p f.val] at hp
  have hpz := congrArg (fun a : 𝓢(Space,C 2) => a z i) hp
  fin_cases i <;> simp [antiPairSelector] at hpz <;>
    simp [weightedRawRHS,antiPairSelector,
      SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
      hpz]
end TamingCompatibility.GeometricHilbert

end
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

lemma preAntiProjection_apply (a : PreL2 A J α hs ht true) :
    preAntiProjection A J α hs ht a =
      ⟨antiInvariantPart J a.val,IsSmooth.antiInvariantPart a.property J⟩ := rfl

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAntiRHSBound
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ComplexMatrix GeometricChart
open TemperedDistribution EuclideanSobolevOperators HilbertSobolev Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in

lemma hodge_antiRHS_bound (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (U : Set Space) (hχ : ∀ z ∈ U, χ z = 1) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 3,
        (∀ f, toDistribution Space (C 6) 3 (L f) =
          smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
            (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
        ∀ f, ‖L f‖ ≤ B*(r⁻¹)^3*‖f‖)
    (ρ : 𝓢(Space,ℝ)) (hρ : tsupport ρ ⊆ U) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ a : PreL2 A J α hs ht true,
        ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
          (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
            (smoothAntiProjection A J α hs ht a)))‖ ≤
          C₀*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  let ρc := SchwartzMap.postcompCLM Complex.ofRealCLM ρ
  let M := antiPairSelector.comp antiMatrix
  let N : H Space (C 6) 3 →L[ℂ] H Space (C 2) 3 :=
    (2:ℂ) • (product 3 ρc).comp (fiberOperator 3 M)
  refine ⟨‖N‖*B,mul_nonneg (norm_nonneg _) hB,fun r hr hr1 a => ?_⟩
  obtain ⟨L,he,hb⟩ := hL r hr hr1
  let f := smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)
  have hsupp : tsupport ρc ⊆ U :=
    (tsupport_comp_subset (map_zero Complex.ofRealCLM) ρ).trans hρ
  have hdist : toDistribution Space (C 2) 3 (N (L f)) =
      (SchwartzMap.postcompCLM (embed 2)
        (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
          (smoothAntiProjection A J α hs ht a)) : 𝓢'(Space,C 2)) := by
    rw [weightedRawRHS_full_distribution]
    change toDistribution Space (C 2) 3 (N (L f)) =
      (2:ℂ) • smulLeftCLM (C 2) ρc (fiberMap antiPairSelector
        (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeSmooth A J α hs ht (preAntiProjection A J α hs ht a))))
    rw [preAntiProjection_apply,hodgeRawDistribution_smooth_antiInvariant]
    simp only [N,smul_apply,ContinuousLinearMap.comp_apply,map_smul]
    have hp (u : H Space (C 2) 3) : toDistribution Space (C 2) 3 (product 3 ρc u) =
        smulLeftCLM (C 2) ρc (toDistribution Space (C 2) 3 u) := by
      simpa only [Nat.cast_ofNat] using toDistribution_product (F := C 2) 3 ρc u
    have hef := he f
    dsimp only [f] at hef
    rw [hodgeRegularizedGraph_smoothShift_cube] at hef
    rw [hp,toDistribution_fiberOperator,hef,fiberMap_product]
    rw [local_cutoff_one χ ρc (fun z hz => hχ z (hsupp hz))]
    congr 2
  have hn : schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
      (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
        (smoothAntiProjection A J α hs ht a))) = N (L f) := by
    apply toDistribution_injective (3:ℝ)
    rw [schwartzToH_spec,hdist]
  rw [hn]
  calc
    _ ≤ ‖N‖*‖L f‖ := N.le_opNorm _
    _ ≤ ‖N‖*(B*(r⁻¹)^3*‖f‖) := mul_le_mul_of_nonneg_left (hb f) (norm_nonneg _)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAntiNorms
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] in
lemma smoothAntiProjection_cube_norm (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    ‖smoothL2 A J α hs ht true (smoothAntiProjection A J α hs ht a).val‖ ≤
      ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖ := by
  change ‖smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a)‖ ≤ _
  rw [preAntiProjection_smooth]
  calc
    _ ≤ ‖smoothL2 A J α hs ht true a‖ := l2AntiProjection_norm A J α hs ht _
    _ = ‖hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a))‖ := by
      rw [hodgeRegularization_smoothShift_cube A J α hs ht r hr]
    _ ≤ _ := hodgeRegularization_norm_le A J α hs ht r _

omit [T2Space X] in
lemma smoothAntiProjection_cube_dual (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) (v : antiEnergy A J α hs ht) :
    |⟪smoothL2 A J α hs ht true (smoothAntiProjection A J α hs ht a).val,
      energyInclusion A J α hs ht v⟫| ≤
      (‖energyInclusion A J α hs ht‖ *
        ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖)*‖v‖ := by
  calc
    _ ≤ ‖smoothL2 A J α hs ht true (smoothAntiProjection A J α hs ht a).val‖ *
        ‖energyInclusion A J α hs ht v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖ *
        (‖energyInclusion A J α hs ht‖*‖v‖) :=
      mul_le_mul (smoothAntiProjection_cube_norm A J α hs ht r hr a)
        ((energyInclusion A J α hs ht).le_opNorm v) (norm_nonneg _ ) (norm_nonneg _)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricChart
open ComplexMatrix TemperedDistribution HilbertSobolev Set
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma hodge_lift_local_estimate_oai
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
      (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
    (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
      weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
        ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C₀*M)
    (p : A.centers) (q : Space) (hq : q ∈ (D p).domain)
    (hwq : coordinateWeight A p q ≠ 0) :
    ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ (D p).domain ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
        ∀ (a : PreL2 A J α hs ht true) (x : Space), x ∈ O →
          ‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht
            (Gs (smoothAntiProjection A J α hs ht a)).val.val))
            (extChartAt Model p.val).symm x‖ ≤
              C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  obtain ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,B,hB,hL⟩ :=
    hodgeRegularization_uniform_local_H3 A J α hs ht D hD p q hq hwq
  obtain ⟨ρ,_,hρ,O,hO,hqO,hOD,C,hC,hest⟩ :=
    exists_local_ddstar_estimate_on A J α hs ht (fun p => (D p).toData) hD
      p τ U hU hUD hτ q hqU
  obtain ⟨B₁,hB₁,h₁⟩ := hodge_antiRHS_bound A J α hs ht D hD p τ χ U hχ B hB hL ρ hρ
  let F := rawRHSSeminormMap A J α hs ht (fun p => (D p).toData) hD p τ ρ
  obtain ⟨B₂,hB₂,h₂⟩ := harmonic_seminorm_bound A J α hs ht (fun p => (D p).toData) hD F
  let E := C₀*‖energyInclusion A J α hs ht‖
  have hE : 0 ≤ E := mul_nonneg hC₀.le (norm_nonneg (energyInclusion A J α hs ht))
  refine ⟨O,hO,hqO,hOD,C*(E+B₁+B₂),mul_nonneg hC (by positivity),fun r hr hr1 a x hx => ?_⟩
  let f := smoothAntiProjection A J α hs ht a
  let N := ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖
  have hN : 0 ≤ N := norm_nonneg _
  have ht1 : 1 ≤ (r⁻¹)^3 := one_le_pow₀ ((one_le_inv₀ hr).mpr hr1)
  have he : ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ E*N := by
    exact (hdual f (‖energyInclusion A J α hs ht‖*N) (mul_nonneg (norm_nonneg (energyInclusion A J α hs ht)) hN)
      (smoothAntiProjection_cube_dual A J α hs ht r hr a)).trans_eq (by dsimp [E] <;> ring)
  have hf : ‖F f‖ ≤ B₁*(r⁻¹)^3*N := h₁ r hr hr1 a
  have hh : ‖F (H f)‖ ≤ B₂*N := (h₂ f (H f) (hH f)).trans
    (mul_le_mul_of_nonneg_left (smoothAntiProjection_cube_norm A J α hs ht r hr a) hB₂)
  have hdiff : ‖F (f-H f)‖ ≤ B₁*(r⁻¹)^3*N+B₂*N := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add hf hh)
  have hb := hest (f-H f) (Gs f) (hweak f) x hx
  change _ ≤ C*(‖antiToEnergy A J α hs ht (Gs f)‖+‖F (f-H f)‖) at hb
  calc
    _ ≤ _ := hb
    _ ≤ C*(E*N+(B₁*(r⁻¹)^3*N+B₂*N)) := mul_le_mul_of_nonneg_left (add_le_add he hdiff) hC
    _ ≤ C*((E+B₁+B₂)*(r⁻¹)^3*N) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have he' := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hE hN)
      have hh' := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hB₂ hN)
      nlinarith
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate_oai.{u_1}
