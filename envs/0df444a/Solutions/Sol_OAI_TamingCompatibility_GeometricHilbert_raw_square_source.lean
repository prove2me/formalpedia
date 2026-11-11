-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.raw_square_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:31:36.115726+00:00
-- url     : https://prove2.me/submissions/9f4ae962-db5a-4c1f-8126-0f8a1f1029b7

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028
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
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hdim hb h0 h1 h2 h3 hF in

lemma normalSymbol_geometric (ξ : E →L[ℝ] ℝ) (q : Pair) (i : Fin 4) :
    starThree g F (wedgeOne ξ (q 0 • AntiInvariantFrame.realPart g b +
      q 1 • AntiInvariantFrame.imagPart g b)) ![b i] =
        normalSymbol (WithLp.toLp 2 (fun k => ξ (b k))) q i := by
  have he : wedgeOne ξ (q 0 • AntiInvariantFrame.realPart g b +
      q 1 • AntiInvariantFrame.imagPart g b) =
        q 0 • wedgeOne ξ (AntiInvariantFrame.realPart g b) +
          q 1 • wedgeOne ξ (AntiInvariantFrame.imagPart g b) := by
    change (wedgeOneBilinear (E := E) (ofSubsingletonLIE (0 : Fin 1) ξ)) _ = _
    rw [_root_.map_add,_root_.map_smul,_root_.map_smul]
    rfl
  rw [he,starThree_add,starThree_smul,starThree_smul]
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  rw [AntiInvariantFrame.star_wedge_real g hdim b hb J h0 h1 h2 h3 F hF,
    AntiInvariantFrame.star_wedge_imag g hdim b hb J h0 h1 h2 h3 F hF]
  rfl

end TamingCompatibility.LocalMatrixOperator

end
end

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_NormalSystem
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace SchwartzMap

lemma normal_operator_expansion {A B : V → ℝ} {ψ χ : V → MetricForms.Form V 2} {x : V}
    (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (hψx : ψ x = realPart g b) (hχx : χ x = imagPart g b)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hψ : DifferentiableAt ℝ ψ x) (hχ : DifferentiableAt ℝ χ x) :
    frameVector b (starThree g F (extDeriv (fun y => A y • ψ y + B y • χ y) x)) =
      (∑ i, normalPrincipal b i (pair (fderiv ℝ A x (e i)) (fderiv ℝ B x (e i)))) +
      normalLower g F ψ χ b x (pair (A x) (B x)) := by
  rw [LocalFrameOperator.expansion_at g F hA hB hψ hχ]
  simp only [map_add,map_smul]
  apply congrArg₂ (· + ·)
  · have hA' := covector_expansion (fderiv ℝ A x)
    have hB' := covector_expansion (fderiv ℝ B x)
    conv_lhs => rw [hA',hB']
    change frameVector b (starThreeCLM g F (wedgeOneRight (ψ x) _)) +
      frameVector b (starThreeCLM g F (wedgeOneRight (χ x) _)) = _
    simp only [_root_.map_sum,map_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ext j
    have hn := normalSymbol_geometric g (by simp [V]) b hb J h0 h1 h2 h3 F hF
      (EuclideanSpace.proj i) (pair (fderiv ℝ A x (e i)) (fderiv ℝ B x (e i))) j
    rw [← hψx,← hχx] at hn
    change (starThree g F (wedgeOne (EuclideanSpace.proj i)
      ((fderiv ℝ A x (e i)) • ψ x + (fderiv ℝ B x (e i)) • χ x))) ![b j] = _ at hn
    have hw : wedgeOne (EuclideanSpace.proj i)
        ((fderiv ℝ A x (e i)) • ψ x + (fderiv ℝ B x (e i)) • χ x) =
      (fderiv ℝ A x (e i)) • wedgeOne (EuclideanSpace.proj i) (ψ x) +
      (fderiv ℝ B x (e i)) • wedgeOne (EuclideanSpace.proj i) (χ x) := by
      change (wedgeOneBilinear (E := V) (ofSubsingletonLIE (0 : Fin 1) (EuclideanSpace.proj i))) _ = _
      rw [map_add,map_smul,map_smul]
      rfl
    rw [hw,starThree_add,starThree_smul,starThree_smul] at hn
    simpa only [frameVector_apply,normalPrincipal,frameCovector,starThreeCLM_apply,
      wedgeOneRight_apply,starThree_add,starThree_smul,ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
      pair,PiLp.proj_apply] using hn
  · simp only [normalLower,ContinuousLinearMap.comp_apply,combine_pair,map_add,map_smul,
      starThreeCLM_apply]

end TamingCompatibility.LocalMatrixOperator

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_ChartNormalTest
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
namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy
lemma pair_fderiv {q : V → Pair} {x v : V} (hq : DifferentiableAt ℝ q x) :
    pair (fderiv ℝ (fun y => q y 0) x v) (fderiv ℝ (fun y => q y 1) x v) =
      fderiv ℝ q x v := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp x hq.hasFDerivAt
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp x hq.hasFDerivAt
  change HasFDerivAt (fun y => q y 0) _ x at h0
  change HasFDerivAt (fun y => q y 1) _ x at h1
  rw [h0.fderiv,h1.fderiv]
  ext i
  fin_cases i <;> rfl
end TamingCompatibility.LocalMatrixOperator

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

include hs in
lemma normal_coordinateTest {q : Space → EuclideanEnergy.Pair}
    (hq : ContDiff ℝ ∞ q) {z : Space} (hz : z ∈ D.domain) :
    frameVector (fun i => D.frame i z)
      (MetricHodge.starThree (coordinateMetric J α ht p z)
        (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (coordinateTest J α ht p D q) z)) =
      (∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
        normalB J α ht p D z (q z) := by
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  have hψ := realPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have hχ := imagPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have hd : DifferentiableAt ℝ q z := hq.differentiable (by norm_num) z
  have h := normal_operator_expansion
    (A := fun y => q y 0) (B := fun y => q y 1)
    (ψ := fun y => realPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (χ := fun y => imagPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
    (fun i => D.frame i z) (D.frame_gram z hz) (coordinateJ J p z) h0 h1 h2 h3
    (fun u v => ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hz) u v)
    rfl rfl (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hq).differentiable (by norm_num) z)
    (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hq).differentiable (by norm_num) z)
    (((hψ z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
    (((hχ z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
  simp only [pair_fderiv hd] at h
  have hqz : EuclideanEnergy.pair (q z 0) (q z 1) = q z := by ext i; fin_cases i <;> rfl
  rw [hqz] at h
  exact h

variable [T2Space X]
include hs in
lemma normal_manifoldTest_delta {q : Space → EuclideanEnergy.Pair}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ D.domain) :
    frameVector (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht (manifoldTest J α ht p D q))
        (extChartAt Model p).symm z) =
      -((∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
        normalB J α ht p D z (q z)) := by
  rw [pullback_codifferential_antiInvariant J α ht
    (manifoldTest_smooth J α hs ht p D hq hc hqD) (manifoldTest_anti J α ht p D q)
    p (D.domain_subset hz),map_neg]
  have he : ManifoldForms.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm =ᶠ[𝓝 z]
      coordinateTest J α ht p D q := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds (D.domain_subset hz)] with y hy
    exact pullback_manifoldTest J α ht p D hqD hy
  rw [he.extDeriv_eq,normal_coordinateTest J α hs ht p D hq hz]
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

include hs in
lemma normal_coordinateTest_at {q : Space → EuclideanEnergy.Pair}
    {z : Space} (hd : DifferentiableAt ℝ q z) (hz : z ∈ D.domain) :
    frameVector (fun i => D.frame i z)
      (MetricHodge.starThree (coordinateMetric J α ht p z)
        (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (coordinateTest J α ht p D q) z)) =
      (∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
        normalB J α ht p D z (q z) := by
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  have hψ := realPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have hχ := imagPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have h := normal_operator_expansion
    (A := fun y => q y 0) (B := fun y => q y 1)
    (ψ := fun y => realPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (χ := fun y => imagPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
    (fun i => D.frame i z) (D.frame_gram z hz) (coordinateJ J p z) h0 h1 h2 h3
    (fun u v => ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hz) u v)
    rfl rfl ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiableAt.comp z hd)
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).differentiableAt.comp z hd)
    (((hψ z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
    (((hχ z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
  simp only [pair_fderiv hd] at h
  have hqz : EuclideanEnergy.pair (q z 0) (q z 1) = q z := by ext i; fin_cases i <;> rfl
  rw [hqz] at h
  exact h

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

include hs in
lemma normal_delta {a : TwoForm X} (ha : IsSmooth a) (hanti : antiInvariantPart J a = a)
    {z : Space} (hz : z ∈ D.domain) :
    frameVector (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z) =
      -((∑ i, normalA J α ht p D i z
          (fderiv ℝ (rawPair J α ht p D a) z (EuclideanEnergy.e i))) +
        normalB J α ht p D z (rawPair J α ht p D a z)) := by
  rw [pullback_codifferential_antiInvariant J α ht ha hanti p (D.domain_subset hz),map_neg]
  have he : ManifoldForms.pullback a (extChartAt Model p).symm =ᶠ[𝓝 z]
      coordinateTest J α ht p D (rawPair J α ht p D a) := by
    filter_upwards [D.domain_open.mem_nhds hz] with y hy
    exact rawScalar_expansion J α ht p D hanti hy
  rw [he.extDeriv_eq]
  rw [normal_coordinateTest_at J α hs ht p D
    (((rawPair_smooth J α ht p D ha z hz).contDiffAt
      (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num)) hz]
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator ManifoldLocalization ManifoldVolume
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

lemma normalOperator_zero_off (q : Space → EuclideanEnergy.Pair) {z : Space}
    (hz : z ∉ tsupport q) : normalOperator J α ht p D q z = 0 := by
  have he : q =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport q).isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  simp only [normalOperator,he.fderiv_eq,fderiv_fun_const,
    image_eq_zero_of_notMem_tsupport hz,map_zero,add_zero]
  apply Finset.sum_eq_zero
  intro i _
  change (normalA J α ht p D i z) (0 : EuclideanEnergy.Pair) = 0
  exact map_zero _

variable [T2Space X]
lemma manifoldTest_delta_zero_off {q : Space → EuclideanEnergy.Pair}
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {x : X} (hx : x ∉ (extChartAt Model p).symm '' tsupport q) :
    codifferential J α ht (manifoldTest J α ht p D q) x = 0 := by
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  rw [codifferential_anti J α ht (manifoldTest_anti J α ht p D q)]
  have he : exteriorDerivative (manifoldTest J α ht p D q) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact manifoldTest_zero_off J α ht p D q hy
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (exteriorDerivative (manifoldTest J α ht p D q) x) = 0
  rw [he]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (0 : MetricForms.Form Space 3) = 0
  exact (congrArg Neg.neg (MetricHodge.starThree_zero (E := Space)
    (GeometricAdjoint.pointMetric J α ht x) (invariantPart J α x))).trans (neg_zero)

variable (hs : IsSmooth α)
include hs in
lemma normal_energy_point {a : TwoForm X} (ha : IsSmooth a) (hanti : antiInvariantPart J a = a)
    {q : Space → EuclideanEnergy.Pair} (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hqD : tsupport q ⊆ D.domain) {z : Space} (hz : z ∈ D.domain) :
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z)
      (ManifoldForms.pullback (codifferential J α ht (manifoldTest J α ht p D q))
        (extChartAt Model p).symm z) =
      ⟪normalOperator J α ht p D (rawPair J α ht p D a) z,normalOperator J α ht p D q z⟫ := by
  rw [← frameVector_pairing _ _ (D.frame_gram z hz),normal_delta J α hs ht p D ha hanti hz,
    normal_manifoldTest_delta J α hs ht p D hq hc hqD hz,inner_neg_neg]
  rfl

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (A : FiniteCharts X)
include hs in
lemma normal_energy_integral {a : TwoForm X} (ha : IsSmooth a) (hanti : antiInvariantPart J a = a)
    {q : Space → EuclideanEnergy.Pair} (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hqD : tsupport q ⊆ D.domain) :
    (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a)
      (codifferential J α ht (manifoldTest J α ht p D q)) x ∂geometricVolume A J α) =
    ∫ z, chartDensity J α p z *
      ⟪normalOperator J α ht p D (rawPair J α ht p D a) z,normalOperator J α ht p D q z⟫ := by
  let f := GeometricAdjoint.pairing J α ht (codifferential J α ht a)
    (codifferential J α ht (manifoldTest J α ht p D q))
  have hfc : Continuous f := (GeometricAdjoint.pairing_one_smooth J α hs ht
    (GeometricAdjoint.codifferential_smooth J α hs ht ha)
    (GeometricAdjoint.codifferential_smooth J α hs ht (manifoldTest_smooth J α hs ht p D hq hc hqD))).continuous
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have hfK : tsupport f ⊆ (extChartAt Model p).symm '' tsupport q := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    apply hx
    change MetricForms.pairing (E := Space) (GeometricAdjoint.pointMetric J α ht x)
      (codifferential J α ht a x) (codifferential J α ht (manifoldTest J α ht p D q) x) = 0
    rw [manifoldTest_delta_zero_off J α ht p D hc hqD hn]
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
  by_cases hzq : z ∈ tsupport q
  · have hz := D.domain_subset (hqD hzq)
    rw [indicator_of_mem hz]
    change chartDensity J α p z * GeometricAdjoint.pairing J α ht _ _
      ((extChartAt Model p).symm z) = _
    rw [← pairing_chart J α ht p (Or.inl rfl) _ _ hz]
    rw [normal_energy_point J α ht p D hs ha hanti hq hc hqD (hqD hzq)]
  · rw [normalOperator_zero_off J α ht p D q hzq,inner_zero_right,mul_zero]
    by_cases hz : z ∈ (extChartAt Model p).target
    · rw [indicator_of_mem hz]
      have hn : (extChartAt Model p).symm z ∉ (extChartAt Model p).symm '' tsupport q := by
        rintro ⟨y,hy,he⟩
        apply hzq
        have hzy : y=z := (extChartAt Model p).symm.injOn (D.domain_subset (hqD hy)) hz he
        rwa [← hzy]
      change chartDensity J α p z * MetricForms.pairing (E := Space)
        (GeometricAdjoint.pointMetric J α ht ((extChartAt Model p).symm z))
        (codifferential J α ht a ((extChartAt Model p).symm z))
        (codifferential J α ht (manifoldTest J α ht p D q) ((extChartAt Model p).symm z)) = 0
      rw [manifoldTest_delta_zero_off J α ht p D hc hqD hn]
      exact (congrArg (fun t : ℝ => chartDensity J α p z * t)
        (MetricForms.pairing_zero_right (E := Space) _ _)).trans (mul_zero _)
    · rw [indicator_of_notMem hz]
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_NormalDistribution
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume LocalFormalAdjoint
open Set Filter _root_.MeasureTheory LineDeriv
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma firstOrder_local (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (s : 𝓢(Space,EuclideanEnergy.Pair))
    (f : Space → EuclideanEnergy.Pair) {z : Space} (he : (s : Space → _) =ᶠ[𝓝 z] f)
    (ha : ∀ i, a i z = normalA J α ht p D i z) (hb : b z = normalB J α ht p D z) :
    firstOrder EuclideanEnergy.e a b s z = normalOperator J α ht p D f z := by
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    multiply_apply,lineDerivOpCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,
    ha,hb,he.fderiv_eq,he.eq_of_nhds,normalOperator]

lemma firstOrder_zero_off (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (q : 𝓢(Space,EuclideanEnergy.Pair))
    {z : Space} (hz : z ∉ tsupport q) : firstOrder EuclideanEnergy.e a b q z = 0 := by
  have hd (i : Fin 4) : (∂_{EuclideanEnergy.e i} q : 𝓢(Space,EuclideanEnergy.Pair)) z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    multiply_apply,lineDerivOpCLM_apply,hd,image_eq_zero_of_notMem_tsupport hz,map_zero,
    Finset.sum_const_zero,add_zero]

variable [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X)
include hs in
lemma chart_energy_local {u : TwoForm X} (hu : IsSmooth u) (hanti : antiInvariantPart J u = u)
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p D i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p D z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p z)
    (s q : 𝓢(Space,EuclideanEnergy.Pair))
    (hsU : ∀ z ∈ U, s z = rawPair J α ht p D u z)
    (hqc : HasCompactSupport (q : Space → _)) (hqU : tsupport q ⊆ U) :
    (∫ z, ρ z * ⟪firstOrder EuclideanEnergy.e a b s z,firstOrder EuclideanEnergy.e a b q z⟫) =
      ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht u)
        (codifferential J α ht (manifoldTest J α ht p D q)) x ∂geometricVolume A J α := by
  rw [normal_energy_integral J α ht p D hs A hu hanti (q.smooth ⊤) hqc (hqU.trans hUD)]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport q
  · have hzU := hqU hz
    have he : (s : Space → _) =ᶠ[𝓝 z] rawPair J α ht p D u := by
      filter_upwards [hU.mem_nhds hzU] with y hy
      exact hsU y hy
    rw [firstOrder_local J α ht p D a b s _ he (ha z hzU) (hb z hzU),
      firstOrder_local J α ht p D a b q q Filter.EventuallyEq.rfl (ha z hzU) (hb z hzU),hρ z hzU]
  · rw [firstOrder_zero_off a b q hz,normalOperator_zero_off J α ht p D q hz]
    simp
end TamingCompatibility.GeometricChart

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_WeakNormalEquation
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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

omit [T2Space X] in
lemma smooth_delta_pair (u v : antiPre A J α hs ht) :
    ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht u),
      weakDelta A J α hs ht (antiToEnergy A J α hs ht v)⟫ =
      ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht u.val.val)
        (codifferential J α ht v.val.val) x ∂geometricVolume A J α := by
  change ⟪smoothL2 A J α hs ht false (antiDelta A J α hs ht u),
    smoothL2 A J α hs ht false (antiDelta A J α hs ht v)⟫ = _
  rw [(smoothL2 A J α hs ht false).inner_map_map,preL2_inner]
  rfl

lemma raw_square_energy (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p) i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p) z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) (u : antiEnergy A J α hs ht) :
    (ComplexMatrix.square EuclideanEnergy.e a b ρ (rawDistribution A J α hs ht D hD p τ u)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      (⟪weakDelta A J α hs ht u,weakDelta A J α hs ht
        (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  let q := componentTest j φ
  let v := testAnti A J α hs ht D p q (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))
  have hLc : Continuous (fun w => (ComplexMatrix.square EuclideanEnergy.e a b ρ
      (rawDistribution A J α hs ht D hD p τ w)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j) :=
    by
      generalize rawDistribution A J α hs ht D hD p τ = L
      generalize ComplexMatrix.square EuclideanEnergy.e a b ρ = P
      exact continuous_system_eval L P (SchwartzMap.postcompCLM Complex.ofRealCLM φ) j
  have hRc : Continuous (fun w => (⟪weakDelta A J α hs ht w,
      weakDelta A J α hs ht (antiToEnergy A J α hs ht v)⟫ : ℂ)) :=
    Complex.continuous_ofReal.comp ((weakDelta A J α hs ht).continuous.inner continuous_const)
  have hclosed : _root_.IsClosed {w : antiEnergy A J α hs ht |
      (ComplexMatrix.square EuclideanEnergy.e a b ρ (rawDistribution A J α hs ht D hD p τ w)
        (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      (⟪weakDelta A J α hs ht w, weakDelta A J α hs ht (antiToEnergy A J α hs ht v)⟫ : ℂ)} :=
    isClosed_eq hLc hRc
  refine (antiToEnergy_dense A J α hs ht).induction_on u hclosed ?_
  intro w
  rw [rawDistribution_smooth,square_component_apply,smooth_delta_pair]
  congr 1
  apply chart_energy_local J α hs ht p.val (D p) A w.val.property w.property hU hUD
    a b ρ ha hb hρ
    (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p w.val))
    q ?_ (componentTest_compact j φ hc) ((componentTest_support j φ).trans hφU)
  intro z hz
  exact cutoff_realPair_raw A J α ht D hD p w.val τ (hUD hz) (hτ z hz)

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_WeakNormal
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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

lemma rhs_component_test (p : A.centers) (f : antiPre A J α hs ht)
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (g : 𝓢(Space,EuclideanEnergy.Pair))
    (hg : ∀ z ∈ U, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) :
    (⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) =
    ((SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j := by
  rw [smooth_energy_pair,embedded_component_apply]
  congr 1
  change (∫ x, GeometricAdjoint.pairing J α ht f.val.val
    (manifoldTest J α ht p.val (D p) (componentTest j φ)) x ∂geometricVolume A J α) = _
  rw [pairing_manifoldTest_integral J α ht p.val (D p) A hs f.val.property f.property
    ((componentTest j φ).smooth ⊤) (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport φ
  · rw [hg z (hφU hz),real_inner_smul_left]
    rw [componentTest_inner]
    fin_cases j <;> simp [componentTest_apply,rawPair,EuclideanEnergy.pair] <;> ring
  · have hφz := image_eq_zero_of_notMem_tsupport hz
    simp [componentTest_apply,hφz]

lemma raw_square_source_oai (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p) i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p) z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫)
    (g : 𝓢(Space,EuclideanEnergy.Pair))
    (hg : ∀ z ∈ U, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχU : tsupport χ ⊆ U) :
    smulLeftCLM (C 2) χ (ComplexMatrix.square EuclideanEnergy.e a b ρ
      (rawDistribution A J α hs ht D hD p τ u)) =
    smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
  apply localize_eq_of_real_tests _ χ hc hχU
  intro φ hφ hφU
  ext j
  rw [raw_square_energy A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ φ hφ hφU j u,heq]
  exact rhs_component_test A J α hs ht D p f hUD g hg φ hφ hφU j

end TamingCompatibility.GeometricHilbert

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.raw_square_source_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.raw_square_source_oai.{u_1}
