-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.Hermitian.combinedForm_global_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:37:22.795763+00:00
-- url     : https://prove2.me/submissions/773a6863-8921-4a1b-b3c2-05f909b005ba

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc029
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_logForm_far_uniform
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_scalarEnergyDual_cutoffLog_bound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_scalarEnergyDual_cutoffSqrt_bound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_sqrtForm_far_uniform
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_correctedDdc_off_source_compact

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartUnitaryData
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
open scoped Manifold ContDiff SchwartzMap
namespace TamingCompatibility.GeometricChart
open ManifoldHodge ManifoldVolume ManifoldForms
open MetricModel MetricForms MetricHodge AntiInvariantFrame EuclideanEnergy LocalMatrixOperator
open _root_.MeasureTheory Set
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace Data
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : Data J α ht p)
lemma source_subset : D.source ⊆ (extChartAt Model p).source := Set.inter_subset_left
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

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartTestPairing
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstOrderAntiDdc
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extDeriv_dc_apply {J : E → E →L[ℝ] E} {f : E → ℝ} {x : E}
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x) (hJ : DifferentiableAt ℝ J x) (u v : E) :
    extDeriv (dc J f) x ![u,v] =
      -(fderiv ℝ (fderiv ℝ f) x u (J x v)) + fderiv ℝ (fderiv ℝ f) x v (J x u) +
      fderiv ℝ f x ((fderiv ℝ J x v) u - (fderiv ℝ J x u) v) := by
  let L := (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasFDerivAt.comp x ((hdf.hasFDerivAt.clm_comp hJ.hasFDerivAt).neg)
  have hd : fderiv ℝ (dc J f) x =
      L.comp (-((ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ f x)).comp (fderiv ℝ J x) +
        ((ContinuousLinearMap.compL ℝ E E ℝ).flip (J x)).comp (fderiv ℝ (fderiv ℝ f) x))) :=
    h.fderiv
  rw [extDeriv_one,hd]
  simp [L,ofSubsingletonLIE,map_sub]
  ring

lemma anti_ddc_first_order {J : E → E →L[ℝ] E} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hJ : DifferentiableAt ℝ J x)
    (hJJ : ∀ v, J x (J x v) = -v) (u v : E) :
    (extDeriv (dc J f) x ![u,v] - extDeriv (dc J f) x ![J x u,J x v])/2 =
      (1/2:ℝ) * fderiv ℝ f x
        ((fderiv ℝ J x v) u - (fderiv ℝ J x u) v +
          (fderiv ℝ J x (J x u)) (J x v) - (fderiv ℝ J x (J x v)) (J x u)) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [extDeriv_dc_apply hdf hJ,extDeriv_dc_apply hdf hJ,hJJ,hJJ]
  simp only [map_neg,neg_neg,map_sub,map_add]
  have hsym := hf.isSymmSndFDerivAt (by simp)
  rw [hsym (J x u) v,hsym (J x v) u]
  ring
end TamingCompatibility.ExteriorForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldComplexDifferential
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap ManifoldHodge Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_ddc (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    pullback (exteriorDerivative (complexDifferential J f)) (extChartAt Model p).symm z =
      extDeriv (ExteriorForms.dc (coordinateJ J p) (f ∘ (extChartAt Model p).symm)) z := by
  rw [pullback_exteriorDerivative _ (complexDifferential_smooth J hf) (isOpen_extChartAt_target p)
    (contMDiffOn_extChartAt_symm p) hz,extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz]
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
  exact pullback_complexDifferential J hf p hy

lemma anti_ddc_chart_first_order (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    pullback (antiInvariantPart J (exteriorDerivative (complexDifferential J f)))
      (extChartAt Model p).symm z ![u,v] =
      (1/2:ℝ) * fderiv ℝ (f ∘ (extChartAt Model p).symm) z
        ((fderiv ℝ (coordinateJ J p) z v) u - (fderiv ℝ (coordinateJ J p) z u) v +
          (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z u)) (coordinateJ J p z v) -
          (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z v)) (coordinateJ J p z u)) := by
  rw [pullback_antiInvariantPart J _ p hz,pullback_ddc J hf p hz]
  have hcInf : ContDiffAt ℝ ∞ (f ∘ (extChartAt Model p).symm) z :=
    (((hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm (n := ∞) p)).contDiffOn) z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)
  have hc : ContDiffAt ℝ 2 (f ∘ (extChartAt Model p).symm) z := hcInf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hj : DifferentiableAt ℝ (coordinateJ J p) z :=
    (((coordinateJ_smooth J p) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : (fun i : Fin 2 => coordinateJ J p z (![u,v] i)) =
      ![coordinateJ J p z u,coordinateJ J p z v] := by
    ext i; fin_cases i <;> rfl
  simp only [ContinuousAlternatingMap.smul_apply,ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,Function.comp_def,he,smul_eq_mul]
  simpa only [Function.comp_def,div_eq_mul_inv,mul_comm,one_mul] using
    ExteriorForms.anti_ddc_first_order hc hj (coordinateJ_square J p hz) u v
end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ScalarChartLift
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
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X]

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarChartLift_apply_inverse (p : X) (f : Space → ℝ)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    scalarChartLift p f ((extChartAt Model p).symm z) = f z := by
  classical
  simp only [scalarChartLift,ite_eq_left ((extChartAt Model p).map_target hz),
    (extChartAt Model p).right_inv hz]

omit [IsManifold Model ∞ X] in
lemma scalarChartLift_tsupport (p : X) {f : Space → ℝ}
    (hc : HasCompactSupport f) (hf : tsupport f ⊆ (extChartAt Model p).target) :
    tsupport (scalarChartLift p f) ⊆ scalarLiftSupport p f := by
  apply closure_minimal _ (scalarLiftSupport_compact p hc hf).isClosed
  intro x hx
  by_contra h
  exact hx (scalarChartLift_zero_off p f h)

omit [IsManifold Model ∞ X] [T2Space X] in

lemma scalarChartLift_fderiv (p : X) (f : Space → ℝ) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    fderiv ℝ (scalarChartLift p f ∘ (extChartAt Model p).symm) z = fderiv ℝ f z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
  exact scalarChartLift_apply_inverse p f hw

end TamingCompatibility.ManifoldForms

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGeometricCoefficient
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)

lemma anti_ddc_apply_vector {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (u v : Space → Space) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (antiInvariantPart J (exteriorDerivative (complexDifferential J f)))
      (extChartAt Model p).symm z ![u z,v z] =
      fderiv ℝ (f ∘ (extChartAt Model p).symm) z (antiDdcVector J p u v z) := by
  rw [anti_ddc_chart_first_order J hf p hz]
  simp only [antiDdcVector,map_smul,smul_eq_mul]

variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma anti_ddc_radialSourceExtension [T2Space X]
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ D.domain) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hft : tsupport f ⊆ (extChartAt Model p).target)
    {z : Space} (hz : z ∈ D.domain) (hφz : φ z = 1) (j : Fin 2) :
    ManifoldForms.pullback (antiInvariantPart J (exteriorDerivative
        (complexDifferential J (scalarChartLift p f)))) (extChartAt Model p).symm z
        ![D.frame 0 z,D.frame (if j = 0 then 2 else 3) z] =
      RadialPotential.firstOrderSource (radialSourceExtension J p D hφ hc hφD j) f z := by
  rw [anti_ddc_apply_vector J p (scalarChartLift_smooth p hf hfc hft) _ _ (D.domain_subset hz),scalarChartLift_fderiv p f (D.domain_subset hz)]
  simp only [RadialPotential.firstOrderSource,radialSourceExtension,
    SchwartzCutoff.schwartz_apply,hφz,one_smul,radialSourceVector]

end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma complexDifferential_zero_of_eventually (J : AlmostComplexStructure X)
    {f : X → ℝ} {x : X} (hf : f =ᶠ[𝓝 x] fun _ => 0) : complexDifferential J f x = 0 := by
  have he := hf.mfderiv_eq (I := Model) (I' := 𝓘(ℝ,ℝ))
  rw [mfderiv_const] at he
  ext v
  change -(mfderiv Model 𝓘(ℝ,ℝ) f x) (J.endomorphism x (v 0)) = 0
  rw [he]
  change -(0:ℝ) = 0
  exact neg_zero

lemma anti_ddc_zero_off (J : AlmostComplexStructure X) (f : X → ℝ)
    {x : X} (hx : x ∉ tsupport f) :
    antiInvariantPart J (exteriorDerivative (complexDifferential J f)) x = 0 := by
  have hd : exteriorDerivative (complexDifferential J f) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    apply complexDifferential_zero_of_eventually J
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hy] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  ext v
  simp [antiInvariantPart,TamingCompatibility.jAction,hd]

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X) {α : TwoForm X} {ht : Tames α J}
  (D : Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)
variable {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)

lemma radialScalarSource_support (j : Fin 2) :
    tsupport (radialScalarSource J p D hφ hc hφD hf hfc j) ⊆ tsupport f :=
  RadialPotential.firstOrderSource_tsupport _ _

lemma radialPairSource_apply (z : Space) (j : Fin 2) :
    radialPairSource J p D hφ hc hφD hf hfc z j =
      RadialPotential.firstOrderSource (radialSourceExtension J p D hφ hc hφD j) f z := by
  fin_cases j <;> simp [radialPairSource,componentTest_apply,radialScalarSource,EuclideanSpace.single] <;> rfl

lemma radialPairSource_support :
    tsupport (radialPairSource J p D hφ hc hφD hf hfc) ⊆ tsupport f := by
  apply (tsupport_add _ _).trans
  apply union_subset
  · exact (GeometricHilbert.componentTest_support _ _).trans (radialScalarSource_support J p D hφ hc hφD hf hfc 0)
  · exact (GeometricHilbert.componentTest_support _ _).trans (radialScalarSource_support J p D hφ hc hφD hf hfc 1)

lemma anti_ddc_eq_manifoldTest [T2Space X] (hfD : tsupport f ⊆ D.domain)
    (hφone : ∀ z ∈ tsupport f, φ z = 1) :
    antiInvariantPart J (exteriorDerivative (complexDifferential J (scalarChartLift p f))) =
      manifoldTest J α ht p D (radialPairSource J p D hφ hc hφD hf hfc) := by
  let a := antiInvariantPart J (exteriorDerivative (complexDifferential J (scalarChartLift p f)))
  let q := radialPairSource J p D hφ hc hφD hf hfc
  have hqs : tsupport q ⊆ tsupport f := radialPairSource_support J p D hφ hc hφD hf hfc
  have hqt : tsupport q ⊆ D.domain := hqs.trans hfD
  have hft := hfD.trans D.domain_subset
  have has : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (scalarChartLift p f) := scalarChartLift_smooth p hf hfc hft
  have hchart {z : Space} (hz : z ∈ (extChartAt Model p).target) :
      ManifoldForms.pullback a (extChartAt Model p).symm z = coordinateTest J α ht p D q z := by
    by_cases hzf : z ∈ tsupport f
    · have hex := rawScalar_expansion J α ht p D (a := a) (antiInvariantPart_idempotent J _) (hfD hzf)
      change ManifoldForms.pullback a (extChartAt Model p).symm z = _ at hex
      rw [hex]
      have hc0 := anti_ddc_radialSourceExtension J p D hφ hc hφD hf hfc hft (hfD hzf) (hφone z hzf) 0
      have hc1 := anti_ddc_radialSourceExtension J p D hφ hc hφD hf hfc hft (hfD hzf) (hφone z hzf) 1
      change rawScalar J α ht p D a 2 z = _ at hc0
      change rawScalar J α ht p D a 3 z = _ at hc1
      simp only [coordinateTest,LocalMatrixOperator.frameTest,q,
        radialPairSource_apply,hc0,hc1]
    · have hd : fderiv ℝ f z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hzf (tsupport_fderiv_subset ℝ h))
      have hqz : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzf (hqs h))
      rw [show coordinateTest J α ht p D q z = 0 from LocalMatrixOperator.frameTest_zero hqz]
      ext v
      have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
      rw [hv]
      change ManifoldForms.pullback (antiInvariantPart J (exteriorDerivative
        (complexDifferential J (scalarChartLift p f)))) (extChartAt Model p).symm z ![v 0,v 1] = 0
      rw [anti_ddc_chart_first_order J has p hz,scalarChartLift_fderiv p f hz,hd]
      simp
  ext x v
  by_cases hxs : x ∈ (extChartAt Model p).source
  · have h := form_eq_of_chart_pullback p a (manifoldTest J α ht p D q) hxs (by
      exact (hchart ((extChartAt Model p).map_source hxs)).trans
        (pullback_manifoldTest J α ht p D hqt ((extChartAt Model p).map_source hxs)).symm)
    exact congrArg (fun b : Space [⋀^Fin 2]→L[ℝ] ℝ => b v) h
  · have hxf : x ∉ tsupport (scalarChartLift p f) := fun h =>
      hxs (scalarLiftSupport_subset p hft (scalarChartLift_tsupport p hfc hft h))
    have hz := anti_ddc_zero_off J (scalarChartLift p f) hxf
    have hm : manifoldTest J α ht p D q x = 0 := by
      have hh : chartLift p (coordinateTest J α ht p D q) x = 0 := by
        simp only [chartLift,ite_eq_right hxs]
      ext w
      simp [manifoldTest,antiInvariantPart,TamingCompatibility.jAction,hh]
    exact congrArg (fun b : Space [⋀^Fin 2]→L[ℝ] ℝ => b v) (hz.trans hm.symm)

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
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
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_complexLine (J : AlmostComplexStructure X) (β : TwoForm X) (p : X)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback β (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      eval β ((extChartAt Model p).symm y) (mfderiv Model Model (extChartAt Model p).symm y v)
        (J.endomorphism _ (mfderiv Model Model (extChartAt Model p).symm y v)) := by
  have hi := coordinateJ_intertwine J p hy v
  change (inverseChartEquiv p y hy).toContinuousLinearMap (coordinateJ J p y v) =
    J.endomorphism _ ((inverseChartEquiv p y hy).toContinuousLinearMap v) at hi
  rw [inverseChartEquiv_coe] at hi
  change β _ ((mfderiv Model Model (extChartAt Model p).symm y) ∘ ![v,coordinateJ J p y v]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hi

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianGeometricAssembly
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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
variable (W : Space → Space →L[ℝ] Space)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma smoothAnti_ddc_cutoffLog (p : A.centers)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hφone : ∀ z ∈ K, φ z = 1)
    {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hb : Metric.closedBall b (2*R) ⊆ K) :
    smoothAntiProjection A J α hs ht (smoothDdc J
      (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffLog_smooth W R hsp b)
        (HermitianRadial.translatedCutoffLog_compact W hR s b)
        (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hb).trans
          (hKD.trans (D p).domain_subset)))) =
      scalarTestLM A J α hs ht D p K hK hKD 0
        (HermitianRadial.logCutoffSourceSupported W (radialSourceExtension J p.val (D p) hφ hc hφD 0)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 0).smooth ⊤) hR hsp K b hb) +
      scalarTestLM A J α hs ht D p K hK hKD 1
        (HermitianRadial.logCutoffSourceSupported W (radialSourceExtension J p.val (D p) hφ hc hφD 1)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 1).smooth ⊤) hR hsp K b hb) := by
  apply Subtype.ext
  apply Subtype.ext
  have he := anti_ddc_eq_manifoldTest J p.val (D p) hφ hc hφD
    (HermitianRadial.translatedCutoffLog_smooth W R hsp b) (HermitianRadial.translatedCutoffLog_compact W hR s b)
    (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hb).trans hKD)
    (fun z hz => hφone z (hb (HermitianRadial.translatedCutoffLog_support W hR s b hz)))
  change antiInvariantPart J (exteriorDerivative (complexDifferential J _)) = _
  rw [he]
  change manifoldTest J α ht p.val (D p) (_ + _) = _
  rw [manifoldTest_add]
  rfl

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma smoothAnti_ddc_cutoffSqrt (p : A.centers)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hφone : ∀ z ∈ K, φ z = 1)
    {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hb : Metric.closedBall b (2*R) ⊆ K) :
    smoothAntiProjection A J α hs ht (smoothDdc J
      (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffSqrt_smooth W R hsp b)
        (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
        (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hb).trans
          (hKD.trans (D p).domain_subset)))) =
      scalarTestLM A J α hs ht D p K hK hKD 0
        (HermitianRadial.sqrtCutoffSourceSupported W (radialSourceExtension J p.val (D p) hφ hc hφD 0)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 0).smooth ⊤) hR hsp K b hb) +
      scalarTestLM A J α hs ht D p K hK hKD 1
        (HermitianRadial.sqrtCutoffSourceSupported W (radialSourceExtension J p.val (D p) hφ hc hφD 1)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 1).smooth ⊤) hR hsp K b hb) := by
  apply Subtype.ext
  apply Subtype.ext
  have he := anti_ddc_eq_manifoldTest J p.val (D p) hφ hc hφD
    (HermitianRadial.translatedCutoffSqrt_smooth W R hsp b) (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
    (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hb).trans hKD)
    (fun z hz => hφone z (hb (HermitianRadial.translatedCutoffSqrt_support W hR s b hz)))
  change antiInvariantPart J (exteriorDerivative (complexDifferential J _)) = _
  rw [he]
  change manifoldTest J α ht p.val (D p) (_ + _) = _
  rw [manifoldTest_add]
  rfl
end TamingCompatibility.GeometricHilbert.Hermitian

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

theorem geometric_cutoffLog_dual_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖antiEnergyDualLM A J α hs ht
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffLog_smooth W R hsr.1 b)
            (HermitianRadial.translatedCutoffLog_compact W hR s b)
            (((HermitianRadial.translatedCutoffLog_support W hR s b).trans (hcenters b hb)).trans
              (hKD.trans (D p).domain_subset)))))‖ ≤ C := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨C₀,hC₀,hzero⟩ := scalarEnergyDual_cutoffLog_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (V 0) ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hone⟩ := scalarEnergyDual_cutoffLog_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (V 1) ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro s hsr b hb
  rw [smoothAnti_ddc_cutoffLog A J α hs ht D W p hφ hc hφD K hK hKD hφone
    hR hsr.1 b (hcenters b hb),map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD 0
      (HermitianRadial.logCutoffSourceSupported W (V 0) ((V 0).smooth ⊤) hR hsr.1 K b (hcenters b hb))) _).trans
    (add_le_add (hzero 0 s hsr b hb) (hone 1 s hsr b hb))

include hD hW in

theorem geometric_cutoffSqrt_dual_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖antiEnergyDualLM A J α hs ht
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffSqrt_smooth W R hsr.1 b)
            (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
            (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans (hcenters b hb)).trans
              (hKD.trans (D p).domain_subset)))))‖ ≤ C := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨C₀,hC₀,hzero⟩ := scalarEnergyDual_cutoffSqrt_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (V 0) ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hone⟩ := scalarEnergyDual_cutoffSqrt_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (V 1) ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro s hsr b hb
  rw [smoothAnti_ddc_cutoffSqrt A J α hs ht D W p hφ hc hφD K hK hKD hφone
    hR hsr.1 b (hcenters b hb),map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD 0
      (HermitianRadial.sqrtCutoffSourceSupported W (V 0) ((V 0).smooth ⊤) hR hsr.1 K b (hcenters b hb))) _).trans
    (add_le_add (hzero 0 s hsr b hb) (hone 1 s hsr b hb))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Hermitian
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
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in
lemma chartLift_tsupport_subset [T2Space X] (p : X) {f : Space → ℝ}
    (hc : HasCompactSupport f) {K : Set Space} (hf : tsupport f ⊆ K)
    (hK : K ⊆ (extChartAt Model p).target) :
    tsupport (scalarChartLift p f) ⊆ (extChartAt Model p).symm '' K :=
  (scalarChartLift_tsupport p hc (hf.trans hK)).trans (image_mono hf)
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
variable (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

variable (D' : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D' p).source)
  (q : A.centers) (τ : 𝓢(Space,ℝ))
  {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
  (hψD : tsupport ψ ⊆ (D' q).domain)
  (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D' q).domain)
  (hτ : ∀ z ∈ K, τ z * coordinateWeight A q z = 1)
  (hψone : ∀ z ∈ K, ψ z = 1)
  (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
  (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hK hτ hψone hK₀ in
lemma logSource_dual_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R),
    ∀ b, ∀ hb : b ∈ K₀,
    ‖antiEnergyDualLM A J α hs ht
      (logSource A J α hs ht q.val (D' q) hψ hcψ hψD hR hsr.1 b
        ((hcenters b hb).trans hKD))‖ ≤ C := by
  let W := hermitianCenterExtension J q.val (D' q) hψ hcψ hψD
  exact geometric_cutoffLog_dual_bound A J α hs ht D' hD W (W.smooth ⊤)
    q τ hψ hcψ hψD K hK hKD hτ hψone R hR K₀ hK₀ hcenters

include hD hK hτ hψone hK₀ in
lemma sqrtSource_dual_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R),
    ∀ b, ∀ hb : b ∈ K₀,
    ‖antiEnergyDualLM A J α hs ht
      (sqrtSource A J α hs ht q.val (D' q) hψ hcψ hψD hR hsr.1 b
        ((hcenters b hb).trans hKD))‖ ≤ C := by
  let W := hermitianCenterExtension J q.val (D' q) hψ hcψ hψD
  exact geometric_cutoffSqrt_dual_bound A J α hs ht D' hD W (W.smooth ⊤)
    q τ hψ hcψ hψD K hK hKD hτ hψone R hR K₀ hK₀ hcenters
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactUniformBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Topology

theorem IsCompact.exists_uniform_monotone_bound {Y : Type*} [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) (P : Y → ℝ → Prop)
    (hmono : ∀ y a b, a ≤ b → P y a → P y b)
    (hlocal : ∀ q ∈ K, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 q, P y C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, P y C := by
  classical
  have hloc : ∀ q : K, ∃ C : ℝ, ∃ U : Set Y,
      0 ≤ C ∧ IsOpen U ∧ q.val ∈ U ∧ ∀ y ∈ U, P y C := by
    intro q
    obtain ⟨C,hC,hq⟩ := hlocal q.val q.property
    obtain ⟨U,hUP,hU,hqU⟩ := mem_nhds_iff.mp hq
    exact ⟨C,U,hC,hU,hqU,hUP⟩
  choose C U hC hU hqU hUP using hloc
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hqU ⟨y,hy⟩⟩)
  refine ⟨∑ q ∈ s, C q, Finset.sum_nonneg (fun q _ => hC q), ?_⟩
  intro y hy
  obtain ⟨q,hq,hyq⟩ := mem_iUnion₂.mp (hs hy)
  exact hmono y (C q) _ (Finset.single_le_sum (fun r _ => hC r) hq) (hUP q y hyq)

end


end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianUnitMetric
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
namespace TamingCompatibility.ManifoldVolume
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J)

lemma inverse_coordinates_eval (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (β : TwoForm X) (u : TangentSpace Model ((extChartAt Model p).symm z)) :
    ∃ v : Space,
      chartMetric J α p z v v = (hermitianMetric J α hs ht).inner _ u u ∧
      ManifoldForms.pullback β (extChartAt Model p).symm z ![v,coordinateJ J p z v] =
        eval β ((extChartAt Model p).symm z) u (J.endomorphism _ u) := by
  let L := inverseChartEquiv p z hz
  have he : mfderiv Model Model (extChartAt Model p).symm z (L.symm u) = u := by
    rw [← inverseChartEquiv_coe p z hz]
    exact L.apply_symm_apply u
  refine ⟨L.symm u,?_,?_⟩
  · rw [chartMetric_derivative J α p hz,he]
    rfl
  · rw [pullback_complexLine J β p hz,he]

lemma unitEvaluation_lower_of_chart (p : X) {K : Set Space} {c : ℝ}
    (β : TwoForm X) (hβ : IsSmooth β)
    (hbound : ∀ z ∈ K, ∀ v : Space, chartMetric J α p z v v = 1 →
      c ≤ ManifoldForms.pullback β (extChartAt Model p).symm z ![v,coordinateJ J p z v])
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source)
    (hzK : extChartAt Model p u.val.proj ∈ K) :
    c ≤ unitEvaluation J (hermitianMetric J α hs ht) β hβ u := by
  let z := extChartAt Model p u.val.proj
  have hz : z ∈ (extChartAt Model p).target := (extChartAt Model p).map_source hu
  have hb : ∀ w : TangentSpace Model ((extChartAt Model p).symm z),
      (hermitianMetric J α hs ht).inner _ w w = 1 →
      c ≤ eval β ((extChartAt Model p).symm z) w (J.endomorphism _ w) := by
    intro w hw
    obtain ⟨v,hv,he⟩ := inverse_coordinates_eval J α hs ht p hz β w
    exact he ▸ hbound z hzK v (hv.trans hw)
  have hbase : (extChartAt Model p).symm z = u.val.proj := (extChartAt Model p).left_inv hu
  rw [hbase] at hb
  exact hb u.val.2 u.property
end TamingCompatibility.ManifoldVolume

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCombinedBounds
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in
lemma combinedForm_chart_lower (hR1 : 2*R ≤ 1) (a δ : ℝ) (ha : 0 ≤ a)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hpos : ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < δ → ∀ v : Space,
      0 ≤ ManifoldForms.pullback
        (combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v])
    (L : Set Space) (hL : IsCompact L) (hLU : L ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ L, ∀ v : Space, chartMetric J α p.val y v v = 1 →
      -C ≤ ManifoldForms.pullback
        (combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
  obtain ⟨C₀,hC₀,hlog⟩ := logForm_far_uniform
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters L hL hLU δ hδ
  obtain ⟨C₁,hC₁,hsqrt⟩ := sqrtForm_far_uniform
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 L hL hLU δ hδ
  refine ⟨C₀+a*C₁,by positivity,?_⟩
  intro s hsr b hb y hy v hv
  by_cases hnear : s+‖y-b‖ < δ
  · have hyK : y ∈ K := hcenters b hb (by
      rw [Metric.mem_closedBall,dist_eq_norm]
      linarith [hsr.1])
    exact (neg_nonpos.mpr (by positivity) : -(C₀+a*C₁) ≤ 0).trans (hpos s hsr b hb y hyK hnear v)
  · have hl := hlog s hsr b hb y hy (le_of_not_gt hnear) v hv
    have hh := hsqrt s hsr b hb y hy (le_of_not_gt hnear) v hv
    have hl' := (neg_le_neg hl).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le _)
    have hh' := mul_le_mul_of_nonneg_left ((neg_le_neg hh).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le _)) ha
    calc
      -(C₀+a*C₁) = -C₀+a*(-C₁) := by ring
      _ ≤ _ := add_le_add hl' hh'
end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianOff
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

variable (q : A.centers) (σ : 𝓢(Space,ℝ))
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D q).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D q).domain)
    (hσ : ∀ z ∈ K, σ z * coordinateWeight A q z = 1)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (L : Set Space) (hL : IsCompact L) (hLU : L ⊆ U)
    (hoff : ∀ z ∈ U, (extChartAt Model p.val).symm z ∉ (extChartAt Model q.val).symm '' K)

include hD hH hweak hB hdual hK hσ hφone hK₀ hU hUD hτ hρ hL hLU hoff in

lemma logForm_off_source_uniform : ∃ C : ℝ, 0 ≤ C ∧
    ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
    ∀ y ∈ L, ∀ v : Space, chartMetric J α p.val y v v = 1 →
    ‖ManifoldForms.pullback
      (logForm A J α hs ht H Gs q.val (D q) hφ hc hφD hR hsr.1 b
        ((hcenters b hb).trans hKD)).val
      (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := logSource_dual_uniform A J α hs ht D hD q σ hφ hc hφD
    K hK hKD hσ hφone R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hobserver⟩ := correctedDdc_off_source_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ L hL hLU
  refine ⟨C₁*C₀,by positivity,?_⟩
  intro s hsr b hb y hy v hv
  have hsupport : tsupport (scalarChartLift q.val
      (HermitianRadial.translatedCutoffLog
        (hermitianCenterExtension J q.val (D q) hφ hc hφD) R s b)) ⊆
      (extChartAt Model q.val).symm '' K :=
    chartLift_tsupport_subset q.val (HermitianRadial.translatedCutoffLog_compact _ hR s b)
      ((HermitianRadial.translatedCutoffLog_support _ hR s b).trans (hcenters b hb))
      (hKD.trans (D q).domain_subset)
  have he := hobserver y hy v hv _
    (scalarChartLift_smooth q.val
      (HermitianRadial.translatedCutoffLog_smooth _ R hsr.1 b)
      (HermitianRadial.translatedCutoffLog_compact _ hR s b)
      (((HermitianRadial.translatedCutoffLog_support _ hR s b).trans
        ((hcenters b hb).trans hKD)).trans (D q).domain_subset))
    (fun z hz h => hoff z hz (hsupport h))
  exact he.trans (mul_le_mul_of_nonneg_left (hsource s hsr b hb) hC₁)

include hD hH hweak hB hdual hK hσ hφone hK₀ hU hUD hτ hρ hL hLU hoff in

lemma sqrtForm_off_source_uniform : ∃ C : ℝ, 0 ≤ C ∧
    ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
    ∀ y ∈ L, ∀ v : Space, chartMetric J α p.val y v v = 1 →
    ‖ManifoldForms.pullback
      (sqrtForm A J α hs ht H Gs q.val (D q) hφ hc hφD hR hsr.1 b
        ((hcenters b hb).trans hKD)).val
      (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := sqrtSource_dual_uniform A J α hs ht D hD q σ hφ hc hφD
    K hK hKD hσ hφone R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hobserver⟩ := correctedDdc_off_source_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ L hL hLU
  refine ⟨C₁*C₀,by positivity,?_⟩
  intro s hsr b hb y hy v hv
  have hsupport : tsupport (scalarChartLift q.val
      (HermitianRadial.translatedCutoffSqrt
        (hermitianCenterExtension J q.val (D q) hφ hc hφD) R s b)) ⊆
      (extChartAt Model q.val).symm '' K :=
    chartLift_tsupport_subset q.val (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
      ((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans (hcenters b hb))
      (hKD.trans (D q).domain_subset)
  have he := hobserver y hy v hv _
    (scalarChartLift_smooth q.val
      (HermitianRadial.translatedCutoffSqrt_smooth _ R hsr.1 b)
      (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
      (((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans
        ((hcenters b hb).trans hKD)).trans (D q).domain_subset))
    (fun z hz h => hoff z hz (hsupport h))
  exact he.trans (mul_le_mul_of_nonneg_left (hsource s hsr b hb) hC₁)
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume Set Filter
open scoped Manifold ContDiff Topology SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_coordinate_observer (p : A.centers) {z : Space} (hz : z ∈ (D p).domain)
    (hwz : coordinateWeight A p z ≠ 0) :
    ∃ τ ρ : 𝓢(Space,ℝ), ∃ U : Set Space,
      IsOpen U ∧ z ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ y ∈ U, τ y * coordinateWeight A p y = 1) ∧
      (∀ y ∈ U, ρ y = chartDensity J α p.val y) := by
  obtain ⟨τ,-,-,V,hV,hzV,hVD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hz hwz
  obtain ⟨ζ,hζ,hζV,U,hU,hzU,hUV,hζone⟩ := SchwartzCutoff.exists_one_near hV hzV
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset)
    (ζ.smooth ⊤) hζ (hζV.trans hVD)
  refine ⟨τ,ρ,U,hU,hzU,hUV.trans hVD,fun y hy => hτ y (hUV hy),?_⟩
  intro y hy
  simp only [ρ,SchwartzCutoff.schwartz_apply,hζone y hy,one_smul]

include hD in
include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma exists_observer_at {O : Set X} (hO : IsOpen O) {x : X} (hx : x ∈ O) :
    ∃ p : A.centers, x ∈ (extChartAt Model p.val).source ∧
      ∃ τ ρ : 𝓢(Space,ℝ), ∃ U : Set Space,
      IsOpen U ∧ extChartAt Model p.val x ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ y ∈ U, τ y * coordinateWeight A p y = 1) ∧
      (∀ y ∈ U, ρ y = chartDensity J α p.val y) ∧
      (∀ y ∈ U, (extChartAt Model p.val).symm y ∈ O) := by
  obtain ⟨p,hp,hz⟩ := exists_nonzero_weight_chart A J α ht D hD x
  have hxp : x ∈ (extChartAt Model p.val).source :=
    (D p).source_subset (hD p (subset_closure hp))
  have hwz : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxp] using hp
  obtain ⟨τ,ρ,V,hV,hzV,hVD,hτ,hρ⟩ := exists_coordinate_observer A J α hs ht D p hz hwz
  have hpre : IsOpen ((extChartAt Model p.val).target ∩ (extChartAt Model p.val).symm ⁻¹' O) :=
    (continuousOn_extChartAt_symm p.val).isOpen_inter_preimage (isOpen_extChartAt_target p.val) hO
  refine ⟨p,hxp,τ,ρ,V ∩ ((extChartAt Model p.val).target ∩ (extChartAt Model p.val).symm ⁻¹' O),
    hV.inter hpre,⟨hzV,(D p).domain_subset hz,?_⟩,
    fun _ hy => hVD hy.1,fun y hy => hτ y hy.1,fun y hy => hρ y hy.1,fun _ hy => hy.2.2⟩
  simpa only [mem_preimage,(extChartAt Model p.val).left_inv hxp] using hx
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_ChartCompactNeighborhood
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
namespace TamingCompatibility.GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in

lemma exists_compact_observer_neighborhood (p : X) {x : X}
    (hx : x ∈ (extChartAt Model p).source) {U : Set Space} (hU : IsOpen U)
    (hxU : extChartAt Model p x ∈ U) :
    ∃ K : Set Space, IsCompact K ∧ K ⊆ U ∧
      ∀ᶠ y in 𝓝 x, y ∈ (extChartAt Model p).source ∧ extChartAt Model p y ∈ K := by
  obtain ⟨K,hK,hzK,hKU⟩ := exists_compact_between
    (isCompact_singleton (x := extChartAt Model p x)) hU (singleton_subset_iff.mpr hxU)
  have hc := (continuousOn_extChartAt p).continuousAt ((isOpen_extChartAt_source p).mem_nhds hx)
  have hmem : K ∈ 𝓝 (extChartAt Model p x) := mem_of_superset
    (isOpen_interior.mem_nhds (hzK (mem_singleton _))) interior_subset
  refine ⟨K,hK,hKU,?_⟩
  filter_upwards [(isOpen_extChartAt_source p).mem_nhds hx,hc.eventually hmem] with y hy hz
  exact ⟨hy,hz⟩
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldVolume
open ManifoldForms ManifoldHodge GeometricChart Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

lemma compact_family_unit_lower {I : Type*} (β : I → smoothForms X 2)
    (hlocal : ∀ x : X, ∃ p : X, ∃ K : Set Space, ∃ C : ℝ,
      0 ≤ C ∧ (∀ᶠ y in 𝓝 x, y ∈ (extChartAt Model p).source ∧ extChartAt Model p y ∈ K) ∧
      ∀ i : I, ∀ z ∈ K, ∀ v : Space, chartMetric J α p z v v = 1 →
        -C ≤ ManifoldForms.pullback (β i).val (extChartAt Model p).symm z ![v,coordinateJ J p z v]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : I, ∀ u : MetricUnit (hermitianMetric J α hs ht),
      -C ≤ unitEvaluation J (hermitianMetric J α hs ht) (β i).val (β i).property u := by
  let P : X → ℝ → Prop := fun x C => ∀ i : I, ∀ u : MetricUnit (hermitianMetric J α hs ht),
    u.val.proj = x → -C ≤ unitEvaluation J (hermitianMetric J α hs ht) (β i).val (β i).property u
  have hmono : ∀ x a b, a ≤ b → P x a → P x b := by
    intro x a b hab hx i u hu
    exact (neg_le_neg hab).trans (hx i u hu)
  have hloc : ∀ x ∈ (univ : Set X), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, P y C := by
    intro x _
    obtain ⟨p,K,C,hC,hN,hbound⟩ := hlocal x
    refine ⟨C,hC,?_⟩
    filter_upwards [hN] with y hy
    intro i u hu
    apply unitEvaluation_lower_of_chart J α hs ht p (β i).val (β i).property (hbound i) u
    · simpa only [hu] using hy.1
    · simpa only [hu] using hy.2
  obtain ⟨C,hC,hbound⟩ := _root_.OAI.IsCompact.exists_uniform_monotone_bound isCompact_univ P hmono hloc
  exact ⟨C,hC,fun i u => hbound u.val.proj (mem_univ _) i u rfl⟩
end TamingCompatibility.ManifoldVolume

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianGlobalLower
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
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in

theorem combinedForm_global_lower_oai (hR1 : 2*R ≤ 1) (a δ : ℝ) (ha : 0 ≤ a)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hpos : ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < δ → ∀ v : Space,
      0 ≤ ManifoldForms.pullback
        (combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ u : MetricUnit (hermitianMetric J α hs ht),
      let β := combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD));
      -C ≤ unitEvaluation J (hermitianMetric J α hs ht) β.val β.property u := by
  let I := {s : ℝ // s ∈ Ioc (0:ℝ) (2*R)} × K₀
  let β : I → smoothForms X 2 := fun i => combinedForm A J α hs ht H Gs p.val (D p)
    hφ hc hφD a hR i.1.property.1 i.2.val
      ((hcenters i.2.val i.2.property).trans (hKU.trans hUD))
  have hlocal : ∀ x : X, ∃ q : X, ∃ L : Set Space, ∃ C : ℝ,
      0 ≤ C ∧ (∀ᶠ y in 𝓝 x, y ∈ (extChartAt Model q).source ∧ extChartAt Model q y ∈ L) ∧
      ∀ i : I, ∀ z ∈ L, ∀ v : Space, chartMetric J α q z v v = 1 →
        -C ≤ ManifoldForms.pullback (β i).val (extChartAt Model q).symm z ![v,coordinateJ J q z v] := by
    intro x
    by_cases hx : x ∈ (extChartAt Model p.val).symm '' K
    · obtain ⟨z,hz,rfl⟩ := hx
      have hzT := (D p).domain_subset (hUD (hKU hz))
      have hxsrc := (extChartAt Model p.val).map_target hzT
      obtain ⟨L,hL,hLU,hN⟩ := exists_compact_observer_neighborhood p.val hxsrc hU
        (by simpa only [(extChartAt Model p.val).right_inv hzT] using hKU hz)
      obtain ⟨C,hC,hbound⟩ := combinedForm_chart_lower
        A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
        hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 a δ ha hδ hδR hpos L hL hLU
      exact ⟨p.val,L,C,hC,hN,fun i y hy v hv => hbound i.1.val i.1.property i.2.val i.2.property y hy v hv⟩
    · have hclosed : _root_.IsClosed ((extChartAt Model p.val).symm '' K) :=
        (hK.image_of_continuousOn ((continuousOn_extChartAt_symm p.val).mono
          (hKU.trans (hUD.trans (D p).domain_subset)))).isClosed
      obtain ⟨q,hxq,τ',ρ',V,hV,hxV,hVD,hτ',hρ',hoff⟩ :=
        exists_observer_at A J α hs ht D hD hclosed.isOpen_compl hx
      obtain ⟨L,hL,hLV,hN⟩ := exists_compact_observer_neighborhood q.val hxq hV hxV
      obtain ⟨C₀,hC₀,hlog⟩ := logForm_off_source_uniform
        A J α hs ht D hD H Gs hH hweak B hB hdual p τ hφ hc hφD
        K hK (hKU.trans hUD) (fun z hz => hτ z (hKU hz)) hφone R hR K₀ hK₀ hcenters
        q τ' ρ' V hV hVD hτ' hρ' L hL hLV hoff
      obtain ⟨C₁,hC₁,hsqrt⟩ := sqrtForm_off_source_uniform
        A J α hs ht D hD H Gs hH hweak B hB hdual p τ hφ hc hφD
        K hK (hKU.trans hUD) (fun z hz => hτ z (hKU hz)) hφone R hR K₀ hK₀ hcenters
        q τ' ρ' V hV hVD hτ' hρ' L hL hLV hoff
      refine ⟨q.val,L,C₀+a*C₁,by positivity,hN,?_⟩
      intro i z hz v hv
      have hl := hlog i.1.val i.1.property i.2.val i.2.property z hz v hv
      have hh := hsqrt i.1.val i.1.property i.2.val i.2.property z hz v hv
      have hl' := (neg_le_neg hl).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le _)
      have hh' := mul_le_mul_of_nonneg_left ((neg_le_neg hh).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le _)) ha
      calc
        -(C₀+a*C₁) = -C₀+a*(-C₁) := by ring
        _ ≤ _ := add_le_add hl' hh'
  obtain ⟨C,hC,hbound⟩ := compact_family_unit_lower J α hs ht β hlocal
  exact ⟨C,hC,fun s hsr b hb u => hbound (⟨s,hsr⟩,⟨b,hb⟩) u⟩
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.Hermitian.combinedForm_global_lower_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.Hermitian.combinedForm_global_lower_oai.{u_1}
