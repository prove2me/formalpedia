-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_sqrtSource_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:38:02.929051+00:00
-- url     : https://prove2.me/submissions/a7e01282-8a28-4205-aa1c-6ee88137318d

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_scalarCorrection_sqrtError_estimate
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_scalarCorrection_all_scales

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

lemma sqrtGradientProfile_scale {r s : ℝ} (hr : 0 < r) (z v : E) :
    sqrtGradientProfile (r*s) (r • z) v = sqrtGradientProfile s z v := by
  simp only [sqrtGradientProfile,norm_smul,Real.norm_of_nonneg (le_of_lt hr),real_inner_smul_left]
  rw [show (r*s)^2+(r*‖z‖)^2 = r^2*(s^2+‖z‖^2) by ring,
    Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq_eq_abs,abs_of_pos hr,mul_inv_rev]
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_DyadicCorrectionProgress
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped BigOperators

variable {V : Type*} [SeminormedAddCommGroup V]

lemma dyadic_count_bound {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hscale : a*(2:ℝ)^N ≤ 2) :
    (N:ℝ) ≤ 1 + |Real.log a| / Real.log 2 := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hpow : 0 < (2:ℝ)^N := by positivity
  have h := Real.log_le_log (mul_pos ha hpow) hscale
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hpow),Real.log_pow] at h
  have he : 1 + |Real.log a| / Real.log 2 =
      (Real.log 2 + |Real.log a|)/Real.log 2 := by field_simp
  rw [he]
  apply (le_div_iff₀ hlog).mpr
  nlinarith [neg_le_abs (Real.log a)]

end TamingCompatibility.RadialPotential

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

lemma sum_dyadic_cube_le {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    ∑ j ∈ Finset.range N, (s*2^j)^3 ≤ (s*2^N)^3 := by
  induction N with
  | zero => simpa using pow_nonneg hs 3
  | succ N ih =>
    rw [Finset.sum_range_succ,pow_succ (2:ℝ)]
    have hp : 0 ≤ (s*2^N)^3 := by positivity
    nlinarith

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
open scoped BigOperators

lemma scalar_dyadic_mixed_log_sum (w : ℕ → ℝ) (N : ℕ) {s a C : ℝ}
    (hs : 0 < s) (_ha : 0 ≤ a) (hC : 0 ≤ C) (hw0 : ∀ j, 0 ≤ w j)
    (hscale : s*2^N ≤ 2)
    (hnear : ∀ j, w j ≤ C)
    (hoff : ∀ j, s*2^j ≤ a → w j ≤ C*(s*2^j)^3/a^3) :
    ∑ j ∈ Finset.range N, w j ≤ C*(9+|Real.log (max s a)|/Real.log 2) := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  by_cases has : a ≤ s
  · rw [max_eq_left has]
    calc
      _ ≤ ∑ _j ∈ Finset.range N, C := Finset.sum_le_sum (fun j _ => hnear j)
      _ = C*(N:ℝ) := by simp <;> ring
      _ ≤ C*(1+|Real.log s|/Real.log 2) := mul_le_mul_of_nonneg_left (dyadic_count_bound hs N hscale) hC
      _ ≤ _ := by gcongr; norm_num
  · have hsa : s < a := lt_of_not_ge has
    have ha' : 0 < a := hs.trans hsa
    rw [max_eq_right hsa.le]
    obtain ⟨n,hn1,hn2⟩ := exists_nat_pow_near ((one_le_div hs).mpr hsa.le) (by norm_num : (1:ℝ) < 2)
    let k := n+1
    have hbasele : s*2^k ≤ 2*a := by
      dsimp only [k]
      rw [pow_succ]
      have hn := (le_div_iff₀ hs).mp hn1
      nlinarith
    have hbaselt : a < s*2^k := by
      have hn := (div_lt_iff₀ hs).mp hn2
      simpa only [mul_comm] using hn
    have hinside : ∀ j < k, s*2^j ≤ a := by
      intro j hj
      have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show j ≤ n by omega)
      have hn := (le_div_iff₀ hs).mp hn1
      nlinarith [mul_le_mul_of_nonneg_left hpow hs.le]
    have hi : ∑ j ∈ Finset.range k, w j ≤ 8*C := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, C*(s*2^j)^3/a^3 :=
          Finset.sum_le_sum (fun j hj => hoff j (hinside j (Finset.mem_range.mp hj)))
        _ = (C/a^3)*∑ j ∈ Finset.range k, (s*2^j)^3 := by rw [Finset.mul_sum]; congr 1; ext j; ring
        _ ≤ (C/a^3)*(s*2^k)^3 :=
          mul_le_mul_of_nonneg_left (sum_dyadic_cube_le hs.le k) (by positivity)
        _ ≤ (C/a^3)*(2*a)^3 := by gcongr
        _ = _ := by field_simp <;> ring
    by_cases hNk : N ≤ k
    · have he : ∑ j ∈ Finset.range N, w j ≤ ∑ j ∈ Finset.range k, w j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNk) (fun j _ _ => hw0 j)
      apply (he.trans hi).trans
      have hpos : 0 ≤ |Real.log a|/Real.log 2 := by positivity
      nlinarith [mul_nonneg hC hpos]
    · have hkN : k ≤ N := by omega
      have htScale : a*2^(N-k) ≤ 2 := by
        calc
          _ ≤ (s*2^k)*2^(N-k) := mul_le_mul_of_nonneg_right hbaselt.le (by positivity)
          _ = s*2^N := by rw [mul_assoc,← pow_add,Nat.add_sub_of_le hkN]
          _ ≤ _ := hscale
      have ht : ∑ j ∈ Finset.range (N-k), w (k+j) ≤ C*(1+|Real.log a|/Real.log 2) := by
        calc
          _ ≤ ∑ _j ∈ Finset.range (N-k), C := Finset.sum_le_sum (fun j _ => hnear (k+j))
          _ = C*((N-k:ℕ):ℝ) := by simp <;> ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_count_bound ha' (N-k) htScale) hC
      calc
        _ = (∑ j ∈ Finset.range k, w j) + ∑ j ∈ Finset.range (N-k), w (k+j) := by
          simpa only [Nat.add_sub_of_le hkN] using (Finset.sum_range_add w k (N-k))
        _ ≤ 8*C+C*(1+|Real.log a|/Real.log 2) := add_le_add hi ht
        _ = _ := by ring

variable {V : Type*} [SeminormedAddCommGroup V]

lemma dyadic_mixed_log_bound (v₀ : V) (v : ℕ → V) (N : ℕ) {s a C : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hC : 0 ≤ C) (hscale : s*2^N ≤ 2)
    (h₀ : ‖v₀‖ ≤ C)
    (hnear : ∀ j < N, ‖v j‖ ≤ C)
    (hoff : ∀ j < N, s*2^j ≤ a → ‖v j‖ ≤ C*(s*2^j)^3/a^3) :
    ‖v₀ + ∑ j ∈ Finset.range N, v j‖ ≤ C*(10+|Real.log (max s a)|/Real.log 2) := by
  let w : ℕ → ℝ := fun j => if j < N then ‖v j‖ else 0
  have hw0 : ∀ j, 0 ≤ w j := by intro j; dsimp only [w]; split_ifs <;> positivity
  have hwn : ∀ j, w j ≤ C := by
    intro j
    dsimp only [w]
    split_ifs with hj
    · exact hnear j hj
    · exact hC
  have hwo : ∀ j, s*2^j ≤ a → w j ≤ C*(s*2^j)^3/a^3 := by
    intro j hj
    dsimp only [w]
    split_ifs with hjN
    · exact hoff j hjN hj
    · positivity
  have hsum := scalar_dyadic_mixed_log_sum w N hs ha hC hw0 hscale hwn hwo
  have he : ∑ j ∈ Finset.range N, w j = ∑ j ∈ Finset.range N, ‖v j‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [w,ite_eq_left (Finset.mem_range.mp hj)]
  rw [he] at hsum
  calc
    _ ≤ ‖v₀‖ + ‖∑ j ∈ Finset.range N, v j‖ := norm_add_le _ _
    _ ≤ ‖v₀‖ + ∑ j ∈ Finset.range N, ‖v j‖ := add_le_add (le_refl _) (norm_sum_le _ _)
    _ ≤ C+C*(9+|Real.log (max s a)|/Real.log 2) := add_le_add h₀ hsum
    _ = _ := by ring

end TamingCompatibility.RadialPotential

end
end

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialObserverScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential

lemma observerScale_properties {δ c d D : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hd : 0 ≤ d) (hdD : d ≤ D) :
    0 ≤ observerScale δ c d ∧ observerScale δ c d < δ ∧
    (5+c)*observerScale δ c d ≤ d ∧
    1 ≤ max (5+c) (2*D/δ) ∧ d ≤ max (5+c) (2*D/δ)*observerScale δ c d := by
  have hc5 : 0 < 5+c := by linarith
  have hC : 1 ≤ max (5+c) (2*D/δ) := (by linarith : (1:ℝ) ≤ 5+c).trans (le_max_left _ _)
  have ht0 : 0 ≤ observerScale δ c d := le_min (by positivity) (by positivity)
  refine ⟨ht0,(min_le_left _ _).trans_lt (by linarith),?_,hC,?_⟩
  · calc
      _ ≤ (5+c)*(d/(5+c)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc5.le
      _ = d := by field_simp
  · unfold observerScale
    by_cases h : δ/2 ≤ d/(5+c)
    · rw [min_eq_left h]
      calc
        d ≤ D := hdD
        _ = (2*D/δ)*(δ/2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    · rw [min_eq_right (le_of_not_ge h)]
      calc
        d = (5+c)*(d/(5+c)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

lemma observerScale_le_dist {δ c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    observerScale δ c d ≤ d := by
  apply (min_le_right _ _).trans
  exact div_le_self hd (by linarith)

lemma log_abs_comparison {u v L : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hvLu : v ≤ L*u) (hL : 1 ≤ L) :
    |Real.log u| ≤ |Real.log v|+Real.log L := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hv : 0 < v := hu.trans_le huv
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have h1 : Real.log u ≤ Real.log v := Real.log_le_log hu huv
  have h2 : Real.log v ≤ Real.log L+Real.log u := by
    simpa only [Real.log_mul hL0.ne' hu.ne'] using Real.log_le_log hv hvLu
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs (Real.log v)]
  · linarith [le_abs_self (Real.log v)]

lemma log_observer_to_distance {s t d L C : ℝ} (hs : 0 < s)
    (ht : 0 ≤ t) (htd : t ≤ d) (hL : 1 ≤ L) (hdt : d ≤ L*t) (hC : 0 ≤ C) :
    C*(10+|Real.log (max s t)|/Real.log 2) ≤
      (C*(10+Real.log (2*L)/Real.log 2+1/Real.log 2))*(1+|Real.log (s+d)|) := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hd : 0 ≤ d := ht.trans htd
  have hu : 0 < max s t := hs.trans_le (le_max_left _ _)
  have huv : max s t ≤ s+d := max_le (by linarith) (by linarith)
  have hv : s+d ≤ (2*L)*max s t := by
    have hsL : s ≤ L*s := by nlinarith
    have hs' : L*s ≤ L*max s t := mul_le_mul_of_nonneg_left (le_max_left _ _) hL0.le
    have ht' : L*t ≤ L*max s t := mul_le_mul_of_nonneg_left (le_max_right _ _) hL0.le
    nlinarith
  have h2L : 1 ≤ 2*L := by linarith
  have hcomp := log_abs_comparison hu huv hv h2L
  have hlog2L : 0 ≤ Real.log (2*L) := Real.log_nonneg h2L
  calc
    _ ≤ C*(10+(|Real.log (s+d)|+Real.log (2*L))/Real.log 2) := by gcongr
    _ ≤ C*(10+(|Real.log (s+d)|+Real.log (2*L))/Real.log 2) +
        C*((10+Real.log (2*L)/Real.log 2)*|Real.log (s+d)|+1/Real.log 2) := by
      apply le_add_of_nonneg_right
      positivity
    _ = _ := by ring

end TamingCompatibility.RadialPotential


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

lemma hermitianSqrtGradient_scale (K : E →L[ℝ] E) {r s : ℝ} (hr : 0 < r) (z v : E) :
    hermitianSqrtGradientProfile K (r*s) (r • z) v = hermitianSqrtGradientProfile K s z v := by
  simp only [hermitianSqrtGradient_eq,map_smul]
  exact sqrtGradientProfile_scale hr _ _

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

lemma firstOrderSource_cutoffSqrt (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (z : E) :
    firstOrderSource V (cutoffSqrtPotential K R s) z =
      scaledCutoff R z * hermitianSqrtGradientProfile K s z (V z) +
      hermitianSqrtPotential K s z * fderiv ℝ (scaledCutoff R) z (V z) := by
  change fderiv ℝ (fun x => scaledCutoff R x * hermitianSqrtPotential K s x) z (V z) = _
  rw [fderiv_fun_mul ((scaledCutoff_smooth R).differentiable (by simp) z)
      ((hermitianSqrtPotential_smooth K hs).differentiable (by simp) z)]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  rw [← hermitianSqrtGradient_eq_fderiv K hs]

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

lemma variableSqrtProfile_smooth (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ) (h0 : (0:E) ∉ tsupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => variableSqrtProfile W χ a V q.1 q.2) := by
  unfold variableSqrtProfile
  refine cutoff_parameter_smooth χ hχ h0
    (fun (p : ℝ × ℝ × E) z => a (p.2.1•z) * hermitianSqrtGradientProfile (W p.2.2) p.1 z
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
  exact (ha.comp hscale).contDiffAt.mul (((hden.contDiffAt.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne').mul hnum.contDiffAt)

lemma variableSqrtProfile_derivatives_bounded (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (h0 : (0:E) ∉ tsupport χ) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) R, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (variableSqrtProfile W χ a V (t,r,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_cutoff_derivatives_bounded χ hχc
    (fun (p : ℝ × ℝ × E) z => a (p.2.1•z) * hermitianSqrtGradientProfile (W p.2.2) p.1 z
      (V (p.2.2+p.2.1•z)))
    (variableSqrtProfile_smooth W χ a V hW hχ h0 ha hV)
    (isCompact_Icc.prod (isCompact_Icc.prod hK)) n
  exact ⟨C,hC,fun t ht r hr b hb z => h (t,r,b) ⟨ht,hr,hb⟩ z⟩

variable [HasContDiffBump E]

lemma variableSqrtProfile_shell_scale (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {r s : ℝ} (hr : 0 < r) (b z : E) :
    shellCutoff r (r•z) * (a (r•z) * hermitianSqrtGradientProfile (W b) s (r•z) (V (b+r•z))) =
      variableSqrtProfile W (shellCutoff 1) a V (s/r,r,b) z := by
  rw [shellCutoff_scale hr.ne']
  have h := hermitianSqrtGradient_scale (W b) hr (s := s/r) z (V (b+r•z))
  rw [mul_div_cancel₀ s hr.ne'] at h
  exact congrArg (fun x => shellCutoff 1 z * (a (r•z) * x)) h

end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma innerSqrtProfile_smooth (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun q : (ℝ × E) × E => variableSqrtProfile W χ a V (1,q.1.1,q.1.2) q.2) := by
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
    (((hden.sqrt (fun q => (hpos q).ne')).inv
      (fun q => (Real.sqrt_pos.mpr (hpos q)).ne')).mul hnum))

lemma innerSqrtProfile_derivatives_bounded (W : E → E →L[ℝ] E) (χ a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) R, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (variableSqrtProfile W χ a V (1,r,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_cutoff_derivatives_bounded χ hχc
    (fun (p : ℝ × E) z => a (p.1 • z) * hermitianSqrtGradientProfile (W p.2) 1 z (V (p.2 + p.1 • z)))
    (innerSqrtProfile_smooth W χ a V hW hχ ha hV) (isCompact_Icc.prod hK) n
  exact ⟨C,hC,fun r hr b hb z => h (r,b) ⟨hr,hb⟩ z⟩

variable [HasContDiffBump E]

lemma variableSqrtProfile_inner_scale (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b z : E) :
    scaledCutoff s (s • z) * (a (s • z) * hermitianSqrtGradientProfile (W b) s (s • z) (V (b+s•z))) =
      variableSqrtProfile W (scaledCutoff 1) a V (1,s,b) z := by
  have hc : scaledCutoff s (s • z) = scaledCutoff 1 z := by
    simpa using scaledCutoff_scale hs.ne' 1 z
  rw [hc]
  have h := hermitianSqrtGradient_scale (W b) hs (s := 1) z (V (b+s•z))
  rw [mul_one] at h
  exact congrArg (fun x => scaledCutoff 1 z * (a (s • z) * x)) h
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
lemma sqrtShell_eq_normalized (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {r s : ℝ} (hr : 0 < r) (b x : E) :
    shellCutoff r x * sqrtSingularSource W a V s b x =
      variableSqrtProfile W (shellCutoff 1) a V (s/r,r,b) (r⁻¹ • (x-0)) := by
  have h := variableSqrtProfile_shell_scale W a V (s := s) hr b (r⁻¹ • x)
  simpa only [sqrtSingularSource,sub_zero,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using h

omit [ProperSpace E] in
lemma sqrtInner_eq_normalized (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b x : E) :
    scaledCutoff s x * sqrtSingularSource W a V s b x =
      variableSqrtProfile W (scaledCutoff 1) a V (1,s,b) (s⁻¹ • (x-0)) := by
  have h := variableSqrtProfile_inner_scale W a V hs b (s⁻¹ • x)
  simpa only [sqrtSingularSource,sub_zero,smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using h

lemma sqrtShell_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (fun z => shellCutoff r z * sqrtSingularSource W a V s b z) x‖ ≤
        C / r^n := by
  obtain ⟨C,hC,hbound⟩ := variableSqrtProfile_derivatives_bounded W (shellCutoff 1) a V
    hW (shellCutoff_smooth _) (shellCutoff_compact (by norm_num))
    (shellCutoff_origin_not_tsupport (by norm_num)) ha hV hK R n
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hb x
  have hsr : s/r ∈ Icc (0:ℝ) 1 := ⟨div_nonneg hs.1 hr.1.le,(div_le_one hr.1).mpr hs.2⟩
  have hf : ContDiff ℝ ∞ (variableSqrtProfile W (shellCutoff 1) a V (s/r,r,b)) :=
    (variableSqrtProfile_smooth W (shellCutoff 1) a V hW (shellCutoff_smooth _)
      (shellCutoff_origin_not_tsupport (by norm_num)) ha hV).comp (contDiff_const.prodMk contDiff_id)
  have he : (fun z => shellCutoff r z * sqrtSingularSource W a V s b z) =
      fun z => variableSqrtProfile W (shellCutoff 1) a V (s/r,r,b) (r⁻¹ • (z-0)) :=
    funext (sqrtShell_eq_normalized W a V hr.1 b)
  rw [he]
  exact (norm_iteratedFDeriv_dilate_le _ hf hr.1 0 x n).trans
    (div_le_div_of_nonneg_right (hbound _ hsr r ⟨hr.1.le,hr.2⟩ b hb _) (pow_nonneg hr.1.le n))

lemma sqrtInner_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (fun z => scaledCutoff s z * sqrtSingularSource W a V s b z) x‖ ≤
        C / s^n := by
  obtain ⟨C,hC,hbound⟩ := innerSqrtProfile_derivatives_bounded W (scaledCutoff 1) a V
    hW (scaledCutoff_smooth _) (scaledCutoff_compact (by norm_num)) ha hV hK R n
  refine ⟨C,hC,?_⟩
  intro s hs b hb x
  have hf : ContDiff ℝ ∞ (variableSqrtProfile W (scaledCutoff 1) a V (1,s,b)) :=
    (innerSqrtProfile_smooth W (scaledCutoff 1) a V hW (scaledCutoff_smooth _) ha hV).comp
      ((show ContDiff ℝ ∞ (fun _ : E => (s,b)) from contDiff_const).prodMk contDiff_id)
  have he : (fun z => scaledCutoff s z * sqrtSingularSource W a V s b z) =
      fun z => variableSqrtProfile W (scaledCutoff 1) a V (1,s,b) (s⁻¹ • (z-0)) :=
    funext (sqrtInner_eq_normalized W a V hs.1 b)
  rw [he]
  exact (norm_iteratedFDeriv_dilate_le _ hf hs.1 0 x n).trans
    (div_le_div_of_nonneg_right (hbound s ⟨hs.1.le,hs.2⟩ b hb _) (pow_nonneg hs.1.le n))
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
lemma shiftedSqrtShell_weight (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) :
    ρ z * shiftedSqrtShell W a V r s b z =
      shiftedSqrtShell W a (fun w => ρ w • V w) r s b z := by
  simp [shiftedSqrtShell,shiftedSqrtSource,sqrtSingularSource,hermitianSqrtGradientProfile,map_smul,
    real_inner_smul_right]
  ring
omit [ProperSpace E] in
lemma shiftedSqrtInner_weight (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E) (s : ℝ) (b z : E) :
    ρ z * shiftedSqrtInner W a V s b z =
      shiftedSqrtInner W a (fun w => ρ w • V w) s b z := by
  simp [shiftedSqrtInner,shiftedSqrtSource,sqrtSingularSource,hermitianSqrtGradientProfile,map_smul,
    real_inner_smul_right]
  ring

lemma shiftedSqrtShell_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedSqrtShell W a V r s b) x‖ ≤ C/r^n := by
  obtain ⟨C,hC,hb⟩ := sqrtShell_derivatives_bounded W a V hW ha hV hK R n
  refine ⟨C,hC,fun r hr s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => shellCutoff r y * sqrtSingularSource W a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => shellCutoff r y * sqrtSingularSource W a V s b y) n b x]
  exact hb r hr s hs b hbK (x-b)
lemma shiftedSqrtInner_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedSqrtInner W a V s b) x‖ ≤ C/s^n := by
  obtain ⟨C,hC,hb⟩ := sqrtInner_derivatives_bounded W a V hW ha hV hK R n
  refine ⟨C,hC,fun s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => scaledCutoff s y * sqrtSingularSource W a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => scaledCutoff s y * sqrtSingularSource W a V s b y) n b x]
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
variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R)

lemma sqrtSourceSchwartz_reconstruction {s : ℝ} (hs : 0 < s) (b : E)
    (N : ℕ) (hN : R ≤ s*2^N) :
    sqrtSourceSchwartz W a V ha hV R haR hs b = sqrtInnerSchwartz W a V ha hV hs b +
    ∑ j ∈ Finset.range N, sqrtShellSchwartz W a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b := by
  apply SchwartzMap.ext
  intro z
  change shiftedSqrtSource W a V s b z = shiftedSqrtInner W a V s b z +
    (∑ j ∈ Finset.range N, sqrtShellSchwartz W a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b) z
  rw [sum_apply]
  change shiftedSqrtSource W a V s b z = scaledCutoff s (z-b) * shiftedSqrtSource W a V s b z +
    ∑ j ∈ Finset.range N, shellCutoff (s*2^j) (z-b) * shiftedSqrtSource W a V s b z
  rw [← Finset.sum_mul,← add_mul,dyadic_cutoff_telescope]
  by_cases hz : ‖z-b‖ ≤ s*2^N
  · rw [scaledCutoff_one (mul_pos hs (by positivity)) hz,one_mul]
  · have ha0 : a (z-b) = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
      have hh := haR h
      simp only [mem_closedBall,dist_zero_right] at hh
      exact hz (hh.trans hN))
    simp [shiftedSqrtSource,sqrtSingularSource,ha0]

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

lemma sqrtSupported_reconstruction {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K)
    (N : ℕ) (hN : R ≤ s*2^N) :
    sqrtSourceSupported W a V ha hV R haR K hs b hb =
      sqrtInnerSupported W a V ha hV R haR K hs b hb +
      ∑ j ∈ Finset.range N, sqrtShellSupported W a V ha hV R haR K
        (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b hb := by
  apply Subtype.ext
  simpa only [Submodule.coe_add,Submodule.coe_sum,sqrtSourceSupported,sqrtInnerSupported,sqrtShellSupported] using
    sqrtSourceSchwartz_reconstruction W a V ha hV R haR hs b N hN

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
lemma firstOrderSource_translatedCutoffSqrt (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (b z : E) :
    firstOrderSource V (translatedCutoffSqrt W R s b) z =
      shiftedSqrtSource W (scaledCutoff R) V s b z + shiftedSqrtError W V R s b z := by
  change fderiv ℝ (fun z => cutoffSqrtPotential (W b) R s (z-b)) z (V z) = _
  rw [fderiv_comp_sub]
  simpa [firstOrderSource,shiftedSqrtSource,sqrtSingularSource,shiftedSqrtError,cutoffSqrtError] using
    firstOrderSource_cutoffSqrt (W b) (fun w => V (b+w)) R hs (z-b)

variable (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)

lemma sqrtCutoffSourceSupported_eq (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    sqrtCutoffSourceSupported W V hV hR hs K b hb =
      sqrtSourceSupported W (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hs b hb + sqrtErrorSupported W V hW hV hR K s b hb := by
  apply Subtype.ext
  ext z
  exact firstOrderSource_translatedCutoffSqrt W V R hs b z

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianUniformInputs
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
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E)
  (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hρ : ContDiff ℝ ∞ ρ) (hV : ContDiff ℝ ∞ V)

include hW hρ in

lemma sqrtShellSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) r, ∀ b ∈ K,
      (∀ z, |sqrtShellSchwartz W a V ha hV hr.1 hs.1 b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * sqrtShellSchwartz W a V ha hV hr.1 hs.1 b z) z‖ ≤ (C)/(5*r)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedSqrtShell_derivatives_bounded W a V hW ha hV hK R 0
  choose D hD hb using fun n => shiftedSqrtShell_derivatives_bounded W a
    (fun w => ρ w • V w) hW ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hbK
  constructor
  · intro z
    have h := hb₀ r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] at h
    exact h.trans (by exact hC₀)
  · intro n hn z
    have he : (fun z => ρ z * sqrtShellSchwartz W a V ha hV hr.1 hs.1 b z) =
        shiftedSqrtShell W a (fun w => ρ w • V w) r s b :=
      funext (shiftedSqrtShell_weight W a ρ V r s b)
    rw [he]
    have h := hb n r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hr.1) n 0 (hCD n hn)

include hW hρ in

lemma sqrtInnerSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) R, ∀ b ∈ K,
      (∀ z, |sqrtInnerSchwartz W a V ha hV hs.1 b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * sqrtInnerSchwartz W a V ha hV hs.1 b z) z‖ ≤ (C)/(5*s)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedSqrtInner_derivatives_bounded W a V hW ha hV hK R 0
  choose D hD hb using fun n => shiftedSqrtInner_derivatives_bounded W a
    (fun w => ρ w • V w) hW ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] at h
    exact h.trans (by exact hC₀)
  · intro n hn z
    have he : (fun z => ρ z * sqrtInnerSchwartz W a V ha hV hs.1 b z) =
        shiftedSqrtInner W a (fun w => ρ w • V w) s b :=
      funext (shiftedSqrtInner_weight W a ρ V s b)
    rw [he]
    have h := hb n s hs b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hs.1) n 0 (hCD n hn)

end TamingCompatibility.HermitianRadial

end
end

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

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtShell_estimates
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) r, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*r+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C*r^3/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.sqrtShellSchwartz_uniform_inputs W a ρ V hW ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy r hr s hsr b hb
  have hr0 : 0 < r := hr.1
  let φ := HermitianRadial.sqrtShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb)
  have hin := hinput r hr s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*r) :=
    (HermitianRadial.shiftedSqrtShell_support W a V hr.1 s b).trans
      (Metric.closedBall_subset_ball (by linarith [hr.1] : 4*r < 5*r))
  have hM : 0 ≤ E := by positivity
  constructor
  · have hnear := (hest y hy).1 (5*r) (by positivity) φ j b (E) hM hball hin.1 hin.2
    apply hnear.trans
    nlinarith [mul_nonneg hC hE]
  · intro t ht hsep
    have hoff := (hest y hy).2 t ht φ j b (5*r) (E) (by positivity) hM hball hin.1 hsep
    apply hoff.trans_eq
    ring

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtInner_estimates
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*s+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*s^3/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.sqrtInnerSchwartz_uniform_inputs W a ρ V hW ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hs0 : 0 < s := hsr.1
  let φ := HermitianRadial.sqrtInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb)
  have hin := hinput s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*s) :=
    (HermitianRadial.shiftedSqrtInner_support W a V hsr.1 b).trans
      (Metric.closedBall_subset_ball (by linarith [hsr.1] : 2*s < 5*s))
  have hM : 0 ≤ E := by positivity
  constructor
  · have hnear := (hest y hy).1 (5*s) (by positivity) φ j b (E) hM hball hin.1 hin.2
    apply hnear.trans
    nlinarith [mul_nonneg hC hE]
  · intro t ht hsep
    have hoff := (hest y hy).2 t ht φ j b (5*s) (E) (by positivity) hM hball hin.1 hsep
    apply hoff.trans_eq
    ring

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianAssembly
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtSource_observer_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) (hR1 : R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ∀ t ∈ Ico (0:ℝ) δ, (5+c)*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtSourceSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*(10+|Real.log (max s t)|/Real.log 2) := by
  obtain ⟨δ₁,hδ₁,hδ₁1,c₁,hc₁,C₁,hC₁,hinner⟩ :=
    scalarCorrection_sqrtInner_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters
  obtain ⟨δ₂,hδ₂,_,c₂,_,C₂,_,hshell⟩ :=
    scalarCorrection_sqrtShell_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters
  let δ := min δ₁ δ₂
  let c := max c₁ c₂
  let C := max C₁ C₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨δ,lt_min hδ₁ hδ₂,(min_le_left _ _).trans hδ₁1,c,hc₁.trans_le (le_max_left _ _),
    C,hC,?_⟩
  intro y hy s hsr b hb t hto hsep
  have hs0 : 0 < s := hsr.1
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le (min_le_left _ _)
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le (min_le_right _ _)
  obtain ⟨N,hN,hscale,hmin⟩ := exists_minimal_dyadic_scale hsr.1 hsr.2
  let L := scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
  let v₀ := L (HermitianRadial.sqrtInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))
  let v := fun k => L (HermitianRadial.sqrtShellSupported W a V ha hV R haR K
    (mul_pos hsr.1 (by positivity : 0 < (2:ℝ)^k)) hsr.1 b (hcenters b hb))
  have hi := hinner y hy₁ s hsr b hb
  have h₀near : ‖v₀‖ ≤ C := hi.1.trans (le_max_left _ _)
  have hnear : ∀ k < N, ‖v k‖ ≤ C := by
    intro k hk
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    exact (hshell y hy₂ (s*2^k) hr s hsr' b hb).1.trans
      (le_max_right _ _)
  have hoff : ∀ k < N, s*2^k ≤ t → ‖v k‖ ≤ C*(s*2^k)^3/t^3 := by
    intro k hk hkt
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    have ht0 : 0 < t := hr.1.trans_le hkt
    have hsel : 5*(s*2^k)+c₂*t ≤ dist b y := by
      have hc : c₂*t ≤ c*t := mul_le_mul_of_nonneg_right (le_max_right _ _) hto.1
      nlinarith
    exact ((hshell y hy₂ (s*2^k) hr s hsr' b hb).2 t
      ⟨ht0,hto.2.trans_le (min_le_right _ _)⟩ hsel).trans (by gcongr; exact le_max_right _ _)
  have he := HermitianRadial.sqrtSupported_reconstruction W a V ha hV R haR K hsr.1 b (hcenters b hb) N hN
  change ‖L _‖ ≤ _
  rw [he,map_add,map_sum]
  exact dyadic_mixed_log_bound v₀ v N hs0 hto.1 hC (hscale.trans (by linarith)) h₀near hnear hoff

end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianDistance
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

theorem scalarCorrection_sqrtSource_distance_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) (hR1 : R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtSourceSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_sqrtSource_observer_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters hR1
  obtain ⟨M,hM,hKM⟩ := hK₀.isBounded.subset_ball_lt 0 q
  let L := max (5+c) (2*(M+1)/δ)
  have hL : 1 ≤ L := (by linarith : (1:ℝ) ≤ 5+c).trans (le_max_left _ _)
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogL : 0 ≤ Real.log (2*L) := Real.log_nonneg (by linarith)
  refine ⟨δ,hδ,C*(10+Real.log (2*L)/Real.log 2+1/Real.log 2),by positivity,?_⟩
  intro y hy s hsr b hb
  have hdM : dist b y ≤ M+1 := by
    have hbM := hKM hb
    have hy1 : dist q y ≤ 1 := by simpa only [dist_comm] using (show dist y q < δ from hy).le.trans hδ1
    have hbM' : dist b q < M := hbM
    linarith [dist_triangle b q y]
  obtain ⟨ht0,htδ,hsep,_,hcomp⟩ := observerScale_properties hδ hc (dist_nonneg : 0 ≤ dist b y) hdM
  have he := hest y hy s hsr b hb (observerScale δ c (dist b y)) ⟨ht0,htδ⟩ hsep
  exact he.trans (log_observer_to_distance hsr.1 ht0 (observerScale_le_dist hc dist_nonneg) hL hcomp hC)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffEstimates
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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

include hD hH hweak hB hdual in

theorem scalarCorrection_cutoffSqrt_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) (hR1 : 2*R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtCutoffSourceSupported W V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hsource⟩ :=
    scalarCorrection_sqrtSource_distance_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W (scaledCutoff R) V hW (scaledCutoff_smooth R) hV
      (2*R) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters hR1
  obtain ⟨δ₂,hδ₂,C₂,hC₂,herror⟩ :=
    scalarCorrection_sqrtError_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W V hW hV R hR (2*R) K₀ hK₀ hcenters
  let δ := min (min δ₁ δ₂) 1
  refine ⟨δ,lt_min (lt_min hδ₁ hδ₂) (by norm_num),C₁+C₂,by positivity,?_⟩
  intro y hy s hsr b hb
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  rw [HermitianRadial.sqrtCutoffSourceSupported_eq W V hW,map_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hsource y hy₁ s hsr b hb) (herror y hy₂ s ⟨hsr.1.le,hsr.2⟩ b hb)).trans
  nlinarith [mul_nonneg hC₂ (abs_nonneg (Real.log (s+dist b y)))]

end TamingCompatibility.GeometricHilbert.Hermitian

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianGeometricEstimates
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

variable (W : Space → Space →L[ℝ] Space) (hW : ContDiff ℝ ∞ W)

include hD hH hweak hB hdual hW in

theorem nonharmonic_geometric_cutoffSqrt_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (q : Space) (hq : q ∈ U) (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) (hR1 : 2*R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffSqrt_smooth W R hsr.1 b)
            (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
            (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans (hcenters b hb)).trans
              (hKU.trans (hUD.trans (D p).domain_subset))))))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨δ₀,hδ₀,C₀,hC₀,hzero⟩ := scalarCorrection_cutoffSqrt_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      0 W (V 0) hW ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters hR1
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hone⟩ := scalarCorrection_cutoffSqrt_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      1 W (V 1) hW ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters hR1
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro y hy s hsr b hb
  have hy₀ : y ∈ Metric.ball q δ₀ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_left _ _)
  have hy₁ : y ∈ Metric.ball q δ₁ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_right _ _)
  rw [smoothAnti_ddc_cutoffSqrt A J α hs ht D W p hφ hc hφD K hK (hKU.trans hUD)
    hφone hR hsr.1 b (hcenters b hb),map_add]
  apply (norm_add_le _ _).trans
  have h₀ := hzero y hy₀ s hsr b hb
  have h₁ := hone y hy₁ s hsr b hb
  exact (add_le_add h₀ h₁).trans_eq (by ring)

end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactUniformBound
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
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

theorem nonharmonic_sqrtSource_compact_oai (hR1 : 2*R ≤ 1)
    (L : Set Space) (hL : IsCompact L) (hLU : L ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ L, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (sqrtSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD)))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  apply _root_.OAI.IsCompact.exists_uniform_monotone_bound hL
  · intro y a c hac ha s hsr b hb
    exact (ha s hsr b hb).trans (mul_le_mul_of_nonneg_right hac (by positivity))
  · intro q hq
    let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
    obtain ⟨δ,hδ,C,hC,hest⟩ := nonharmonic_geometric_cutoffSqrt_estimate
      A J α hs ht D hD H Gs hH hweak B hB hdual W (W.smooth ⊤)
      p τ ρ U hU hUD hτ hρ hφ hc hφD K hK hKU hφone q (hLU hq)
      R hR K₀ hK₀ hcenters hR1
    refine ⟨C,hC,?_⟩
    filter_upwards [Metric.ball_mem_nhds q hδ] with y hy
    intro s hsr b hb
    exact hest y hy s hsr b hb
end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_sqrtSource_compact_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_sqrtSource_compact_oai.{u_1}
