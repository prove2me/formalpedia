-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.Hermitian.logForm_far_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:36:43.143042+00:00
-- url     : https://prove2.me/submissions/a9d6b558-3c28-4914-a6f5-ae021cc8f5a4

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_nonharmonic_logSource_compact

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JAction
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

lemma invariantPart_add_antiInvariantPart (J : AlmostComplexStructure X) (α : TwoForm X) :
    invariantPart J α + antiInvariantPart J α = α := by
  unfold invariantPart antiInvariantPart
  module

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldComplexDifferential
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothUnitEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
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
attribute [local instance] unitMeasurable unitBorel 

lemma eval_antiInvariantPart_complexLine (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (v : TangentSpace Model x) :
    eval (antiInvariantPart J α) x v (J.endomorphism x v) = 0 := by
  have h := congrArg (fun β => eval β x v (J.endomorphism x v))
    (invariantPart_add_antiInvariantPart J α)
  change eval (invariantPart J α) x v (J.endomorphism x v) +
    eval (antiInvariantPart J α) x v (J.endomorphism x v) = _ at h
  rw [eval_invariantPart_complexLine] at h
  linarith

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftData
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma closedLiftOfInverse_apply
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) :
    (closedLiftOfInverse A J α hs ht H Gs f).val =
      (fun a b : TwoForm X => a+b) (exteriorDerivative (codifferential J α ht (Gs f).val.val)) (H f).val.val := rfl

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma closedLiftOfInverse_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) (x : X) (v : TangentSpace Model x) :
    eval (closedLiftOfInverse A J α hs ht H Gs f).val x v (J.endomorphism x v) =
      eval (exteriorDerivative (codifferential J α ht (Gs f).val.val)) x v (J.endomorphism x v) := by
  rw [closedLiftOfInverse_apply]
  change eval (exteriorDerivative (codifferential J α ht (Gs f).val.val)) x v (J.endomorphism x v) +
    eval (H f).val.val x v (J.endomorphism x v) = _
  rw [← (H f).property,eval_antiInvariantPart_complexLine,add_zero]

end TamingCompatibility.GeometricHilbert

end
end

end
end
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

end TamingCompatibility.ManifoldForms

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

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ContinuousAlternatingMap
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma closedLift_pullback_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (a : antiPre A J α hs ht) (p : X) {y : Space}
    (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs a).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      nonharmonicCorrectionLM A J α hs ht Gs p y a ![v,coordinateJ J p y v] := by
  change _ = ManifoldForms.pullback
    (exteriorDerivative (codifferential J α ht (Gs a).val.val)) (extChartAt Model p).symm y _
  rw [pullback_complexLine J _ p hy,pullback_complexLine J _ p hy]
  exact closedLiftOfInverse_complexLine A J α hs ht H Gs a _ _

lemma correctedDdc_pullback_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (p : X) {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback (correctedDdc A J α hs ht H Gs hf).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
    ManifoldForms.pullback (exteriorDerivative (complexDifferential J f))
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] -
      nonharmonicCorrectionLM A J α hs ht Gs p y
        (smoothAntiProjection A J α hs ht (smoothDdc J hf)) ![v,coordinateJ J p y v] := by
  change ManifoldForms.pullback (_-_) _ _ _ = _
  change ManifoldForms.pullback (smoothDdc J hf).val _ _ _ -
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs
      (smoothAntiProjection A J α hs ht (smoothDdc J hf))).val _ _ _ = _
  rw [closedLift_pullback_complexLine A J α hs ht H Gs _ p hy]
  rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianTraceTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ExteriorForms
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extDeriv_dc_congr_germ {J K : E → E →L[ℝ] E} {f g : E → ℝ} {y : E}
    (hJ : J =ᶠ[𝓝 y] K) (hf : f =ᶠ[𝓝 y] g) :
    extDeriv (dc J f) y = extDeriv (dc K g) y := by
  have he : dc J f =ᶠ[𝓝 y] dc K g := by
    filter_upwards [hJ,hf.fderiv (𝕜 := ℝ)] with x hx hf
    simp only [dc,hx,hf]
  exact congrArg ContinuousAlternatingMap.alternatizeUncurryFin he.fderiv_eq
end TamingCompatibility.ExteriorForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianManifoldTrace
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter ContinuousAlternatingMap RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
 [T2Space X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma pullback_ddc_scalarChartLift {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hfD : tsupport f ⊆ (extChartAt Model p).target)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (exteriorDerivative (complexDifferential J (scalarChartLift p f)))
      (extChartAt Model p).symm y = extDeriv (ExteriorForms.dc (coordinateJ J p) f) y := by
  rw [pullback_ddc J (scalarChartLift_smooth p hf hc hfD) p hy]
  apply ExteriorForms.extDeriv_dc_congr_germ Filter.EventuallyEq.rfl
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact scalarChartLift_apply_inverse p f hz

end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianFarSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma parameter_fderiv_contDiffAt {f : P → E → F} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (fun x : P × E => f x.1 x.2) q) :
    ContDiffAt ℝ ∞ (fun x : P × E => fderiv ℝ (f x.1) x.2) q := by
  have h : ContDiffAt ℝ ∞ (fun x : (P × E) × E => f x.1.1 x.2) (q,q.2) :=
    hf.comp (q,q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact h.fderiv contDiffAt_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

lemma parameter_dc_contDiffAt {f : P → E → ℝ} {J : E → E →L[ℝ] E} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (fun x : P × E => f x.1 x.2) q)
    (hJ : ContDiffAt ℝ ∞ J q.2) :
    ContDiffAt ℝ ∞ (fun x : P × E => dc J (f x.1) x.2) q := by
  exact ((parameter_fderiv_contDiffAt hf).clm_comp
    (hJ.comp q contDiffAt_snd)).neg.continuousLinearMap_comp
      (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap

lemma parameter_ddc_contDiffAt {f : P → E → ℝ} {J : E → E →L[ℝ] E} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (fun x : P × E => f x.1 x.2) q)
    (hJ : ContDiffAt ℝ ∞ J q.2) :
    ContDiffAt ℝ ∞ (fun x : P × E => extDeriv (dc J (f x.1)) x.2) q := by
  have hd : ContDiffAt ℝ ∞ (fun x : P × E => fderiv ℝ (dc J (f x.1)) x.2) q :=
    parameter_fderiv_contDiffAt (f := fun a => dc J (f a))
      (parameter_dc_contDiffAt hf hJ)
  exact hd.continuousLinearMap_comp (alternatizeUncurryFinCLM (n := 1) ℝ E ℝ)
end TamingCompatibility.ExteriorForms

namespace TamingCompatibility.HermitianRadial
open RadialPotential Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]
variable (W : E → E →L[ℝ] E) (hW : ContDiff ℝ ∞ W) (R : ℝ)

include hW in
lemma translatedCutoffLog_joint_smooth {q : (ℝ × E) × E}
    (hq : 0 < q.1.1^2 + ‖q.2-q.1.2‖^2) :
    ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E => translatedCutoffLog W R x.1.1 x.1.2 x.2) q := by
  have hz : ContDiff ℝ ∞ (fun x : (ℝ × E) × E => x.2-x.1.2) := contDiff_snd.sub contDiff_fst.snd
  have hden : ContDiff ℝ ∞ (fun x : (ℝ × E) × E =>
      x.1.1^2 + ‖x.2-x.1.2‖^2 + ‖W x.1.2 (x.2-x.1.2)‖^2) :=
    ((contDiff_fst.fst.pow 2).add ((contDiff_norm_sq ℝ).comp hz)).add
      ((contDiff_norm_sq ℝ).comp ((hW.comp contDiff_fst.snd).clm_apply hz))
  have hp : 0 < q.1.1^2 + ‖q.2-q.1.2‖^2 + ‖W q.1.2 (q.2-q.1.2)‖^2 := by positivity
  simpa only [translatedCutoffLog,cutoffLogPotential,hermitianLogPotential,
    logPotential,hermitianGraph_norm_sq,add_assoc,Function.comp_def] using
    ((scaledCutoff_smooth R).comp hz).contDiffAt.mul
      (contDiffAt_const.mul (hden.contDiffAt.log hp.ne'))

end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open RadialPotential ExteriorForms ContinuousAlternatingMap Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]
variable (W : E → E →L[ℝ] E) (hW : ContDiff ℝ ∞ W)
  (J : E → E →L[ℝ] E) (U : Set E) (hU : IsOpen U) (hJ : ContDiffOn ℝ ∞ J U)
  (R : ℝ) (K₀ L : Set E) (hK₀ : IsCompact K₀) (hL : IsCompact L) (hLU : L ⊆ U)
  (ε : ℝ) (hε : 0 < ε)

include hK₀ hL in
omit [InnerProductSpace ℝ E] [HasContDiffBump E] in
lemma far_parameter_compact : IsCompact
    {q : (ℝ × E) × E | q.1.1 ∈ Icc (0:ℝ) (2*R) ∧ q.1.2 ∈ K₀ ∧ q.2 ∈ L ∧
      ε ≤ q.1.1+‖q.2-q.1.2‖} := by
  have hclosed : _root_.IsClosed {q : (ℝ × E) × E | ε ≤ q.1.1+‖q.2-q.1.2‖} :=
    isClosed_le continuous_const (continuous_fst.fst.add (continuous_snd.sub continuous_fst.snd).norm)
  convert ((isCompact_Icc.prod hK₀).prod hL).inter_right hclosed using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  simp only [mem_inter_iff,mem_prod,mem_ofPred_eq]
  tauto

include hW hU hJ hK₀ hL hLU hε in
lemma cutoffLog_ddc_far_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) (2*R),
    ∀ b ∈ K₀, ∀ y ∈ L, ε ≤ s+‖y-b‖ →
      ‖extDeriv (dc J (translatedCutoffLog W R s b)) y‖ ≤ C := by
  let S := {q : (ℝ × E) × E | q.1.1 ∈ Icc (0:ℝ) (2*R) ∧ q.1.2 ∈ K₀ ∧ q.2 ∈ L ∧
      ε ≤ q.1.1+‖q.2-q.1.2‖}
  have hS : IsCompact S := far_parameter_compact R K₀ L hK₀ hL ε
  have hcont : ContinuousOn (fun q : (ℝ × E) × E =>
      extDeriv (dc J (translatedCutoffLog W R q.1.1 q.1.2)) q.2) S := by
    intro q hq
    have hp : 0 < q.1.1^2+‖q.2-q.1.2‖^2 := by
      have h := hq.2.2.2
      nlinarith [sq_nonneg (q.1.1-‖q.2-q.1.2‖)]
    have hf : ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E =>
        translatedCutoffLog W R x.1.1 x.1.2 x.2) q :=
      translatedCutoffLog_joint_smooth W hW R hp
    have hj : ContDiffAt ℝ ∞ J q.2 := hJ.contDiffAt (hU.mem_nhds (hLU hq.2.2.1))
    have hd : ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E =>
        extDeriv (dc J (translatedCutoffLog W R x.1.1 x.1.2)) x.2) q :=
      parameter_ddc_contDiffAt (f := fun a : ℝ × E => translatedCutoffLog W R a.1 a.2)
        (J := J) (q := q) hf hj
    exact hd.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hcont
  exact ⟨max C 0,le_max_right _ _,fun s hs b hb y hy hf =>
    (hC ((s,b),y) ⟨hs,hb,hy,hf⟩).trans (le_max_left _ _)⟩

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactPositiveBilinear
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Set

lemma compact_positive_bilinear_bounds {Y E : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {K : Set Y} (hK : IsCompact K) {g : Y → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContinuousOn g K) (hpos : ∀ z ∈ K, ∀ v : E, v ≠ 0 → 0 < g z v v) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : E,
      m*‖v‖^2 ≤ g z v v ∧ g z v v ≤ M*‖v‖^2 := by
  by_cases hne : K.Nonempty
  · let q : Y × E → ℝ := fun x => g x.1 x.2 x.2
    have hq : ContinuousOn q (K ×ˢ Metric.sphere (0:E) 1) :=
      ((hg.comp continuousOn_fst (fun _ hx => hx.1)).clm_apply continuousOn_snd).clm_apply
        continuousOn_snd
    obtain ⟨x,hx,hmin⟩ := (hK.prod (isCompact_sphere (0:E) 1)).exists_isMinOn
      (hne.prod (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1))) hq
    have hxnorm : ‖x.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx.2
    have hqx : 0 < q x := hpos x.1 hx.1 x.2 (by intro h; simp [h] at hxnorm)
    obtain ⟨y,hy,hmax⟩ := (hK.prod (isCompact_sphere (0:E) 1)).exists_isMaxOn
      (hne.prod (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1))) hq
    refine ⟨q x,max (q y) 1,hqx,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      let w := ‖v‖⁻¹ • v
      have hw : w ∈ Metric.sphere (0:E) 1 := by
        simp [w,norm_smul,inv_mul_cancel₀ hnv]
      have hid : g z w w * ‖v‖^2 = g z v v := by
        simp only [w,map_smul,_root_.smul_apply,smul_eq_mul]
        field_simp
      have hlo := mul_le_mul_of_nonneg_right (hmin (show (z,w) ∈ K ×ˢ Metric.sphere (0:E) 1 from ⟨hz,hw⟩)) (sq_nonneg ‖v‖)
      have hup := mul_le_mul_of_nonneg_right
        ((hmax (show (z,w) ∈ K ×ˢ Metric.sphere (0:E) 1 from ⟨hz,hw⟩)).trans (le_max_left (q y) 1)) (sq_nonneg ‖v‖)
      change q x * ‖v‖^2 ≤ g z w w * ‖v‖^2 at hlo
      change g z w w * ‖v‖^2 ≤ max (q y) 1 * ‖v‖^2 at hup
      rw [hid] at hlo hup
      exact ⟨hlo,hup⟩
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro z hz
    exact (hne ⟨z,hz⟩).elim
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianUnitMetric
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
namespace TamingCompatibility.ManifoldVolume
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J)

include hs ht in
lemma chartMetric_compact_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : Space,
      m*‖v‖^2 ≤ chartMetric J α p z v v ∧ chartMetric J α p z v v ≤ M*‖v‖^2 :=
  compact_positive_bilinear_bounds hK (((hs.invariantPart J).metricCoords J p).continuousOn.mono hKT)
    (fun _z hz v hv => chartMetric_pos J α ht p (hKT hz) v hv)

include hs ht in
lemma chartMetric_unit_norm_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : Space,
      chartMetric J α p z v v = 1 → m ≤ ‖v‖^2 ∧ ‖v‖^2 ≤ M := by
  obtain ⟨a,b,ha,hb,hbound⟩ := chartMetric_compact_bounds J α hs ht p hK hKT
  refine ⟨1/b,1/a,by positivity,by positivity,?_⟩
  intro z hz v hv
  obtain ⟨hlo,hup⟩ := hbound z hz v
  rw [hv] at hlo hup
  exact ⟨(div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hup),
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hlo)⟩

include ht in
lemma chartMetric_hermitian (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z (coordinateJ J p z u) (coordinateJ J p z v) =
      chartMetric J α p z u v := by
  have h := coordinateMetric_hermitian J α ht p hz u v
  simpa only [coordinateMetric_bilinear J α ht p hz] using h

include hs ht in
lemma form_unit_line_bound (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, ∀ v : Space, chartMetric J α p z v v = 1 →
      ∀ β : MetricForms.Form Space 2, ‖β ![v,coordinateJ J p z v]‖ ≤ ‖β‖*M := by
  obtain ⟨m,M,_,hM,hbound⟩ := chartMetric_unit_norm_bounds J α hs ht p hK hKT
  refine ⟨M,hM,?_⟩
  intro z hz v hv β
  have hnv := (hbound z hz v hv).2
  have hnJ := (hbound z hz (coordinateJ J p z v)
    ((chartMetric_hermitian J α ht p (hKT hz) v v).trans hv)).2
  have hprod : ‖v‖*‖coordinateJ J p z v‖ ≤ M := by
    nlinarith [sq_nonneg (‖v‖-‖coordinateJ J p z v‖)]
  calc
    _ ≤ ‖β‖*(‖v‖*‖coordinateJ J p z v‖) := by
      simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
        using β.le_opNorm ![v,coordinateJ J p z v]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)

end TamingCompatibility.ManifoldVolume

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

theorem logForm_far_uniform_oai (L : Set Space) (hL : IsCompact L)
    (hLU : L ⊆ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ L, ε ≤ s+‖y-b‖ → ∀ v : Space, chartMetric J α p.val y v v = 1 →
      ‖ManifoldForms.pullback
        (logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤ C := by
  let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
  have hLT : L ⊆ (extChartAt Model p.val).target := hLU.trans (hUD.trans (D p).domain_subset)
  obtain ⟨C₀,hC₀,hraw⟩ := HermitianRadial.cutoffLog_ddc_far_bound
    W (W.smooth ⊤) (coordinateJ J p.val) (extChartAt Model p.val).target
    (isOpen_extChartAt_target p.val) (coordinateJ_smooth J p.val)
    R K₀ L hK₀ hL hLT ε hε
  obtain ⟨C₁,hC₁,hcorr⟩ := nonharmonic_logSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters L hL hLU
  let F := C₁/ε
  have hF : 0 ≤ F := by dsimp [F] <;> positivity
  obtain ⟨M,hM,hunit⟩ := form_unit_line_bound J α hs ht p.val hL hLT
  refine ⟨(C₀+F)*M,by positivity,?_⟩
  intro s hsr b hb y hy hfar v hv
  have hball := (hcenters b hb).trans (hKU.trans hUD)
  have hnc : ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
      (logSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b hball)‖ ≤ F := by
    exact (hcorr y hy s hsr b hb).trans
      (div_le_div_of_nonneg_left hC₁ hε (by simpa only [dist_comm b y,dist_eq_norm] using hfar))
  have hrc := hraw s ⟨hsr.1.le,hsr.2⟩ b hb y hy hfar
  rw [logForm,correctedDdc_pullback_complexLine A J α hs ht H Gs _ p.val (hLT hy),
    pullback_ddc_scalarChartLift J p.val
      (HermitianRadial.translatedCutoffLog_smooth W R hsr.1 b)
      (HermitianRadial.translatedCutoffLog_compact W hR s b)
      (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hball).trans
        (D p).domain_subset) (hLT hy)]
  calc
    _ ≤ ‖extDeriv (ExteriorForms.dc (coordinateJ J p.val)
        (HermitianRadial.translatedCutoffLog W R s b)) y ![v,coordinateJ J p.val y v]‖ +
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (logSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b hball)
        ![v,coordinateJ J p.val y v]‖ := norm_sub_le _ _
    _ ≤ C₀*M+F*M := add_le_add
      ((hunit y hy v hv _).trans (mul_le_mul_of_nonneg_right hrc hM.le))
      ((hunit y hy v hv _).trans (mul_le_mul_of_nonneg_right hnc hM.le))
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.Hermitian.logForm_far_uniform_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.Hermitian.logForm_far_uniform_oai.{u_1}
