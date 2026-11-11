-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.hodgePositiveCurrentFamily_anti_cross_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:15:40.282258+00:00
-- url     : https://prove2.me/submissions/d404f777-5400-4c10-8f13-e44b09b2cd08

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc033

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

lemma unitMeasureCurrent_antiInvariantPart [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (α : TwoForm X) (hα : IsSmooth α) :
    unitMeasureCurrent J g μ ⟨antiInvariantPart J α, hα.antiInvariantPart J⟩ = 0 := by
  change (∫ p : MetricUnit g,
    eval (antiInvariantPart J α) p.val.proj p.val.2
      (J.endomorphism p.val.proj p.val.2) ∂μ) = 0
  simp only [eval_antiInvariantPart_complexLine, integral_zero]

end TamingCompatibility

end

end OAI
end

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

end TamingCompatibility.HilbertKernel

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalDistribution
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

lemma hodgeInclusion_dense : DenseRange (hodgeInclusion A J α hs ht) :=
  (smoothL2_dense A J α hs ht true).mono (by rintro _ ⟨a,rfl⟩; exact ⟨hodgeSmooth A J α hs ht a,rfl⟩)
end TamingCompatibility.GeometricHilbert

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeConvergence
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Filter Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeResolvent_domain_error (r : ℝ) (hr : 0 < r) (a : hodgeEnergy A J α hs ht) :
    ‖hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a) -
      hodgeInclusion A J α hs ht a‖ ≤ r * ‖hodgeWeakDerivative A J α hs ht a‖ := by
  let i := hodgeInclusion A J α hs ht
  let D := hodgeWeakDerivative A J α hs ht
  let u := hodgeWeakSolution A J α hs ht r hr (i a)
  have he := hodgeWeakSolution_identity A J α hs ht r hr (i a) (u-a)
  have hi : hodgeResolvent A J α hs ht r (i a) = i u := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  change ⟪hodgeResolvent A J α hs ht r (i a),i (u-a)⟫ + r^2*⟪D u,D (u-a)⟫ = ⟪i a,i (u-a)⟫ at he
  rw [hi,map_sub,map_sub,inner_sub_right,inner_sub_right,inner_sub_right] at he
  have hn : ‖i u-i a‖^2 + r^2*‖D u‖^2 = r^2*⟪D u,D a⟫ := by
    rw [← real_inner_self_eq_norm_sq (i u-i a)]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq]
    rw [real_inner_comm (i a) (i u)] at he ⊢
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
    linarith
  have hc := mul_le_mul_of_nonneg_left (real_inner_le_norm (D u) (D a)) (sq_nonneg r)
  rw [hi]
  have hpos : 0 ≤ r * ‖D a‖ := mul_nonneg hr.le (norm_nonneg _)
  have hsquare := sq_nonneg (r*‖D u‖-r*‖D a‖)
  nlinarith [norm_nonneg (i u-i a)]

lemma hodgeResolvent_tendsto (f : L2 A J α hs ht true) :
    Tendsto (fun r : ℝ => hodgeResolvent A J α hs ht r f) (𝓝[>] 0) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := (hodgeInclusion_dense A J α hs ht).exists_dist_lt f (by positivity : 0 < ε/4)
  let D := hodgeWeakDerivative A J α hs ht a
  have hδ : 0 < ε/(2*(‖D‖+1)) := div_pos hε (by positivity)
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds hδ))] with r hr hsmall
  have hr' : 0 < r := hr
  have hsmallD : r * ‖D‖ < ε/2 := by
    have hb : r*(2*(‖D‖+1)) < ε := (lt_div_iff₀ (by positivity)).mp hsmall
    nlinarith [norm_nonneg D]
  rw [dist_eq_norm]
  have hx := hodgeResolvent_domain_error A J α hs ht r hr' a
  have hf := hodgeResolvent_norm_le A J α hs ht r (f-hodgeInclusion A J α hs ht a)
  rw [map_sub] at hf
  have htri := norm_add_le (hodgeResolvent A J α hs ht r f-
    hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a))
    (hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a)-hodgeInclusion A J α hs ht a)
  have htri2 := norm_add_le (hodgeResolvent A J α hs ht r f-hodgeInclusion A J α hs ht a)
    (hodgeInclusion A J α hs ht a-f)
  rw [sub_add_sub_cancel] at htri htri2
  rw [dist_eq_norm,norm_sub_rev] at ha
  have hn := norm_sub_rev (hodgeInclusion A J α hs ht a) f
  change r*‖hodgeWeakDerivative A J α hs ht a‖ < ε/2 at hsmallD
  linarith

lemma hodgeRegularization_error (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeRegularization A J α hs ht r f-f‖ ≤
      3*‖hodgeResolvent A J α hs ht r f-f‖ := by
  let R := hodgeResolvent A J α hs ht r
  have h1 : ‖R (R f)-R f‖ ≤ ‖R f-f‖ := by
    rw [← map_sub]; exact hodgeResolvent_norm_le A J α hs ht r _
  have h2 : ‖R (R (R f))-R (R f)‖ ≤ ‖R (R f)-R f‖ := by
    rw [← map_sub]; exact hodgeResolvent_norm_le A J α hs ht r _
  have ht1 := norm_add_le (R (R (R f))-R (R f)) (R (R f)-R f)
  have ht2 := norm_add_le (R (R (R f))-R f) (R f-f)
  rw [sub_add_sub_cancel] at ht1 ht2
  change ‖R (R (R f))-f‖ ≤ 3*‖R f-f‖
  linarith

lemma hodgeRegularization_tendsto (f : L2 A J α hs ht true) :
    Tendsto (fun r : ℝ => hodgeRegularization A J α hs ht r f) (𝓝[>] 0) (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (hodgeResolvent_tendsto A J α hs ht f).sub (tendsto_const_nhds (x := f))
  have hn := h.norm.const_mul 3
  simp only [sub_self,norm_zero,mul_zero] at hn
  exact squeeze_zero (fun r => norm_nonneg _)
    (fun r => hodgeRegularization_error A J α hs ht r f) hn
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalEvaluation
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
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

namespace LocalHodgeSmoothing
variable {A J α hs ht D hD} {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

omit [T2Space X] in
lemma representative_spec (f : L2 A J α hs ht true) :
    boundedDistribution (L.representative f) =
      hodgeLocalizedRegularization A J α hs ht D hD p L.reciprocal L.cutoff r hr f := by
  rw [representative,sobolevToBounded_spec,L.lift_spec]
end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalKernel
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
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace LocalHodgeSmoothing
variable {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

omit [T2Space X] in
lemma realEvaluation_apply (z : Space) (f : L2 A J α hs ht true) (j : Fin 6) :
    L.realEvaluation z f j = (L.representative f z j).re := rfl

end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothingCover
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
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma weight_chart (i : C.centers) {x : X}
    (hx : x ∈ (extChartAt Model (C.patch i).chart.val).source) :
    C.weight i (extChartAt Model (C.patch i).chart.val x) = C.partition i x := by
  change (C.weightFunction i) _ = _
  rw [weightFunction,indicator_of_mem ((extChartAt Model (C.patch i).chart.val).map_source hx),
    (extChartAt Model (C.patch i).chart.val).left_inv hx]

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeRegularization
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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

lemma regularize_pair (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (f : L2 A J α hs ht true) :
    ⟪C.regularize g μ,f⟫ = ∫ u, C.evaluation g u f ∂μ := by
  have h := HilbertKernel.regularize_pair μ (C.evaluation g) (fun _ => (1:ℝ))
    (C.evaluationVector_integrable g μ) f
  simpa only [HilbertKernel.regularize,regularize,evaluationVector,Real.inner_apply,one_mul,mul_one] using h

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

omit [T2Space X] in
lemma coordinate_basis_expansion (i : C.centers) (a : TwoForm X) {z : Space}
    (hz : z ∈ (D (C.patch i).chart).domain) :
    ∑ j : Fin 6, rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a z j •
      coordinateTest J α ht (C.patch i).chart.val (D (C.patch i).chart).toData
        (componentTest j (C.weight i)) z =
      C.weight i z • ManifoldForms.pullback a (extChartAt Model (C.patch i).chart.val).symm z := by
  let R := HodgeFrame.reconstruct (coordinateMetric J α ht (C.patch i).chart.val z)
    (fun k => (D (C.patch i).chart).frame k z)
  let v := rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a z
  have hv : ∑ j : Fin 6, v j • (C.weight i z • EuclideanSpace.single j (1:ℝ)) = C.weight i z • v := by
    ext k
    simp [WithLp.ofLp_sum,PiLp.smul_apply,EuclideanSpace.single,Pi.single_apply,smul_eq_mul,mul_ite,mul_comm]
  change ∑ j : Fin 6, v j • R (componentTest j (C.weight i) z) = _
  simp only [componentTest_apply]
  simp only [← map_smul]
  rw [← map_sum]
  rw [hv,map_smul]
  exact congrArg (C.weight i z • ·) (rawVector_expansion J α ht (C.patch i).chart.val
    (D (C.patch i).chart).toData a hz)

lemma basisForm_expansion (i : C.centers) (a : TwoForm X) {x : X}
    (hx : x ∈ tsupport (C.partition i)) :
    ∑ j : Fin 6, rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a
      (extChartAt Model (C.patch i).chart.val x) j • (C.basisForm i j).val x =
      C.partition i x • a x := by
  classical
  have hxs := (C.subordinate i hx).1
  have hxD := (C.patch i).smoothing.neighborhood_subset (C.subordinate i hx).2
  let z := extChartAt Model (C.patch i).chart.val x
  let L : TangentSpace Model x →L[ℝ] Space := mfderiv Model Model (extChartAt Model (C.patch i).chart.val) x
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := Model) hxs
  simp only [Model,modelWithCornersSelf_coe,Set.range_id,mfderivWithin_univ] at hi
  have he := C.coordinate_basis_expansion i a hxD
  have he' := congrArg (ContinuousAlternatingMap.compContinuousLinearMapCLM L) he
  change (ContinuousAlternatingMap.compContinuousLinearMapCLM L) (∑ j : Fin 6,
    rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a z j •
      coordinateTest J α ht (C.patch i).chart.val (D (C.patch i).chart).toData
        (componentTest j (C.weight i)) z) =
    (ContinuousAlternatingMap.compContinuousLinearMapCLM L)
      (C.weight i z • ManifoldForms.pullback a (extChartAt Model (C.patch i).chart.val).symm z) at he'
  rw [map_sum] at he'
  simp only [map_smul] at he'
  change (∑ j : Fin 6, rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a z j • (coordinateTest J α ht (C.patch i).chart.val
    (D (C.patch i).chart).toData (componentTest j (C.weight i)) z).compContinuousLinearMap L) =
    C.weight i z • (ManifoldForms.pullback a (extChartAt Model (C.patch i).chart.val).symm z).compContinuousLinearMap L at he'
  have hp : (ManifoldForms.pullback a (extChartAt Model (C.patch i).chart.val).symm z).compContinuousLinearMap L = a x := by
    unfold ManifoldForms.pullback
    change ((a ((extChartAt Model (C.patch i).chart.val).symm z) : Space [⋀^Fin 2]→L[ℝ] ℝ).compContinuousLinearMap
      ((mfderiv Model Model (extChartAt Model (C.patch i).chart.val).symm z : Space →L[ℝ] Space) ∘L
        (L : Space →L[ℝ] Space))) = (a x : Space [⋀^Fin 2]→L[ℝ] ℝ)
    erw [hi]
    change a ((extChartAt Model (C.patch i).chart.val).symm z) = a x
    erw [show (extChartAt Model (C.patch i).chart.val).symm z = x from
      (extChartAt Model (C.patch i).chart.val).left_inv hxs]
  rw [hp,C.weight_chart i hxs] at he'
  refine Eq.trans ?_ he'
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change chartLift (C.patch i).chart.val
    (coordinateTest J α ht (C.patch i).chart.val (D (C.patch i).chart).toData
      (componentTest j (C.weight i))) x = _
  rw [chartLift,ite_eq_left hxs]
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalSmooth
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
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace LocalHodgeSmoothing
variable {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

omit [T2Space X] in

lemma realEvaluation_smooth (f : L2 A J α hs ht true)
    (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a)
    {z : Space} (hz : z ∈ L.neighborhood) :
    L.realEvaluation z f = rawVector J α ht p.val (D p).toData a.val z := by
  have hg : hodgeRegularizedGraph A J α hs ht r hr f = hodgeSmooth A J α hs ht a := by
    apply hodgeInclusion_injective A J α hs ht
    rw [hodgeRegularizedGraph_inclusion,hodgeInclusion_smooth,ha]
  let b := SchwartzMap.smulLeftCLM HodgeNormalSymbol.W L.reciprocal
    (realVectorSchwartz A J α ht (fun q => (D q).toData) hD p a)
  let c := SchwartzMap.smulLeftCLM HodgeScalar.F L.cutoff (SchwartzMap.postcompCLM (embed 6) b)
  have he : L.representative f = c.toBoundedContinuousFunction := by
    apply boundedDistributionCLM_injective
    rw [boundedDistributionCLM_apply,boundedDistributionCLM_apply,L.representative_spec]
    change smulLeftCLM HodgeScalar.F L.cutoff
      (hodgeRawDistribution A J α hs ht D hD p L.reciprocal
        (hodgeRegularizedGraph A J α hs ht r hr f)) = _
    rw [hg,hodgeRawDistribution_smooth,product_schwartz,boundedDistribution_schwartz]
  ext j
  rw [L.realEvaluation_apply,he]
  change (c z j).re = _
  have hb : b z = rawVector J α ht p.val (D p).toData a.val z :=
    cutoff_realVector_raw A J α ht (fun q => (D q).toData) hD p a L.reciprocal
      (L.neighborhood_subset hz) (L.reciprocal_eq z hz)
  simp only [c,SchwartzMap.smulLeftCLM_apply L.cutoff.hasTemperateGrowth,
    L.cutoff_eq z hz,one_smul,SchwartzMap.postcompCLM_apply,hb,embed_apply,Complex.ofReal_re]
end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma evaluationTerm_smooth_sum (i : C.centers) (u : MetricUnit g)
    (f : L2 A J α hs ht true) (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    ∑ j : Fin 6, C.evaluationTerm g i j u f =
      C.partition i u.val.proj * unitEvaluation J g a.val a.property u := by
  classical
  by_cases hu : u.val.proj ∈ tsupport (C.partition i)
  · have he := C.basisForm_expansion i a.val hu
    have he' := congrArg (fun b => b ![u.val.2,J.endomorphism u.val.proj u.val.2]) he
    simp only [ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul] at he'
    change ∑ j : Fin 6, unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property u *
      ((C.patch i).smoothing.realEvaluation (extChartAt Model (C.patch i).chart.val u.val.proj) f) j = _
    rw [(C.patch i).smoothing.realEvaluation_smooth f a ha (C.subordinate i hu).2]
    simpa only [unitEvaluation,ContinuousMap.coe_mk,eval,mul_comm] using he'
  · have hp := image_eq_zero_of_notMem_tsupport hu
    rw [hp,zero_mul]
    apply Finset.sum_eq_zero
    intro j _
    change unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property u * _ = 0
    have hz : unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property u = 0 := by
      change (C.basisForm i j).val u.val.proj ![u.val.2,J.endomorphism u.val.proj u.val.2] = 0
      rw [C.basisForm_zero i j hu]
      rfl
    rw [hz,zero_mul]

lemma evaluation_smooth (u : MetricUnit g) (f : L2 A J α hs ht true)
    (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    C.evaluation g u f = unitEvaluation J g a.val a.property u := by
  classical
  simp only [evaluation,sum_apply]
  simp_rw [C.evaluationTerm_smooth_sum g _ u f a ha]
  rw [← Finset.sum_mul]
  have hp : ∑ i : C.centers, C.partition i u.val.proj = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using C.partition.sum_eq_one (mem_univ u.val.proj)
  rw [hp,one_mul]
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothInverse
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
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeSmoothInverse_left (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeSmoothInverse A J α hs ht D hD r hr ((hodgeSmoothShift A J α hs ht r ^ 3) a) = a :=
  (LinearEquiv.ofBijective _ (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr)).symm_apply_apply a
lemma hodgeSmoothInverse_right (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht r ^ 3) (hodgeSmoothInverse A J α hs ht D hD r hr a) = a :=
  (LinearEquiv.ofBijective _ (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr)).apply_symm_apply a

lemma hodgeSmoothInverse_spec (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true (hodgeSmoothInverse A J α hs ht D hD r hr a) =
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true a) := by
  rw [← hodgeSmoothInverse_right A J α hs ht D hD r hr a,
    hodgeRegularization_smoothShift_cube A J α hs ht r hr,
    hodgeSmoothInverse_left]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothCommutation
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma hodgeSmoothShift_commute (r s : ℝ) :
    Commute (hodgeSmoothShift A J α hs ht r) (hodgeSmoothShift A J α hs ht s) := by
  change (_ : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true) = _
  simp only [hodgeSmoothShift,add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
  module

omit [T2Space X] in
lemma hodgeSmoothShift_cubes_commute (r s : ℝ) (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht r^3) ((hodgeSmoothShift A J α hs ht s^3) a) =
      (hodgeSmoothShift A J α hs ht s^3) ((hodgeSmoothShift A J α hs ht r^3) a) := by
  have h := ((hodgeSmoothShift_commute A J α hs ht r s).pow_pow 3 3).eq
  exact congrArg (fun L : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true => L a) h

lemma hodgeSmoothInverse_commute (r : ℝ) (hr : 0 < r) (s : ℝ)
    (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht s^3) (hodgeSmoothInverse A J α hs ht D hD r hr a) =
      hodgeSmoothInverse A J α hs ht D hD r hr ((hodgeSmoothShift A J α hs ht s^3) a) := by
  apply (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr).injective
  dsimp only
  rw [hodgeSmoothShift_cubes_commute A J α hs ht r s,
    hodgeSmoothInverse_right,hodgeSmoothInverse_right]

lemma hodgeSmoothFamily_spec (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true (hodgeSmoothFamily A J α hs ht D hD r a) =
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true a) := by
  simp only [hodgeSmoothFamily,dite_eq_left hr,LinearEquiv.coe_coe,hodgeSmoothInverse_spec]

lemma hodgeSmoothFamily_graph (r : ℝ) (hr : 0 < r) (s : ℝ)
    (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht s^3)
      (hodgeSmoothFamily A J α hs ht D hD r a)) =
      hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht s^3) a)) := by
  simp only [hodgeSmoothFamily,dite_eq_left hr,LinearEquiv.coe_coe,
    hodgeSmoothInverse_commute,hodgeSmoothInverse_spec]

omit [T2Space X] in
lemma hodgeRegularization_twice_tendsto (a : L2 A J α hs ht true) :
    Tendsto (fun r : ℝ => hodgeRegularization A J α hs ht r (hodgeRegularization A J α hs ht r a))
      (𝓝[>] 0) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun r : ℝ => 2*‖hodgeRegularization A J α hs ht r a-a‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (((hodgeRegularization_tendsto A J α hs ht a).sub (tendsto_const_nhds (x:=a))).norm.const_mul 2)
  apply squeeze_zero (fun r => norm_nonneg _) _ h
  intro r
  have hb := hodgeRegularization_norm_le A J α hs ht r (hodgeRegularization A J α hs ht r a-a)
  rw [map_sub] at hb
  have ht := norm_add_le (hodgeRegularization A J α hs ht r (hodgeRegularization A J α hs ht r a)-
    hodgeRegularization A J α hs ht r a) (hodgeRegularization A J α hs ht r a-a)
  rw [sub_add_sub_cancel] at ht
  linarith
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma evaluationApply_smooth (f : L2 A J α hs ht true) (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    C.evaluationApply g f = smoothUnitEvaluation J g a := by
  ext u
  exact C.evaluation_smooth g u f a ha
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

lemma hodgeSmoothFamily_evaluation (r : ℝ) (hr : 0 < r)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (C : HodgeSmoothingCover A J α hs ht D hD 1 zero_lt_one)
    (a : PreL2 A J α hs ht true) :
    smoothUnitEvaluation J g (hodgeSmoothFamily A J α hs ht D hD r a) =
      C.evaluationApply g (hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht 1^3) a))) := by
  rw [← hodgeSmoothFamily_graph A J α hs ht D hD r hr 1 a]
  exact (C.evaluationApply_smooth g _ _
    (hodgeRegularization_smoothShift_cube A J α hs ht 1 zero_lt_one _)).symm

lemma hodgeSmoothFamily_twice_evaluation (r : ℝ) (hr : 0 < r)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (C : HodgeSmoothingCover A J α hs ht D hD 1 zero_lt_one)
    (a : PreL2 A J α hs ht true) :
    smoothUnitEvaluation J g
      (hodgeSmoothFamily A J α hs ht D hD r (hodgeSmoothFamily A J α hs ht D hD r a)) =
      C.evaluationApply g (hodgeRegularization A J α hs ht r
        (hodgeRegularization A J α hs ht r
          (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht 1^3) a)))) := by
  rw [hodgeSmoothFamily_evaluation A J α hs ht D hD r hr g C,
    hodgeSmoothFamily_graph A J α hs ht D hD r hr 1 a]

lemma hodgeSmoothFamily_twice_uniform_tendsto
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => smoothUnitEvaluation J g
      (hodgeSmoothFamily A J α hs ht D hD r (hodgeSmoothFamily A J α hs ht D hD r a)))
      (𝓝[>] 0) (𝓝 (smoothUnitEvaluation J g a)) := by
  let C := hodgeSmoothingCover A J α hs ht D hD 1 zero_lt_one
  let b := smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht 1^3) a)
  have he : C.evaluationApply g b = smoothUnitEvaluation J g a :=
    C.evaluationApply_smooth g b a (hodgeRegularization_smoothShift_cube A J α hs ht 1 zero_lt_one a)
  have hl := (C.evaluationApply g).continuous.tendsto b |>.comp
    (hodgeRegularization_twice_tendsto A J α hs ht b)
  rw [he] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hodgeSmoothFamily_twice_evaluation A J α hs ht D hD r hr g C a).symm
end TamingCompatibility.GeometricHilbert

end
end

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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel

lemma hodgePositiveCurrentFamily_pair
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    ⟪hodgePositiveCurrentFamily A J α hs ht D hD g μ r,smoothL2 A J α hs ht true a⟫ =
      unitMeasureCurrent J g μ (hodgeSmoothFamily A J α hs ht D hD r a) := by
  simp only [hodgePositiveCurrentFamily,dite_eq_left hr]
  rw [HodgeSmoothingCover.regularize_pair]
  apply integral_congr_ae
  filter_upwards [] with u
  exact HodgeSmoothingCover.evaluation_smooth _ g u _ _
    (hodgeSmoothFamily_spec A J α hs ht D hD r hr a).symm

lemma hodgePositiveCurrentFamily_twice_pair_tendsto
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => ⟪hodgePositiveCurrentFamily A J α hs ht D hD g μ r,
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true a)⟫)
      (𝓝[>] 0) (𝓝 (unitMeasureCurrent J g μ a)) := by
  have hl := (unitIntegral g μ).continuous.tendsto (smoothUnitEvaluation J g a) |>.comp
    (hodgeSmoothFamily_twice_uniform_tendsto A J α hs ht D hD g a)
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [← hodgeSmoothFamily_spec A J α hs ht D hD r hr a,
    hodgePositiveCurrentFamily_pair A J α hs ht D hD g μ r hr]
  rfl

lemma hodgePositiveCurrentFamily_anti_cross_tendsto_oai
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => ⟪hodgePositiveCurrentFamily A J α hs ht D hD g μ r,
      hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a))⟫)
      (𝓝[>] 0) (𝓝 0) := by
  have h := hodgePositiveCurrentFamily_twice_pair_tendsto A J α hs ht D hD g μ
    (preAntiProjection A J α hs ht a)
  have he : unitMeasureCurrent J g μ (preAntiProjection A J α hs ht a) = 0 :=
    unitMeasureCurrent_antiInvariantPart J g μ a.val a.property
  rw [he] at h
  exact h

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.hodgePositiveCurrentFamily_anti_cross_tendsto_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.hodgePositiveCurrentFamily_anti_cross_tendsto_oai.{u_1}
