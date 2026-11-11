-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:13:57.979086+00:00
-- url     : https://prove2.me/submissions/434541ce-55c4-41ed-b171-b18cc88d9b4c

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalRescaleH1
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
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance instFactLeENNRealOfNat_solutions_1_rccb13e_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
lemma schwartzToH_zero (f : 𝓢(E,F)) : schwartzToH 0 f = f.toLp 2 (volume : Measure E) := by
  simp [schwartzToH]

end TamingCompatibility.HilbertSobolev

end
end

end
end
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothLaplacian
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

lemma regularize_smoothShift_cube (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (a : PreL2 A J α hs ht true) :
    ⟪C.regularize g μ,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ =
      unitMeasureCurrent J g μ ⟨a.val,a.property⟩ := by
  rw [C.regularize_pair]
  change (∫ u, C.evaluation g u _ ∂μ) = ∫ u, unitEvaluation J g a.val a.property u ∂μ
  apply integral_congr_ae
  filter_upwards [] with u
  exact C.evaluation_smooth g u _ a (hodgeRegularization_smoothShift_cube A J α hs ht r hr a)
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
include D hD in

lemma hodgeSmoothShift_cube_dense (r : ℝ) (hr : 0 < r) :
    DenseRange (fun a : PreL2 A J α hs ht true =>
      smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)) := by
  apply (smoothL2_dense A J α hs ht true).mono
  rintro _ ⟨f,rfl⟩
  obtain ⟨b,hb⟩ := hodgeRegularization_smooth A J α hs ht D hD r hr f
  refine ⟨b,?_⟩
  apply hodgeRegularization_injective A J α hs ht r hr
  rw [hodgeRegularization_smoothShift_cube A J α hs ht r hr,hb]
end TamingCompatibility.GeometricHilbert

end
end

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
local instance instNormedSpaceRealTangentSpaceSpaceModel_2_rccb13e_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
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

end GeometricHilbert
end TamingCompatibility

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

lemma preAntiProjection_smooth (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a) =
      l2AntiProjection A J α hs ht (smoothL2 A J α hs ht true a) :=
  (l2AntiProjection_smooth A J α hs ht a).symm

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open scoped RealInnerProductSpace
lemma linmap_shift_cube {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : E →ₗ[ℝ] E) (r : ℝ) :
    (LinearMap.id + r^2 • d)^3 = LinearMap.id +
      (3*r^2) • d + (3*r^4) • d^2 + r^6 • d^3 := by
  simp only [pow_succ,pow_zero,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    Module.End.one_eq_id]
  module
lemma linmap_shift_cube_commutator {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d p : E →ₗ[ℝ] E) (r : ℝ) :
    ((LinearMap.id + r^2 • d)^3).comp p - p.comp ((LinearMap.id + r^2 • d)^3) =
      (3*r^2) • (d.comp p - p.comp d) +
      (3*r^4) • ((d^2).comp p - p.comp (d^2)) +
      r^6 • ((d^3).comp p - p.comp (d^3)) := by
  rw [linmap_shift_cube]
  simp only [LinearMap.add_comp,LinearMap.comp_add,LinearMap.smul_comp,
    LinearMap.comp_smul,LinearMap.id_comp,LinearMap.comp_id]
  module
end TamingCompatibility
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeCubeCommutator_expand (r : ℝ) : hodgeCubeCommutator A J α hs ht r =
    (3*r^2) • hodgePowerCommutator A J α hs ht 1 +
      (3*r^4) • hodgePowerCommutator A J α hs ht 2 +
      r^6 • hodgePowerCommutator A J α hs ht 3 := by
  simpa only [hodgeCubeCommutator,hodgePowerCommutator,hodgeSmoothShift,pow_one] using
    linmap_shift_cube_commutator (hodgeLaplacian A J α hs ht)
      (preAntiProjection A J α hs ht).toLinearMap r

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUniformCommutator
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
namespace TamingCompatibility.ComplexMatrix
lemma embed_norm_sq {n : ℕ} (v : R n) : ‖embed n v‖^2 = ‖v‖^2 := by
  simp only [PiLp.norm_sq_eq_of_L2,embed_apply,Complex.norm_real,Real.norm_eq_abs]
end TamingCompatibility.ComplexMatrix
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge ManifoldVolume GeometricChart HodgeFrame
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X)
  (D : GeometricChart.Data J α ht p)
lemma rawVector_norm_sq (a : TwoForm X) {z : Space} (hz : z ∈ D.domain) :
    ‖rawVector J α ht p D a z‖^2 =
      GeometricAdjoint.pairing J α ht a a ((extChartAt Model p).symm z) := by
  rw [← real_inner_self_eq_norm_sq]
  change ⟪coordinates (fun i => D.frame i z) _,coordinates (fun i => D.frame i z) _⟫ = _
  rw [coordinates_pairing (coordinateMetric J α ht p z) (by simp [Space]) _ (D.frame_gram z hz),
    pairing_chart J α ht p (Or.inr rfl) a a (D.domain_subset hz)]
end TamingCompatibility.HodgeChart
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeRawSchwartz_spec (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (f : PreL2 A J α hs ht true) :
    (hodgeRawSchwartz A J α hs ht D hD p τ χ f : 𝓢'(Space,C 6)) =
      smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f)) := by
  rw [hodgeRawDistribution_smooth,product_schwartz]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma hodgeRawSchwartz_norm_sq (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    {U : Set Space} (hU : U ⊆ (D p).domain)
    (hχ : tsupport χ ⊆ U) (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (f : PreL2 A J α hs ht true) (z : Space) :
    ‖hodgeRawSchwartz A J α hs ht D hD p τ χ f z‖^2 =
      ‖χ z‖^2 * ‖rawVector J α ht p.val (D p).toData f.val z‖^2 := by
  rw [hodgeRawSchwartz,SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
    SchwartzMap.postcompCLM_apply]
  rw [norm_smul,mul_pow,embed_norm_sq]
  by_cases hz : z ∈ tsupport χ
  · rw [cutoff_realVector_raw A J α ht (fun p => (D p).toData) hD p f τ
      (hU (hχ hz)) (hτ z (hχ hz))]
  · rw [image_eq_zero_of_notMem_tsupport hz,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_mul]

lemma hodgeRawSchwartz_H0_norm_sq (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    {U : Set Space} (hU : U ⊆ (D p).domain)
    (hχ : tsupport χ ⊆ U) (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (f : PreL2 A J α hs ht true) (u : H Space (C 6) 0)
    (hu : toDistribution Space (C 6) 0 u =
      smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))) :
    ‖u‖^2 = ∫ z, ‖χ z‖^2 * ‖rawVector J α ht p.val (D p).toData f.val z‖^2 := by
  have he : u = schwartzToH 0 (hodgeRawSchwartz A J α hs ht D hD p τ χ f) := by
    apply toDistribution_injective 0
    rw [hu,schwartzToH_spec,hodgeRawSchwartz_spec]
  rw [he,schwartzToH_zero,GeometricChart.schwartz_l2_norm_sq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (hodgeRawSchwartz_norm_sq A J α hs ht D hD p τ χ hU hχ hτ f)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWeightNorm
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
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

namespace LocalWeight
variable (p : A.centers) (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
  (η : X → ℝ) (hη : ContMDiff Model 𝓘(ℝ,ℝ) ∞ η)
  (hηU : tsupport η ⊆ (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' U)

omit [MeasurableSpace X] [BorelSpace X] in
lemma halfDensity_apply (z : Space) : halfDensity A J α hs ht D p U hU hUD η hη hηU z =
    coordinateFunction A p η z * Real.sqrt (chartDensity J α p.val z) := rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma halfDensity_support : tsupport (halfDensity A J α hs ht D p U hU hUD η hη hηU) ⊆ U :=
  (tsupport_smul_subset_left _ _).trans (coordinateFunction_support A p U η hηU)

omit [MeasurableSpace X] [BorelSpace X] in
lemma halfDensity_compact : HasCompactSupport (halfDensity A J α hs ht D p U hU hUD η hη hηU : Space → ℝ) :=
  SchwartzCutoff.compact (coordinateFunction_smooth_compact A p U η hη hηU).2

lemma integral_weight_norm (f : PreL2 A J α hs ht true) :
    (∫ x, (η x)^2 * GeometricAdjoint.pairing J α ht f.val f.val x ∂geometricVolume A J α) =
      ∫ z, (halfDensity A J α hs ht D p U hU hUD η hη hηU z)^2 *
        ‖rawVector J α ht p.val (D p).toData f.val z‖^2 := by
  have hc : Continuous (fun x => (η x)^2 * GeometricAdjoint.pairing J α ht f.val f.val x) :=
    (hη.continuous.pow 2).mul (GeometricAdjoint.pairing_two_smooth J α hs ht f.property f.property).continuous
  have hsq : tsupport (fun x => (η x)^2) ⊆ tsupport η := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η))
  have hsource : tsupport (fun x => (η x)^2 * GeometricAdjoint.pairing J α ht f.val f.val x) ⊆
      (extChartAt Model p.val).source := (tsupport_mul_subset_left.trans hsq).trans (fun _ hx => (hηU hx).1)
  rw [integral_geometricVolume_coordinate A J α hs ht p.val _ hc hsource,
    ← integral_indicator (isOpen_extChartAt_target p.val).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [halfDensity_apply]
  by_cases hz : z ∈ (extChartAt Model p.val).target
  · rw [indicator_of_mem hz]
    by_cases he : coordinateFunction A p η z = 0
    · have he' : η ((extChartAt Model p.val).symm z) = 0 := by
        simpa only [coordinateFunction,indicator_of_mem hz] using he
      simp only [he,he',zero_mul,zero_pow (by decide : 2 ≠ 0),mul_zero]
    · have hzU := coordinateFunction_support A p U η hηU (subset_closure he)
      rw [rawVector_norm_sq J α ht p.val (D p).toData f.val (hUD hzU),mul_pow,
        Real.sq_sqrt (show 0 ≤ chartDensity J α p.val z from Real.sqrt_nonneg _)]
      simp only [coordinateFunction,indicator_of_mem hz]
      ring
  · rw [indicator_of_notMem hz]
    simp only [coordinateFunction,indicator_of_notMem hz,zero_mul,zero_pow (by decide : 2 ≠ 0)]

lemma integral_weight_H0_norm (τ : 𝓢(Space,ℝ))
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (f : PreL2 A J α hs ht true) (u : H Space (C 6) 0)
    (hu : toDistribution Space (C 6) 0 u =
      smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM
        (halfDensity A J α hs ht D p U hU hUD η hη hηU))
        (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))) :
    (∫ x, (η x)^2 * GeometricAdjoint.pairing J α ht f.val f.val x ∂geometricVolume A J α) = ‖u‖^2 := by
  rw [integral_weight_norm A J α hs ht D p U hU hUD η hη hηU f]
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM (halfDensity A J α hs ht D p U hU hUD η hη hηU)
  have hχ : tsupport χ ⊆ U :=
    (tsupport_comp_subset (g := Complex.ofRealCLM) (map_zero _) _).trans
      (halfDensity_support A J α hs ht D p U hU hUD η hη hηU)
  rw [hodgeRawSchwartz_H0_norm_sq A J α hs ht D hD p τ χ hUD hχ hτ f u hu]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]
end LocalWeight
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCommutatorCover
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
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeCommutatorCover
variable {k : ℕ} (C : HodgeCommutatorCover A J α hs ht D hD k)

omit [T2Space X] in
lemma weight_support (i : C.centers) : tsupport (C.weight i) ⊆ (C.patch i).neighborhood :=
  LocalWeight.halfDensity_support A J α hs ht D (C.patch i).chart (C.patch i).neighborhood
    (C.patch i).neighborhood_open (C.patch i).neighborhood_subset
    (C.partition i) (C.partition i).contMDiff (C.subordinate i)

omit [T2Space X] in
lemma weight_compact (i : C.centers) : HasCompactSupport (C.weight i : Space → ℝ) :=
  LocalWeight.halfDensity_compact A J α hs ht D (C.patch i).chart (C.patch i).neighborhood
    (C.patch i).neighborhood_open (C.patch i).neighborhood_subset
    (C.partition i) (C.partition i).contMDiff (C.subordinate i)

omit [T2Space X] in

lemma weighted_norm_eq (i : C.centers) (a : PreL2 A J α hs ht true)
    (u : H Space (ComplexMatrix.C 6) 0)
    (hu : toDistribution Space (ComplexMatrix.C 6) 0 u =
      smulLeftCLM (ComplexMatrix.C 6)
        (SchwartzMap.postcompCLM Complex.ofRealCLM (C.weight i))
        (hodgeRawDistribution A J α hs ht D hD (C.patch i).chart (C.patch i).reciprocal
          (hodgeSmooth A J α hs ht a))) :
    (∫ x, (C.partition i x)^2 * GeometricAdjoint.pairing J α ht a.val a.val x
      ∂geometricVolume A J α) = ‖u‖^2 :=
  LocalWeight.integral_weight_H0_norm A J α hs ht D hD
    (C.patch i).chart (C.patch i).neighborhood (C.patch i).neighborhood_open
    (C.patch i).neighborhood_subset (C.partition i) (C.partition i).contMDiff
    (C.subordinate i) (C.patch i).reciprocal (C.patch i).reciprocal_spec a u hu

omit [T2Space X] in

lemma local_integral_bound (i : C.centers) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ f : PreL2 A J α hs ht true,
        C.weightedSquare i (hodgePowerCommutator A J α hs ht (k+1) f) ≤
          (B*(r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖)^2 := by
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM (C.weight i)
  have hχ : tsupport χ ⊆ (C.patch i).neighborhood :=
    (tsupport_comp_subset (g := Complex.ofRealCLM) (map_zero _) _).trans (C.weight_support i)
  have hc : HasCompactSupport (χ : Space → ℂ) :=
    (C.weight_compact i).of_isClosed_subset (isClosed_tsupport χ)
      (postcomp_real_tsupport (C.weight i))
  obtain ⟨B,hB,hreg⟩ := (C.patch i).estimate χ hc hχ
  refine ⟨B,hB,fun r hr hr1 f => ?_⟩
  obtain ⟨T,hT,hTb⟩ := hreg r hr hr1
  have hTf := hT f
  have hbf := hTb (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f))
  generalize hfcomm : hodgePowerCommutator A J α hs ht (k+1) f = a at hTf ⊢
  generalize hu : T (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f)) = u at hTf hbf
  rw [weightedSquare,C.weighted_norm_eq i a u hTf]
  have hb := pow_le_pow_left₀ (norm_nonneg _) hbf 2
  simpa only [LinearIsometry.norm_map] using hb

omit [T2Space X] in
lemma partition_sum (x : X) : ∑ i : C.centers, C.partition i x = 1 := by
  rw [← finsum_eq_sum_of_fintype]
  exact C.partition.sum_eq_one (mem_univ x)

include C in
omit [T2Space X] in

lemma global_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
    ∀ f : PreL2 A J α hs ht true,
      ‖hodgePowerCommutator A J α hs ht (k+1) f‖ ≤
        B*(r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖ := by
  classical
  let := geometricVolume_finite A J α hs ht
  choose b hb hbound using C.local_integral_bound
  let N : ℝ := Fintype.card C.centers
  let K : ℝ := N * ∑ i : C.centers, (b i)^2
  have hN : 0 ≤ N := by dsimp [N] <;> positivity
  have hK : 0 ≤ K := mul_nonneg hN (Finset.sum_nonneg fun i _ => sq_nonneg (b i))
  refine ⟨Real.sqrt K,Real.sqrt_nonneg _,fun r hr hr1 f => ?_⟩
  let a := hodgePowerCommutator A J α hs ht (k+1) f
  let F : X → ℝ := GeometricAdjoint.pairing J α ht a.val a.val
  have hFc : Continuous F := (GeometricAdjoint.pairing_two_smooth J α hs ht a.property a.property).continuous
  have hF : Integrable F (geometricVolume A J α) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hW (i : C.centers) : Integrable (fun x => (C.partition i x)^2*F x) (geometricVolume A J α) :=
    (((C.partition i).contMDiff.continuous.pow 2).mul hFc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (x : X) : F x ≤ N * ∑ i : C.centers, (C.partition i x)^2*F x := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : C.centers => C.partition i x)
    rw [C.partition_sum x,one_pow] at h
    have hn : 0 ≤ F x := MetricForms.pairing_self_nonneg (GeometricAdjoint.pointMetric J α ht x) (a.val x)
    simpa only [N,one_mul,Finset.card_univ,Finset.sum_mul,mul_assoc] using mul_le_mul_of_nonneg_right h hn
  have hI := integral_mono hF ((integrable_finsetSum Finset.univ (fun i _ => hW i)).const_mul N) hp
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun i _ => hW i)] at hI
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset C.centers)) => hbound i r hr hr1 f)
  have hsquared : ‖a‖^2 ≤ K * ((r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖)^2 := by
    rw [preL2_norm_sq]
    exact hI.trans ((mul_le_mul_of_nonneg_left hsum hN).trans_eq (by
      simp_rw [mul_pow]
      rw [← Finset.sum_mul,← Finset.sum_mul]
      dsimp [K]
      ring))
  have hroot : (Real.sqrt K*(r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖)^2 =
      K * ((r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖)^2 := by
    rw [mul_assoc,mul_pow,Real.sq_sqrt hK]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  exact hsquared.trans_eq hroot.symm
end HodgeCommutatorCover

lemma hodge_power_commutator_global_bound
    (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J)
    (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
    (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
    (k : ℕ) (hk : k ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ f : PreL2 A J α hs ht true,
        ‖hodgePowerCommutator A J α hs ht (k+1) f‖ ≤
          B*(r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖ :=
  (hodgeCommutatorCover A J α hs ht D hD k hk).global_bound
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCubeBound
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
lemma norm_cube_combination_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (B₁ B₂ B₃ N : ℝ) (u₁ u₂ u₃ : E)
    (h₁ : ‖u₁‖ ≤ B₁*r⁻¹*N) (h₂ : ‖u₂‖ ≤ B₂*(r⁻¹)^3*N)
    (h₃ : ‖u₃‖ ≤ B₃*(r⁻¹)^5*N) :
    ‖(3*r^2) • u₁ + (3*r^4) • u₂ + r^6 • u₃‖ ≤ (3*B₁+3*B₂+B₃)*r*N := by
  calc
    _ ≤ ‖(3*r^2) • u₁‖ + ‖(3*r^4) • u₂‖ + ‖r^6 • u₃‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (3*r^2)*‖u₁‖+(3*r^4)*‖u₂‖+r^6*‖u₃‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ) ≤ 3*r^2),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 3*r^4),abs_of_nonneg (by positivity : (0:ℝ) ≤ r^6)]
    _ ≤ (3*r^2)*(B₁*r⁻¹*N)+(3*r^4)*(B₂*(r⁻¹)^3*N)+r^6*(B₃*(r⁻¹)^5*N) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
        (mul_le_mul_of_nonneg_left h₂ (by positivity)))
        (mul_le_mul_of_nonneg_left h₃ (by positivity))
    _ = _ := by field_simp [hr.ne']
end TamingCompatibility
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include D hD in

lemma hodge_cube_commutator_global_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ f : PreL2 A J α hs ht true,
        ‖hodgeCubeCommutator A J α hs ht r f‖ ≤
          B*r*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖ := by
  obtain ⟨B₁,hB₁,h₁⟩ := hodge_power_commutator_global_bound A J α hs ht D hD 0 (by norm_num)
  obtain ⟨B₂,hB₂,h₂⟩ := hodge_power_commutator_global_bound A J α hs ht D hD 1 (by norm_num)
  obtain ⟨B₃,hB₃,h₃⟩ := hodge_power_commutator_global_bound A J α hs ht D hD 2 (by norm_num)
  refine ⟨3*B₁+3*B₂+B₃,by positivity,fun r hr hr1 f => ?_⟩
  rw [hodgeCubeCommutator_expand]
  simp only [LinearMap.add_apply,LinearMap.smul_apply]
  apply norm_cube_combination_le r hr
  · simpa only [Nat.mul_zero,Nat.zero_add,pow_one] using h₁ r hr hr1 f
  · exact h₂ r hr hr1 f
  · exact h₃ r hr hr1 f
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
lemma hodgeCubeCommutator_apply (r : ℝ) (a : PreL2 A J α hs ht true) :
    hodgeCubeCommutator A J α hs ht r a =
      (hodgeSmoothShift A J α hs ht r ^ 3) (preAntiProjection A J α hs ht a) -
        preAntiProjection A J α hs ht ((hodgeSmoothShift A J α hs ht r ^ 3) a) := rfl
lemma hodgeCubeCommutator_pairing (r : ℝ) (a : PreL2 A J α hs ht true)
    (U : L2 A J α hs ht true) :
    ⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫ =
      ⟪U,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
        (preAntiProjection A J α hs ht a))⟫ -
          ⟪l2AntiProjection A J α hs ht U,
            smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ := by
  rw [hodgeCubeCommutator_apply, map_sub, inner_sub_right, preAntiProjection_smooth,
    l2AntiProjection_self_adjoint]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open scoped RealInnerProductSpace
lemma norm_le_of_dense_pair_bound {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (d : F → E) (hd : DenseRange d) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ f, |⟪v,d f⟫| ≤ B*‖d f‖) : ‖v‖ ≤ B := by
  have hall (y : E) : |⟪v,y⟫| ≤ B*‖y‖ :=
    hd.induction_on y (isClosed_le (continuous_const.inner continuous_id).abs
      (continuous_const.mul continuous_norm)) h
  have hi := hall v
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hi
  by_cases hz : ‖v‖ = 0
  · simpa only [hz] using hB
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith
end TamingCompatibility
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in

lemma hodge_relative_antiprojection :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ U : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪U,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (preAntiProjection A J α hs ht a))⟫ = 0) →
        ‖l2AntiProjection A J α hs ht U‖ ≤ B*r*‖U‖ := by
  obtain ⟨B,hB,hbound⟩ := hodge_cube_commutator_global_bound A J α hs ht D hD
  refine ⟨B,hB,fun r hr hr1 U hU => ?_⟩
  apply norm_le_of_dense_pair_bound _ _ (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr)
    (B*r*‖U‖) (by positivity)
  intro a
  have he : ⟪l2AntiProjection A J α hs ht U,
      smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ =
      -⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫ := by
    rw [hodgeCubeCommutator_pairing,hU,zero_sub,neg_neg]
  calc
    _ = |⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫| := by rw [he,abs_neg]
    _ ≤ ‖U‖*‖smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖U‖*(B*r*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖) := by
      rw [(smoothL2 A J α hs ht true).norm_map,(smoothL2 A J α hs ht true).norm_map]
      exact mul_le_mul_of_nonneg_left (hbound r hr hr1 a) (norm_nonneg U)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMixing
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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

lemma hodge_regularized_positive_current_mixing :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
        (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ],
        ‖l2AntiProjection A J α hs ht (C.regularize g μ)‖ ≤ B*r*‖C.regularize g μ‖ := by
  obtain ⟨B,hB,hbound⟩ := hodge_relative_antiprojection A J α hs ht D hD
  refine ⟨B,hB,fun r hr hr1 C g μ _ => hbound r hr hr1 _ ?_⟩
  intro a
  rw [C.regularize_smoothShift_cube]
  exact unitMeasureCurrent_antiInvariantPart J g μ a.val a.property
end TamingCompatibility.GeometricHilbert

end
end

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
include D hD in

lemma hodge_relative_complement :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ U : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪U,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (a-preAntiProjection A J α hs ht a))⟫ = 0) →
        ‖U-l2AntiProjection A J α hs ht U‖ ≤ B*r*‖U‖ := by
  obtain ⟨B,hB,hbound⟩ := hodge_cube_commutator_global_bound A J α hs ht D hD
  refine ⟨B,hB,fun r hr hr1 U hU => ?_⟩
  apply norm_le_of_dense_pair_bound _ _ (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr)
    (B*r*‖U‖) (by positivity)
  intro a
  have hz := hU a
  rw [map_sub,map_sub,inner_sub_right,sub_eq_zero] at hz
  have he : ⟪U-l2AntiProjection A J α hs ht U,
      smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ =
      ⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫ := by
    rw [hodgeCubeCommutator_pairing,inner_sub_left,hz]
  calc
    _ = |⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫| := by rw [he]
    _ ≤ ‖U‖*‖smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖U‖*(B*r*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖) := by
      rw [(smoothL2 A J α hs ht true).norm_map,(smoothL2 A J α hs ht true).norm_map]
      exact mul_le_mul_of_nonneg_left (hbound r hr hr1 a) (norm_nonneg U)
    _ = _ := by ring

omit [T2Space X] in
lemma antiProjection_pair_split (U V : L2 A J α hs ht true) :
    ⟪U,V⟫ = ⟪l2AntiProjection A J α hs ht U,V⟫ +
      ⟪U,V-l2AntiProjection A J α hs ht V⟫ := by
  rw [l2AntiProjection_self_adjoint,inner_sub_right]
  ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

lemma hodge_regularized_positive_current_cross_oai :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
        (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
        (V : L2 A J α hs ht true),
        (∀ a : PreL2 A J α hs ht true,
          ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (a-preAntiProjection A J α hs ht a))⟫ = 0) →
        |⟪C.regularize g μ,V⟫| ≤ B*r*‖C.regularize g μ‖*‖V‖ := by
  obtain ⟨B₁,hB₁,h₁⟩ := hodge_regularized_positive_current_mixing A J α hs ht D hD
  obtain ⟨B₂,hB₂,h₂⟩ := hodge_relative_complement A J α hs ht D hD
  refine ⟨B₁+B₂,add_nonneg hB₁ hB₂,fun r hr hr1 C g μ _ V hV => ?_⟩
  let U := C.regularize g μ
  have hb₁ := h₁ r hr hr1 C g μ
  have hb₂ := h₂ r hr hr1 V hV
  change |⟪U,V⟫| ≤ _
  calc
    _ ≤ |⟪l2AntiProjection A J α hs ht U,V⟫| +
        |⟪U,V-l2AntiProjection A J α hs ht V⟫| := by
      rw [antiProjection_pair_split A J α hs ht U V]
      exact abs_add_le _ _
    _ ≤ ‖l2AntiProjection A J α hs ht U‖*‖V‖ +
        ‖U‖*‖V-l2AntiProjection A J α hs ht V‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (B₁*r*‖U‖)*‖V‖ + ‖U‖*(B₂*r*‖V‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hb₁ (norm_nonneg V))
        (mul_le_mul_of_nonneg_left hb₂ (norm_nonneg U))
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross_oai.{u_1}
