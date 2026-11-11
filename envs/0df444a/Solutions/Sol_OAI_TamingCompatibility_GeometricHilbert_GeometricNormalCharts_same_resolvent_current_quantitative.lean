-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:20:13.28414+00:00
-- url     : https://prove2.me/submissions/62f1ba3a-ec8e-417f-98c1-ab11afde133e

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc033
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_smooth_spatial
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_HodgeSmoothingCover_pairingGammaTail_integral

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

lemma kernel_inner (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (x : A) (y : B) (a : F) (b : G) :
    ⟪a,kernel E D x y b⟫ = ⟪(E x).adjoint a,(D y).adjoint b⟫ := by
  exact (ContinuousLinearMap.adjoint_inner_left (E x) ((D y).adjoint b) a).symm

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

lemma regularize_kernel_pair [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (v : A → F) (w : B → G)
    (hv : Integrable (fun x => (E x).adjoint (v x)) μ)
    (hw : Integrable (fun y => (D y).adjoint (w y)) ν) :
    ⟪regularize μ E v,regularize ν D w⟫ =
      ∫ x, ∫ y, ⟪v x,kernel E D x y (w y)⟫ ∂ν ∂μ := by
  rw [regularize_pair μ E v hv]
  apply integral_congr_ae
  filter_upwards [] with x
  have h := ((innerSL ℝ (v x)).comp (E x)).integral_comp_comm hw
  simpa only [regularize,ContinuousLinearMap.comp_apply,innerSL_apply_apply,kernel] using h.symm

end TamingCompatibility.HilbertKernel

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

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraKernel
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
namespace TamingCompatibility.GeometricHilbert.VolterraBounds
open _root_.MeasureTheory Set Metric
open scoped Topology
variable {X B : Type*} [PseudoMetricSpace X]

lemma weight_one_le (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    1 ≤ weight N t x y := by
  apply one_le_pow₀
  have := div_nonneg (dist_nonneg (x := x) (y := y)) (Real.sqrt_pos.2 ht).le
  linarith

lemma weight_pos (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    0 < weight N t x y := lt_of_lt_of_le zero_lt_one (weight_one_le N ht x y)

end TamingCompatibility.GeometricHilbert.VolterraBounds

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelForms
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma framePairing_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (framePairing A J α ht E a) := by
  unfold framePairing
  apply (squareMass_inv_smooth A).continuous.smul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro j _
  exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (globalFrame_smooth J α ht A E hE hs p j)).continuous.smul continuous_const

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalGamma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

lemma continuous_kernel_nonneg_of_smooth_tests (μ : Measure X) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (K : X → X → ℝ)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (htest : ∀ φ ψ : X → ℝ, ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ →
      ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ → (∀ x, 0 ≤ φ x) → (∀ y, 0 ≤ ψ y) →
      0 ≤ ∫ x, ∫ y, φ x*ψ y*K x y ∂μ ∂μ) :
    ∀ x y, 0 ≤ K x y := by
  intro x y
  by_contra hn
  have hneg : K x y < 0 := lt_of_not_ge hn
  have hnh : {p : X × X | K p.1 p.2 < 0} ∈ 𝓝 (x,y) :=
    (isOpen_lt hK continuous_const).mem_nhds hneg
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hnh
  obtain ⟨φ,_,hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := Model) x).mem_iff.mp hU
  obtain ⟨ψ,_,hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := Model) y).mem_iff.mp hV
  let F : X × X → ℝ := fun p => φ p.1*ψ p.2*K p.1 p.2
  have hFc : Continuous F := (φ.continuous.comp continuous_fst).mul
    (ψ.continuous.comp continuous_snd) |>.mul hK
  have hFi : Integrable F (μ.prod μ) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFneg : F ≤ 0 := by
    intro p
    by_cases hp : φ p.1 = 0
    · simp only [F,hp,zero_mul]; rfl
    by_cases hq : ψ p.2 = 0
    · simp only [F,hq,mul_zero,zero_mul]; rfl
    have hn := hUV ⟨hφ (subset_tsupport _ hp),hψ (subset_tsupport _ hq)⟩
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg φ.nonneg ψ.nonneg) hn.le
  have hzero : ∫ p, (-F p) ∂μ.prod μ = 0 := by
    have ht := htest φ ψ φ.contMDiff ψ.contMDiff (fun _ => φ.nonneg) (fun _ => ψ.nonneg)
    have hpos : 0 ≤ ∫ p, F p ∂μ.prod μ := by
      rw [integral_prod F hFi]
      exact ht
    rw [integral_neg]
    exact neg_eq_zero.mpr (le_antisymm (integral_nonpos hFneg) hpos)
  have hae : (fun p => -F p) =ᵐ[μ.prod μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p => neg_nonneg.mpr (hFneg p)) hFi.neg).mp hzero
  have heq := Measure.eq_of_ae_eq hae hFc.neg continuous_const
  have hxy := congrFun heq (x,y)
  have hKzero : K x y = 0 := by
    simpa only [F,φ.eq_one,ψ.eq_one,one_mul,Pi.zero_apply,neg_eq_zero] using hxy
  exact hneg.ne hKzero

lemma continuous_kernel_le_of_smooth_tests (μ : Measure X) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (K L : X → X → ℝ)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (hL : Continuous (fun p : X × X => L p.1 p.2))
    (htest : ∀ φ ψ : X → ℝ, ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ →
      ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ → (∀ x, 0 ≤ φ x) → (∀ y, 0 ≤ ψ y) →
      (∫ x, ∫ y, φ x*ψ y*K x y ∂μ ∂μ) ≤ ∫ x, ∫ y, φ x*ψ y*L x y ∂μ ∂μ) :
    ∀ x y, K x y ≤ L x y := by
  have hn := continuous_kernel_nonneg_of_smooth_tests μ (fun x y => L x y-K x y)
    (hL.sub hK) ?_
  · intro x y
    exact sub_nonneg.mp (hn x y)
  intro φ ψ hφ hψ hp hq
  have hFi (Z : X → X → ℝ) (hZ : Continuous (fun p : X × X => Z p.1 p.2)) :
      Integrable (fun p : X × X => φ p.1*ψ p.2*Z p.1 p.2) (μ.prod μ) :=
    (((hφ.continuous.comp continuous_fst).mul (hψ.continuous.comp continuous_snd)).mul hZ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_prod _ (hFi (fun x y => L x y-K x y) (hL.sub hK))]
  simp_rw [mul_sub]
  rw [integral_sub (hFi L hL) (hFi K hK),integral_prod _ (hFi L hL),integral_prod _ (hFi K hK)]
  exact sub_nonneg.mpr (htest φ ψ hφ hψ hp hq)

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_fun_smul (a : TwoForm X) (φ : X → ℝ) (x : X) (v : FrameSpace A) :
    framePairing A J α ht E (fun y => φ y • a y) x v =
      φ x * framePairing A J α ht E a x v := by
  erw [framePairing_apply,framePairing_apply]
  change X → MetricForms.Form Space 2 at a
  change (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2
    (φ x • a x)) (frameDecode J α ht A E x v) =
    φ x * (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2
      (a x)) (frameDecode J α ht A E x v)
  rw [map_smul,_root_.smul_apply,smul_eq_mul]

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma frame_kernel_pairing_continuous (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (a b : TwoForm X) (ha : IsSmooth a) (hb : IsSmooth b) :
    Continuous (fun p : X × X => framePairing A J α ht E a p.1
      (K p.1 p.2 (frameEncode J α ht A E p.2 (b p.2)))) :=
  ((framePairing_continuous A J α hs ht E hE a ha).comp continuous_fst).clm_apply
    (hK.clm_apply ((frameEncode_section_smooth J α ht A E hE hs b hb).continuous.comp continuous_snd))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingEvaluationTerm_continuous (b : PreL2 A J α hs ht true) (i : C.centers) (j : Fin 6) :
    Continuous (C.pairingEvaluationTerm b i j) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport (C.partition i)
  · have hc := (continuousOn_extChartAt _ _ (C.subordinate i hx).1).continuousAt
      ((isOpen_extChartAt_source _).mem_nhds (C.subordinate i hx).1)
    exact (GeometricAdjoint.pairing_two_smooth J α hs ht b.property
      (C.basisForm i j).property).continuous.continuousAt.smul
      (continuousAt_const.clm_comp ((C.patch i).smoothing.realEvaluation_continuous.continuousAt.comp hc))
  · apply (continuousAt_const (y := (0 : L2 A J α hs ht true →L[ℝ] ℝ))).congr_of_eventuallyEq
    have hn : ∀ᶠ y in 𝓝 x, y ∉ tsupport (C.partition i) :=
      (isClosed_tsupport (C.partition i)).isOpen_compl.mem_nhds hx
    filter_upwards [hn] with y hy
    unfold pairingEvaluationTerm
    have hz : GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val y = 0 := by
      change (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht y) 2 (b.val y))
        ((C.basisForm i j).val y) = 0
      erw [C.basisForm_zero i j hy,map_zero]
    rw [hz,zero_smul]

lemma pairingEvaluation_continuous (b : PreL2 A J α hs ht true) :
    Continuous (C.pairingEvaluation b) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact C.pairingEvaluationTerm_continuous b i j

lemma pairingEvaluationTerm_smooth_sum (b : PreL2 A J α hs ht true) (i : C.centers) (x : X)
    (f : L2 A J α hs ht true) (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    ∑ j : Fin 6, C.pairingEvaluationTerm b i j x f =
      C.partition i x * GeometricAdjoint.pairing J α ht b.val a.val x := by
  classical
  by_cases hx : x ∈ tsupport (C.partition i)
  · let aa : MetricForms.Form Space 2 := a.val x
    let bb : MetricForms.Form Space 2 := b.val x
    let v : Fin 6 → MetricForms.Form Space 2 := fun j => (C.basisForm i j).val x
    let c : Fin 6 → ℝ := fun j => (rawVector J α ht (C.patch i).chart.val
      (D (C.patch i).chart).toData a.val (extChartAt Model (C.patch i).chart.val x)) j
    let L : MetricForms.Form Space 2 →L[ℝ] ℝ :=
      MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 bb
    have he : (∑ j : Fin 6, c j • v j) = C.partition i x • aa :=
      C.basisForm_expansion i a.val hx
    have hl := congrArg L he
    change L (∑ j : Fin 6, c j • v j) = L (C.partition i x • aa) at hl
    simp only [map_sum,map_smul,smul_eq_mul] at hl
    change ∑ j : Fin 6, GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x *
      (((C.patch i).smoothing.realEvaluation (extChartAt Model (C.patch i).chart.val x) f) j) = _
    rw [(C.patch i).smoothing.realEvaluation_smooth f a ha (C.subordinate i hx).2]
    change ∑ j : Fin 6, L (v j) * c j = (C.partition i x) * L aa
    simpa only [mul_comm] using hl
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    apply Finset.sum_eq_zero
    intro j _
    change GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x * _ = 0
    have hz : GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x = 0 := by
      change (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 (b.val x))
        ((C.basisForm i j).val x) = 0
      erw [C.basisForm_zero i j hx,map_zero]
    rw [hz,zero_mul]

lemma pairingEvaluation_smooth (b : PreL2 A J α hs ht true) (x : X)
    (f : L2 A J α hs ht true) (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    C.pairingEvaluation b x f = GeometricAdjoint.pairing J α ht b.val a.val x := by
  simp only [pairingEvaluation,sum_apply]
  simp_rw [C.pairingEvaluationTerm_smooth_sum b _ x f a ha]
  rw [← Finset.sum_mul]
  have hp : ∑ i : C.centers, C.partition i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using C.partition.sum_eq_one (mem_univ x)
  rw [hp,one_mul]

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairingIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
omit [T2Space X] in
lemma hodgeRegularization_symmetric (r : ℝ) (u v : L2 A J α hs ht true) :
    ⟪hodgeRegularization A J α hs ht r u,v⟫ = ⟪u,hodgeRegularization A J α hs ht r v⟫ := by
  have hsym (f g : L2 A J α hs ht true) :
      ⟪hodgeResolvent A J α hs ht r f,g⟫ = ⟪f,hodgeResolvent A J α hs ht r g⟫ :=
    hodgeResolvent_symmetric A J α hs ht r f g
  change ⟪hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r u)),v⟫ =
    ⟪u,hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r v))⟫
  rw [hsym,hsym,hsym]

namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingEvaluationVector_continuous (b : PreL2 A J α hs ht true) :
    Continuous (C.pairingEvaluationVector b) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.pairingEvaluation_continuous b)).clm_apply continuous_const

lemma pairingEvaluationVector_integrable (b : PreL2 A J α hs ht true) :
    Integrable (C.pairingEvaluationVector b) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (C.pairingEvaluationVector_continuous b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma pairingEvaluationVector_pair (b : PreL2 A J α hs ht true) (f : L2 A J α hs ht true) :
    ⟪∫ x, C.pairingEvaluationVector b x ∂geometricVolume A J α,f⟫ =
      ∫ x, C.pairingEvaluation b x f ∂geometricVolume A J α := by
  have h := HilbertKernel.regularize_pair (geometricVolume A J α) (C.pairingEvaluation b)
    (fun _ => (1:ℝ)) (C.pairingEvaluationVector_integrable b) f
  simpa only [HilbertKernel.regularize,pairingEvaluationVector,Real.inner_apply,one_mul,mul_one] using h

lemma pairingEvaluationVector_integral (b : PreL2 A J α hs ht true) :
    ∫ x, C.pairingEvaluationVector b x ∂geometricVolume A J α =
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true b) := by
  apply ext_inner_right ℝ
  intro f
  refine (smoothL2_dense A J α hs ht true).induction_on f
    (_root_.isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro a
  obtain ⟨c,hc⟩ := hodgeRegularization_smooth A J α hs ht D hD r hr a
  rw [C.pairingEvaluationVector_pair,hodgeRegularization_symmetric,← hc,(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  unfold l2Pairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => C.pairingEvaluation_smooth b x _ c hc.symm

lemma pairingEvaluationVector_gram (a b : PreL2 A J α hs ht true) :
    (∫ x, ∫ y, ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
      ∂geometricVolume A J α ∂geometricVolume A J α) =
      ⟪(hodgeRegularization A J α hs ht r ^ 2) (smoothL2 A J α hs ht true a),
        smoothL2 A J α hs ht true b⟫ := by
  have h := HilbertKernel.regularize_kernel_pair (geometricVolume A J α) (geometricVolume A J α)
    (C.pairingEvaluation b) (C.pairingEvaluation a) (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (C.pairingEvaluationVector_integrable b) (C.pairingEvaluationVector_integrable a)
  simp only [HilbertKernel.kernel_inner] at h
  change ⟪∫ x, C.pairingEvaluationVector b x ∂geometricVolume A J α,
    ∫ y, C.pairingEvaluationVector a y ∂geometricVolume A J α⟫ =
      ∫ x, ∫ y, ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
        ∂geometricVolume A J α ∂geometricVolume A J α at h
  rw [← h,C.pairingEvaluationVector_integral,C.pairingEvaluationVector_integral,real_inner_comm]
  rw [← hodgeRegularization_symmetric]
  rfl

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgePairingHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {ρ : ℝ} {hρ : 0 < ρ} (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)

lemma pairingHeatEvaluation_continuous (b : PreL2 A J α hs ht true) :
    Continuous (C.pairingHeatEvaluation b) :=
  (C.pairingEvaluation_continuous b).clm_comp continuous_const

lemma pairingHeatVector_continuous (b : PreL2 A J α hs ht true) :
    Continuous (C.pairingHeatVector b) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.pairingHeatEvaluation_continuous b)).clm_apply continuous_const

lemma pairingGammaTail_continuous (T : ℝ) (hT : 0 ≤ T) (r : ℝ)
    (a b : PreL2 A J α hs ht true) :
    Continuous (fun p : X × X => C.pairingGammaTail T hT r a b p.1 p.2) :=
  ((C.pairingHeatVector_continuous b).comp continuous_fst).inner
    ((hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)).continuous.comp
      ((C.pairingHeatVector_continuous a).comp continuous_snd))

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairingLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingEvaluation_smul_of (a b : PreL2 A J α hs ht true) (x : X) (c : ℝ)
    (hab : a.val x = c • b.val x) : C.pairingEvaluation a x = c • C.pairingEvaluation b x := by
  have hp (i : C.centers) (j : Fin 6) :
      GeometricAdjoint.pairing J α ht a.val (C.basisForm i j).val x =
        c * GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x := by
    change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
      (a.val x : MetricForms.Form Space 2) ((C.basisForm i j).val x : MetricForms.Form Space 2) =
      c * MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
        (b.val x : MetricForms.Form Space 2) ((C.basisForm i j).val x : MetricForms.Form Space 2)
    erw [hab,MetricForms.pairing_smul_left]
  simp only [pairingEvaluation,pairingEvaluationTerm,hp,Finset.smul_sum,smul_smul]

lemma pairingEvaluationVector_smul_of (a b : PreL2 A J α hs ht true) (x : X) (c : ℝ)
    (hab : a.val x = c • b.val x) :
    C.pairingEvaluationVector a x = c • C.pairingEvaluationVector b x := by
  unfold pairingEvaluationVector
  rw [C.pairingEvaluation_smul_of a b x c hab]
  simp only [map_smul,_root_.smul_apply]

lemma pairingHeatVector_smul_of (a b : PreL2 A J α hs ht true) (x : X) (c : ℝ)
    (hab : a.val x = c • b.val x) :
    C.pairingHeatVector a x = c • C.pairingHeatVector b x := by
  unfold pairingHeatVector pairingHeatEvaluation
  rw [C.pairingEvaluation_smul_of a b x c hab,ContinuousLinearMap.smul_comp]
  simp only [map_smul,_root_.smul_apply]

lemma pairingGammaTail_smul_of (T : ℝ) (hT : 0 ≤ T) (s : ℝ)
    (a a' b b' : PreL2 A J α hs ht true) (x y : X) (c d : ℝ)
    (ha : a'.val y = c • a.val y) (hb : b'.val x = d • b.val x) :
    C.pairingGammaTail T hT s a' b' x y = d*c*C.pairingGammaTail T hT s a b x y := by
  unfold pairingGammaTail
  rw [C.pairingHeatVector_smul_of b' b x d hb,C.pairingHeatVector_smul_of a' a y c ha,
    map_smul,real_inner_smul_left,real_inner_smul_right,mul_assoc]

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeActualGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {E : ∀ p : A.centers, ParametrixData J α ht p.val}
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
  {r ρ : ℝ} {hr : 0 < r} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD r hr)
  (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
attribute [local irreducible] framePairing

include hE in
lemma actual_gram_eq_of_smooth_tests (T : ℝ) (hT : 0 ≤ T)
    (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (htest : ∀ a b : PreL2 A J α hs ht true,
      (∫ x, ∫ y, ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
        ∂geometricVolume A J α ∂geometricVolume A J α) =
      ∫ x, ∫ y, (framePairing A J α ht E b.val x
        (K x y (frameEncode J α ht A E y (a.val y))) +
        B.pairingGammaTail T hT r a b x y) ∂geometricVolume A J α ∂geometricVolume A J α)
    (a b : PreL2 A J α hs ht true) (x y : X) :
    ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫ =
      framePairing A J α ht E b.val x (K x y (frameEncode J α ht A E y (a.val y))) +
        B.pairingGammaTail T hT r a b x y := by
  let := geometricVolume_finite A J α hs ht
  let := geometricVolume_openPos A J α hs ht
  let F : X → X → ℝ := fun x y => ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
  let G : X → X → ℝ := fun x y =>
    framePairing A J α ht E b.val x (K x y (frameEncode J α ht A E y (a.val y))) +
      B.pairingGammaTail T hT r a b x y
  have hF : Continuous (fun p : X × X => F p.1 p.2) :=
    ((C.pairingEvaluationVector_continuous b).comp continuous_fst).inner
      ((C.pairingEvaluationVector_continuous a).comp continuous_snd)
  have hG : Continuous (fun p : X × X => G p.1 p.2) :=
    (frame_kernel_pairing_continuous A J α hs ht E hE K hK b.val a.val b.property a.property).add
      (B.pairingGammaTail_continuous T hT r a b)
  have hlocal (φ ψ : X → ℝ) (hφ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ)
      (hψ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ) :
      (∫ x, ∫ y, φ x*ψ y*F x y ∂geometricVolume A J α ∂geometricVolume A J α) =
      ∫ x, ∫ y, φ x*ψ y*G x y ∂geometricVolume A J α ∂geometricVolume A J α := by
    let a' : PreL2 A J α hs ht true := ⟨fun y => ψ y • a.val y,Smooth.fun_smul hψ a.property⟩
    let b' : PreL2 A J α hs ht true := ⟨fun x => φ x • b.val x,Smooth.fun_smul hφ b.property⟩
    have heF (x y : X) : ⟪C.pairingEvaluationVector b' x,C.pairingEvaluationVector a' y⟫ =
        φ x*ψ y*F x y := by
      rw [C.pairingEvaluationVector_smul_of b' b x (φ x) rfl,
        C.pairingEvaluationVector_smul_of a' a y (ψ y) rfl,
        real_inner_smul_left,real_inner_smul_right,mul_assoc]
    have heK (x y : X) : framePairing A J α ht E b'.val x
        (K x y (frameEncode J α ht A E y (a'.val y))) =
        φ x*ψ y*framePairing A J α ht E b.val x
          (K x y (frameEncode J α ht A E y (a.val y))) := by
      change framePairing A J α ht E (fun x => φ x • b.val x) x
        (K x y (frameEncode J α ht A E y (ψ y • a.val y))) = _
      erw [framePairing_fun_smul,map_smul,map_smul,map_smul]
      simp only [smul_eq_mul]
      ring
    have heG (x y : X) : framePairing A J α ht E b'.val x
        (K x y (frameEncode J α ht A E y (a'.val y))) + B.pairingGammaTail T hT r a' b' x y =
        φ x*ψ y*G x y := by
      rw [heK,B.pairingGammaTail_smul_of T hT r a a' b b' x y (ψ y) (φ x) rfl rfl]
      exact (mul_add _ _ _).symm
    simpa only [heF,heG] using htest a' b'
  apply le_antisymm
  · exact continuous_kernel_le_of_smooth_tests (geometricVolume A J α) F G hF hG
      (fun φ ψ hφ hψ _ _ => (hlocal φ ψ hφ hψ).le) x y
  · exact continuous_kernel_le_of_smooth_tests (geometricVolume A J α) G F hG hF
      (fun φ ψ hφ hψ _ _ => (hlocal φ ψ hφ hψ).ge) x y

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeActualResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_actual_gram (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L Q : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T Q (globalCorrection J α ht A E T) ∧
      (∀ r : ℝ, 0 < r →
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
      (∀ r : ℝ, 0 < r → ∀ x y : X,
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
            ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
            ((1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ a b : PreL2 A J α hs ht true, ∀ x y : X,
        ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫ =
          framePairing A J α ht E b.val x
            ((HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y +
              HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y)
                (frameEncode J α ht A E y (a.val y))) +
          B.pairingGammaTail T hT.le r a b x y := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,Q,hT,hT1,hL,hQ,hcont,hbound,hpair⟩ :=
    same_resolvent_smooth_spatial A J α hs ht E hE D hD n
  refine ⟨T,L,Q,hT,hT1,hL,hQ,hcont,hbound,?_⟩
  intro r hr C ρ hρ B hρT a b x y
  let KL := HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r
  let KE := HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r
  have hcL : Continuous (fun p : X × X => KL p.1 p.2) := (hcont r hr).1
  have hcE : Continuous (fun p : X × X => KE p.1 p.2) := (hcont r hr).2
  apply actual_gram_eq_of_smooth_tests hE C B T hT.le (fun x y => KL x y + KE x y)
    (hcL.add hcE) ?_ a b x y
  intro a b
  let FL : X → X → ℝ := fun x y => framePairing A J α ht E b.val x
    (KL x y (frameEncode J α ht A E y (a.val y)))
  let FE : X → X → ℝ := fun x y => framePairing A J α ht E b.val x
    (KE x y (frameEncode J α ht A E y (a.val y)))
  let FT : X → X → ℝ := B.pairingGammaTail T hT.le r a b
  have hFL : Continuous (fun p : X × X => FL p.1 p.2) :=
    frame_kernel_pairing_continuous A J α hs ht E hE KL hcL b.val a.val b.property a.property
  have hFE : Continuous (fun p : X × X => FE p.1 p.2) :=
    frame_kernel_pairing_continuous A J α hs ht E hE KE hcE b.val a.val b.property a.property
  have hFT : Continuous (fun p : X × X => FT p.1 p.2) :=
    B.pairingGammaTail_continuous T hT.le r a b
  have hIL := hFL.integrable_of_hasCompactSupport (μ := (geometricVolume A J α).prod (geometricVolume A J α))
    (HasCompactSupport.of_compactSpace _)
  have hIE := hFE.integrable_of_hasCompactSupport (μ := (geometricVolume A J α).prod (geometricVolume A J α))
    (HasCompactSupport.of_compactSpace _)
  have hIT := hFT.integrable_of_hasCompactSupport (μ := (geometricVolume A J α).prod (geometricVolume A J α))
    (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, ∫ y, ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
      ∂geometricVolume A J α ∂geometricVolume A J α) =
      (∫ x, ∫ y, FL x y ∂geometricVolume A J α ∂geometricVolume A J α) +
      (∫ x, ∫ y, FE x y ∂geometricVolume A J α ∂geometricVolume A J α) +
      (∫ x, ∫ y, FT x y ∂geometricVolume A J α ∂geometricVolume A J α) := by
    have hsL := integral_integral_swap_of_hasCompactSupport (f := FL) (μ := geometricVolume A J α) (ν := geometricVolume A J α) hFL
      (HasCompactSupport.of_compactSpace _)
    have hsE := integral_integral_swap_of_hasCompactSupport (f := FE) (μ := geometricVolume A J α) (ν := geometricVolume A J α) hFE
      (HasCompactSupport.of_compactSpace _)
    rw [C.pairingEvaluationVector_gram,hpair a r hr b,← hsL,← hsE,
      B.pairingGammaTail_integral T hT.le r hr hρT a b]
  rw [he]
  have hz : (∫ x, ∫ y, FL x y + FE x y + FT x y ∂geometricVolume A J α ∂geometricVolume A J α) =
      (∫ x, ∫ y, FL x y ∂geometricVolume A J α ∂geometricVolume A J α) +
      (∫ x, ∫ y, FE x y ∂geometricVolume A J α ∂geometricVolume A J α) +
      (∫ x, ∫ y, FT x y ∂geometricVolume A J α ∂geometricVolume A J α) := by
    have hIS : Integrable (fun p : X × X => FL p.1 p.2 + FE p.1 p.2 + FT p.1 p.2)
        ((geometricVolume A J α).prod (geometricVolume A J α)) := (hIL.add hIE).add hIT
    rw [← integral_prod _ hIS]
    have hsum := integral_add (hIL.add hIE) hIT
    simp only [Pi.add_apply] at hsum
    rw [hsum]
    have hsum' := integral_add hIL hIE
    rw [hsum',integral_prod _ hIL,integral_prod _ hIE,integral_prod _ hIT]
  rw [← hz]
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [_root_.add_apply,map_add,FL,FE,FT]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

attribute [local irreducible] frameDecode unitFrameDirection

include hE in
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_direction (a : TwoForm X) (u : MetricUnit g) :
    framePairing A J α ht E a u.val.proj (unitFrameDirection A J α ht E g u) =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  have he := globalFrame_full_resolution J α ht A E hE a u.val.proj
  have hh := congrArg (fun b : MetricForms.Form Space 2 =>
    b ![u.val.2,J.endomorphism u.val.proj u.val.2]) he
  let v : A.centers → Fin 6 → MetricForms.Form Space 2 := fun p j =>
    globalFrame J α ht A E p j u.val.proj
  let c : A.centers → Fin 6 → ℝ := fun p j => (squareMass A u.val.proj)⁻¹ *
    GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) u.val.proj
  change (∑ p : A.centers, ∑ j : Fin 6, c p j • v p j)
    ![u.val.2,J.endomorphism u.val.proj u.val.2] =
    a u.val.proj ![u.val.2,J.endomorphism u.val.proj u.val.2] at hh
  simp only [ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul] at hh
  calc
    _ = ∑ p : A.centers, ∑ j : Fin 6,
        ((squareMass A u.val.proj)⁻¹ * GeometricAdjoint.pairing J α ht a
          (globalFrame J α ht A E p j) u.val.proj) *
          eval (globalFrame J α ht A E p j) u.val.proj u.val.2
            (J.endomorphism u.val.proj u.val.2) := by
      simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul,Finset.mul_sum,unitFrameDirection,mul_assoc]
    _ = _ := hh

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitDual_pairing (a : TwoForm X) (u : MetricUnit g) :
    GeometricAdjoint.pairing J α ht (unitDual A J α hs ht E hE g u).val a u.val.proj =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  rw [← framePairing_direction A J α ht E hE g a u,framePairing_apply]
  exact MetricForms.pairing_symm _ _ _

variable {A J α hs ht E hE g}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
  {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingEvaluation_unitDual (u : MetricUnit g) :
    C.pairingEvaluation (unitDual A J α hs ht E hE g u) u.val.proj = C.evaluation g u := by
  have he : (fun f => C.pairingEvaluation (unitDual A J α hs ht E hE g u) u.val.proj f) =
      (fun f => C.evaluation g u f) :=
    (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr).equalizer
      (C.pairingEvaluation (unitDual A J α hs ht E hE g u) u.val.proj).continuous
      (C.evaluation g u).continuous (by
        funext a
        dsimp only [Function.comp_apply]
        rw [C.pairingEvaluation_smooth _ _ _ a
          (hodgeRegularization_smoothShift_cube A J α hs ht r hr a),
          C.evaluation_smooth g u _ a (hodgeRegularization_smoothShift_cube A J α hs ht r hr a)]
        exact unitDual_pairing A J α hs ht E hE g a.val u)
  ext f
  exact congrFun he f

lemma pairingEvaluationVector_unitDual (u : MetricUnit g) :
    C.pairingEvaluationVector (unitDual A J α hs ht E hE g u) u.val.proj = C.evaluationVector g u := by
  unfold HodgeSmoothingCover.pairingEvaluationVector HodgeSmoothingCover.evaluationVector
  rw [pairingEvaluation_unitDual C u]

lemma pairingHeatVector_unitDual (u : MetricUnit g) :
    C.pairingHeatVector (unitDual A J α hs ht E hE g u) u.val.proj = C.heatEvaluationVector g u := by
  unfold HodgeSmoothingCover.pairingHeatVector HodgeSmoothingCover.heatEvaluationVector
    HodgeSmoothingCover.pairingHeatEvaluation HodgeSmoothingCover.heatEvaluation
  rw [pairingEvaluation_unitDual C u]

lemma pairingGammaTail_unitDual (T : ℝ) (hT : 0 ≤ T) (s : ℝ) (u v : MetricUnit g) :
    C.pairingGammaTail T hT s (unitDual A J α hs ht E hE g v)
      (unitDual A J α hs ht E hE g u) u.val.proj v.val.proj = C.gammaTailKernel g T hT s u v := by
  unfold HodgeSmoothingCover.pairingGammaTail HodgeSmoothingCover.gammaTailKernel
  rw [pairingHeatVector_unitDual C u,pairingHeatVector_unitDual C v]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolvent2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_current_kernel (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L Q : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T Q (globalCorrection J α ht A E T) ∧
      (∀ r : ℝ, 0 < r →
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
      (∀ r : ℝ, 0 < r → ∀ x y : X,
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
            ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
            ((1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type),
        ∀ u v : MetricUnit g,
        C.innerKernel g u v =
          framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj
            ((HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r u.val.proj v.val.proj +
              HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r u.val.proj v.val.proj)
                (frameEncode J α ht A E v.val.proj ((unitDual A J α hs ht E hE g v).val v.val.proj))) +
          B.gammaTailKernel g T hT.le r u v := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,Q,hT,hT1,hL,hQ,hcont,hbound,hgram⟩ :=
    same_resolvent_actual_gram A J α hs ht E hE D hD n
  refine ⟨T,L,Q,hT,hT1,hL,hQ,hcont,hbound,?_⟩
  intro r hr C ρ hρ B hρT g u v
  have h := hgram r hr C ρ hρ B hρT
    (unitDual A J α hs ht E hE g v) (unitDual A J α hs ht E hE g u) u.val.proj v.val.proj
  rw [pairingEvaluationVector_unitDual C u,pairingEvaluationVector_unitDual C v,
    pairingGammaTail_unitDual B T hT.le r u v] at h
  exact h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

include hs hE in
lemma unitFrameDirection_continuous : Continuous (unitFrameDirection A J α ht E g) := by
  apply continuous_pi
  intro i
  exact (unitEvaluation J g (globalFrame J α ht A E i.1 i.2)
    (globalFrame_smooth J α ht A E hE hs i.1 i.2)).continuous

lemma unitFrameFunctional_eq (u : MetricUnit g) :
    unitFrameFunctional A J α ht E g u =
      framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj := by
  unfold unitFrameFunctional framePairing
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  rw [unitDual_pairing A J α hs ht E hE g (globalFrame J α ht A E p j) u]
  rfl

lemma unitDual_encode (u : MetricUnit g) :
    frameEncode J α ht A E u.val.proj ((unitDual A J α hs ht E hE g u).val u.val.proj) =
      unitFrameDirection A J α ht E g u := by
  ext i
  rw [frameEncode_apply]
  exact unitDual_pairing A J α hs ht E hE g (globalFrame J α ht A E i.1 i.2) u

include hs hE in
lemma unitFrameFunctional_continuous : Continuous (unitFrameFunctional A J α ht E g) := by
  have hb : Continuous (fun u : MetricUnit g => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  unfold unitFrameFunctional
  apply ((squareMass_inv_smooth A).continuous.comp hb).smul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply (p,j)).comp
    (unitFrameDirection_continuous A J α hs ht E hE g)).smul continuous_const

include hs hE in
lemma unitFrame_uniform : ∃ B : ℝ, 0 ≤ B ∧ ∀ u : MetricUnit g,
    ‖unitFrameDirection A J α ht E g u‖ ≤ B ∧ ‖unitFrameFunctional A J α ht E g u‖ ≤ B := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (unitFrameDirection_continuous A J α hs ht E hE g).continuousOn
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (unitFrameFunctional_continuous A J α hs ht E hE g).continuousOn
  refine ⟨max 0 (max B C),le_max_left _ _,fun u => ⟨?_,?_⟩⟩
  · exact (hB u (mem_univ _)).trans ((le_max_left B C).trans (le_max_right _ _))
  · exact (hC u (mem_univ _)).trans ((le_max_right B C).trans (le_max_right _ _))

lemma currentFrame_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ u v : MetricUnit g,
    ∀ K : FrameSpace A →L[ℝ] FrameSpace A,
    |framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj
      (K (frameEncode J α ht A E v.val.proj ((unitDual A J α hs ht E hE g v).val v.val.proj)))| ≤
        B * ‖K‖ := by
  obtain ⟨B,hB,hbound⟩ := unitFrame_uniform A J α hs ht E hE g
  refine ⟨B^2,sq_nonneg _,fun u v K => ?_⟩
  rw [unitDual_encode,← unitFrameFunctional_eq A J α hs ht E hE g]
  calc
    _ ≤ ‖unitFrameFunctional A J α ht E g u‖ * ‖K (unitFrameDirection A J α ht E g v)‖ :=
      (unitFrameFunctional A J α ht E g u).le_opNorm _
    _ ≤ B * (‖K‖ * B) := mul_le_mul (hbound u).2
      ((K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbound v).1 (norm_nonneg _)))
      (norm_nonneg _) hB
    _ = B^2*‖K‖ := by ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma unitCurrentKernel_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ K : X → X → FrameSpace A →L[ℝ] FrameSpace A, ∀ u v : MetricUnit g,
      |unitCurrentKernel A J α ht E g K u v| ≤ B * ‖K u.val.proj v.val.proj‖ := by
  obtain ⟨B,hB,hbound⟩ := currentFrame_bound A J α hs ht E hE g
  refine ⟨B,hB,fun K u v => ?_⟩
  have h := hbound u v (K u.val.proj v.val.proj)
  rw [unitDual_encode,← unitFrameFunctional_eq A J α hs ht E hE g] at h
  exact h

include hE D hD in
lemma same_resolvent_current_quantitative_oai (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T C : ℝ, ∃ hT : 0 < T, 0 ≤ C ∧ T ≤ 1 ∧
      (∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| ≤ C/r^4 ∧
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤ C/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ u v : MetricUnit g,
        S.innerKernel g u v =
          unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v +
          unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v +
          B.gammaTailKernel g T hT.le r u v := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,Q,hT,hT1,_,_,_,hbound,hker⟩ :=
    same_resolvent_current_kernel A J α hs ht E hE D hD n
  obtain ⟨B,hB,hscalar⟩ := unitCurrentKernel_bound A J α hs ht E hE g
  let a := (1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1)
  let b := (1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1)
  let C := max 0 (max (B*a) (B*b))
  have hCa : B*a ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCb : B*b ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T,C,hT,le_max_left _ _,hT1,?_,?_⟩
  · intro r hr u v
    have hw : 0 ≤ VolterraBounds.weight n (r^2) u.val.proj v.val.proj :=
      (VolterraBounds.weight_pos n (sq_pos_of_pos hr) _ _).le
    have htransfer (K : X → X → FrameSpace A →L[ℝ] FrameSpace A) (c : ℝ) (k : ℕ)
        (hk : VolterraBounds.weight n (r^2) u.val.proj v.val.proj * ‖K u.val.proj v.val.proj‖ ≤ c/r^k)
        (hc : B*c ≤ C) :
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitCurrentKernel A J α ht E g K u v| ≤ C/r^k := by
      calc
        _ ≤ VolterraBounds.weight n (r^2) u.val.proj v.val.proj * (B*‖K u.val.proj v.val.proj‖) :=
          mul_le_mul_of_nonneg_left (hscalar K u v) hw
        _ = B*(VolterraBounds.weight n (r^2) u.val.proj v.val.proj * ‖K u.val.proj v.val.proj‖) := by ring
        _ ≤ B*(c/r^k) := mul_le_mul_of_nonneg_left hk hB
        _ = (B*c)/r^k := by ring
        _ ≤ C/r^k := div_le_div_of_nonneg_right hc (pow_nonneg hr.le _)
    exact ⟨htransfer _ a 4 (hbound r hr u.val.proj v.val.proj).1 hCa,
      htransfer _ b 2 (hbound r hr u.val.proj v.val.proj).2 hCb⟩
  · intro r hr S ρ hρ R hρT u v
    have h := hker r hr S ρ hρ R hρT g u v
    rw [unitDual_encode,← unitFrameFunctional_eq A J α hs ht E hE g,
      _root_.add_apply,map_add] at h
    exact h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative_oai.{u_1}
