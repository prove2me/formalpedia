-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:42.537369+00:00
-- url     : https://prove2.me/submissions/3d9afb96-c87c-48c0-bfa5-682fb191ef3f

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc024

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalSymbol
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

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftData
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
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
lemma closedLiftOfInverse_pullback_sub
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) (p : X) (z : Space) :
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val (extChartAt Model p).symm z -
      ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p).symm z =
      ManifoldForms.pullback (exteriorDerivative (codifferential J α ht (Gs f).val.val))
        (extChartAt Model p).symm z := by
  rw [closedLiftOfInverse_apply,ManifoldForms.pullback_add]
  exact add_sub_cancel_right _ _
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace

lemma frameVector_injective (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) :
    Function.Injective (frameVector b) := by
  apply (frameVector b).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  change frameVector b a = 0 at ha
  apply (pairing_self_eq_zero g a).mp
  rw [← frameVector_pairing g b hb a a,ha,inner_zero_left]

lemma frameVector_recover (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (u : V) :
    frameVector b (frameRecover g b u) = u := by
  ext j
  simp only [frameVector_apply,frameRecover,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  change (∑ i : Fin 4, u i * g.bilinear (b i) (b j)) = u j
  simp [hb]

lemma frameRecover_vector (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a : MetricForms.Form V 1) :
    frameRecover g b (frameVector b a) = a := by
  apply frameVector_injective g b hb
  exact frameVector_recover g b hb _

lemma frameRecover_smooth {U : Set V} (g : V → Metric V) (b : Fin 4 → V → V)
    (hg : ContDiffOn ℝ ∞ (fun z => (g z).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    ContDiffOn ℝ ∞ (fun z => frameRecover (g z) (fun i => b i z)) U := by
  unfold frameRecover
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_const.smulRight
    ((ofSubsingletonLIE (0 : Fin 1) : (V →L[ℝ] ℝ) ≃ₗᵢ[ℝ] MetricForms.Form V 1).contDiff.comp_contDiffOn
      (hg.clm_apply (hb i)))

end TamingCompatibility.LocalMatrixOperator

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

include hs in
lemma deltaA_smooth (i : Fin 4) : ContDiffOn ℝ ∞ (deltaA J α ht p D i) D.domain := by
  exact ((frameRecover_smooth (coordinateMetric J α ht p) D.frame
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth).clm_comp
    (normalA_smooth J α ht p D i)).neg

include hs in
lemma deltaB_smooth : ContDiffOn ℝ ∞ (deltaB J α ht p D) D.domain := by
  exact ((frameRecover_smooth (coordinateMetric J α ht p) D.frame
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth).clm_comp
    (normalB_smooth J α hs ht p D)).neg

include hs in
lemma delta_coefficient_expansion {a : TwoForm X} (ha : IsSmooth a)
    (hanti : antiInvariantPart J a = a) {z : Space} (hz : z ∈ D.domain) :
    ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z =
      (∑ i, deltaA J α ht p D i z
        (fderiv ℝ (rawPair J α ht p D a) z (EuclideanEnergy.e i))) +
          deltaB J α ht p D z (rawPair J α ht p D a z) := by
  have he := congrArg (frameRecover (coordinateMetric J α ht p z) (fun j => D.frame j z))
    (normal_delta J α hs ht p D ha hanti hz)
  rw [frameRecover_vector _ _ (D.frame_gram z hz)] at he
  rw [he]
  simp only [map_neg,map_add,map_sum,deltaA,deltaB,neg_apply,
    ContinuousLinearMap.comp_apply,Finset.sum_neg_distrib,neg_add_rev,add_comm]

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JetOperator
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
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap
open scoped SchwartzMap ContDiff LineDeriv
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma derivative_component (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (u : 𝓢(V,F)) (x : V) (ha : ∀ i, DifferentiableAt ℝ (a i) x)
    (hb : DifferentiableAt ℝ b x) (j : Fin 4) :
    fderiv ℝ (firstOrder a b u) x (e j) = derivativeComponent a b x j (value u x) := by
  have hu : DifferentiableAt ℝ (u : V → F) x := u.differentiableAt
  have hd (i : Fin 4) : DifferentiableAt ℝ (fun y => (a i y) ((∂_{e i} u) y)) x :=
    (ha i).clm_apply (∂_{e i} u).differentiableAt
  unfold firstOrder
  rw [fderiv_fun_add (DifferentiableAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hd i)) (hb.clm_apply hu),
    fderiv_fun_sum (fun i _ => hd i)]
  simp only [_root_.add_apply,_root_.sum_apply]
  simp_rw [fderiv_clm_apply (ha _) (SchwartzMap.differentiableAt _),fderiv_clm_apply hb hu]
  simp only [derivativeComponent,value,projZero,projOne,projTwo,_root_.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.flip_apply,_root_.sum_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,add_assoc]

lemma directional_reconstruct (L : V →L[ℝ] G) :
    (∑ j : Fin 4, (EuclideanSpace.proj j).smulRight (L (e j))) = L := by
  ext x
  have hx : x = ∑ j : Fin 4, x j • e j := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e] using
      ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x).symm
  calc
    _ = L (∑ j : Fin 4, x j • e j) := by simp only [_root_.sum_apply,
      ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,_root_.map_sum,map_smul]
    _ = L x := congrArg L hx.symm

lemma derivativeJet_spec (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (u : 𝓢(V,F)) (x : V) (ha : ∀ i, DifferentiableAt ℝ (a i) x)
    (hb : DifferentiableAt ℝ b x) :
    derivativeJet a b x (value u x) = fderiv ℝ (firstOrder a b u) x := by
  change (∑ j : Fin 4, (EuclideanSpace.proj j).smulRight
    (derivativeComponent a b x j (value u x))) = _
  simp_rw [← derivative_component a b u x ha hb]
  exact directional_reconstruct _

lemma exteriorJet_spec (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1) (u : 𝓢(V,F)) (x : V)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hb : DifferentiableAt ℝ b x) :
    exteriorJet a b x (value u x) = extDeriv (firstOrder a b u) x := by
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 1) ℝ V ℝ)
    (derivativeJet a b x (value u x)) = _
  rw [derivativeJet_spec a b u x ha hb]
  rfl

end TamingCompatibility.JetOperator

end
end

section
noncomputable section
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap Set
open scoped SchwartzMap ContDiff LineDeriv
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma derivativeComponent_smooth {U : Set V} (hU : IsOpen U)
    (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U) (j : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => derivativeComponent a b x j) U := by
  have hda (i : Fin 4) : ContDiffOn ℝ ∞ (fderiv ℝ (a i)) U :=
    (ha i).fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdb : ContDiffOn ℝ ∞ (fderiv ℝ b) U := hb.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold derivativeComponent
  exact ((ContDiffOn.sum (fun i _ => ((ha i).clm_comp contDiffOn_const).add
    (((hda i).clm_apply contDiffOn_const).clm_comp contDiffOn_const))).add
    (hb.clm_comp contDiffOn_const)).add
      ((hdb.clm_apply contDiffOn_const).clm_comp contDiffOn_const)

lemma derivativeJet_smooth {U : Set V} (hU : IsOpen U)
    (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (derivativeJet a b) U := by
  unfold derivativeJet
  exact ContDiffOn.sum (fun j _ => contDiffOn_const.clm_comp
    (derivativeComponent_smooth hU a b ha hb j))

lemma exteriorJet_smooth {U : Set V} (hU : IsOpen U)
    (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (exteriorJet a b) U :=
  contDiffOn_const.clm_comp (derivativeJet_smooth hU a b ha hb)

lemma exteriorJet_bounded {U K : Set V} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖exteriorJet a b x‖ ≤ C := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (f := exteriorJet a b)
    ((exteriorJet_smooth hU a b ha hb).continuousOn.mono hKU)
  exact ⟨max 0 C,le_max_left _ _,fun x hx => (hC x hx).trans (le_max_right _ _)⟩

end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawJetEstimate
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator GeometricAdjoint Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

include hs in
lemma deltaComplexA_smooth (i : Fin 4) : ContDiffOn ℝ ∞ (deltaComplexA J α ht p D i) D.domain :=
  (deltaA_smooth J α hs ht p D i).clm_comp contDiffOn_const
include hs in
lemma deltaComplexB_smooth : ContDiffOn ℝ ∞ (deltaComplexB J α ht p D) D.domain :=
  (deltaB_smooth J α hs ht p D).clm_comp contDiffOn_const

include hs in
lemma delta_local_representation {a : TwoForm X} (ha : IsSmooth a)
    (hanti : antiInvariantPart J a = a) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (u : 𝓢(Space,C 2)) (hrep : ∀ z ∈ U, rawPair J α ht p D a z = retract 2 (u z))
    {z : Space} (hz : z ∈ U) :
    ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z =
      JetOperator.firstOrder (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) u z := by
  have he : rawPair J α ht p D a =ᶠ[𝓝 z] fun y => retract 2 (u y) :=
    Filter.mem_of_superset (hU.mem_nhds hz) hrep
  have hfd : fderiv ℝ (rawPair J α ht p D a) z =
      (retract 2).comp (fderiv ℝ (u : Space → C 2) z) := by
    rw [he.fderiv_eq]
    exact ((retract 2).hasFDerivAt.comp z u.differentiableAt.hasFDerivAt).fderiv
  rw [delta_coefficient_expansion J α hs ht p D ha hanti (hUD hz),hfd,hrep z hz]
  simp only [JetOperator.firstOrder,deltaComplexA,deltaComplexB,ContinuousLinearMap.comp_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

include hs in
lemma ddstar_local_jet {a : TwoForm X} (ha : IsSmooth a)
    (hanti : antiInvariantPart J a = a) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (u : 𝓢(Space,C 2)) (hrep : ∀ z ∈ U, rawPair J α ht p D a z = retract 2 (u z))
    {z : Space} (hz : z ∈ U) :
    ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a))
      (extChartAt Model p).symm z =
        JetOperator.exteriorJet (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) z
          (JetOperator.value u z) := by
  have he : ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm =ᶠ[𝓝 z]
      JetOperator.firstOrder (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) u := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact delta_local_representation J α hs ht p D ha hanti hU hUD u hrep hy
  rw [pullback_exteriorDerivative _ (codifferential_smooth J α hs ht ha)
    (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) (D.domain_subset (hUD hz)),
    extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) (D.domain_subset (hUD hz)),he.extDeriv_eq]
  symm
  apply JetOperator.exteriorJet_spec
  · intro i
    exact ((deltaComplexA_smooth J α hs ht p D i).differentiableOn (by simp) z (hUD hz)).differentiableAt
      (D.domain_open.mem_nhds (hUD hz))
  · exact ((deltaComplexB_smooth J α hs ht p D).differentiableOn (by simp) z (hUD hz)).differentiableAt
      (D.domain_open.mem_nhds (hUD hz))

end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap Set LineDeriv
open scoped SchwartzMap ContDiff LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma schwartz_direction_basis (v : V) (u : 𝓢(V,F)) :
    ∂_{v} u = ∑ i : Fin 4, (v i) • ∂_{e i} u := by
  have he : v = ∑ i : Fin 4, v i • e i := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e] using
      ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v).symm
  conv_lhs => rw [he]
  simp only [lineDerivOp_left_sum,lineDerivOp_left_smul]

lemma directionOne_value (v : V) (u : 𝓢(V,F)) (x : V) :
    directionOne v (value u x) = (∂_{v} u) x := by
  rw [schwartz_direction_basis]
  simp only [directionOne,value,projOne,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']

lemma directionTwo_value (v w : V) (u : 𝓢(V,F)) (x : V) :
    directionTwo v w (value u x) = (∂_{w} (∂_{v} u)) x := by
  rw [schwartz_direction_basis v u]
  simp only [lineDerivOp_sum,lineDerivOp_smul]
  simp_rw [schwartz_direction_basis w]
  simp only [Finset.smul_sum,smul_smul,directionTwo,value,projTwo,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,ContinuousLinearMap.coe_snd']

lemma linearTransport_value (L : V ≃L[ℝ] V) (u : 𝓢(V,F)) (x : V) :
    linearTransport L (value u (L x)) =
      value (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L u) x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      change directionOne (L (e i)) (value u (L x)) = _
      rw [directionOne_value]
      simp only [value,SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply]
    · funext i j
      change directionTwo (L (e i)) (L (e j)) (value u (L x)) = _
      rw [directionTwo_value]
      simp only [value,SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply]

lemma value_recover_linear (L : V ≃L[ℝ] V) (u : 𝓢(V,F)) (x : V) :
    value u x = linearTransport L
      (value (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L.symm u) (L x)) := by
  rw [linearTransport_value]
  congr 1
  ext y
  simp

end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricScaledJet
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma localizedRawSchwartz_raw (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) {z : Space} (hz : z ∈ (D p).domain)
    (hτ : τ z * coordinateWeight A p z = 1) (hχ : χ z = 1) :
    retract 2 (localizedRawSchwartz A J α hs ht D hD p τ χ a z) =
      rawPair J α ht p.val (D p) a.val.val z := by
  simp only [localizedRawSchwartz,SchwartzMap.smulLeftCLM_apply χ.hasTemperateGrowth,hχ,one_smul,
    SchwartzMap.postcompCLM_apply,retract_embed]
  exact cutoff_realPair_raw A J α ht D hD p a.val τ hz hτ

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JetBasis
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
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap Set LineDeriv
open scoped SchwartzMap ContDiff LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]
lemma schwartz_direction_any_basis (b : Module.Basis ι ℝ V) (v : V) (u : 𝓢(V,F)) :
    ∂_{v} u = ∑ i : ι, b.repr v i • ∂_{b i} u := by
  have he : v = ∑ i : ι, b.repr v i • b i := (b.sum_repr v).symm
  conv_lhs => rw [he]
  simp only [lineDerivOp_left_sum,lineDerivOp_left_smul]
lemma basisDirectionOne_value (b : Module.Basis ι ℝ V) (v : V) (u : 𝓢(V,F)) (x : V) :
    basisDirectionOne b v (basisValue b u x) = (∂_{v} u) x := by
  rw [schwartz_direction_any_basis b]
  simp only [basisDirectionOne,basisValue,basisProjOne,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
lemma basisDirectionTwo_value (b : Module.Basis ι ℝ V) (v w : V) (u : 𝓢(V,F)) (x : V) :
    basisDirectionTwo b v w (basisValue b u x) = (∂_{w} (∂_{v} u)) x := by
  rw [schwartz_direction_any_basis b v u]
  simp only [lineDerivOp_sum,lineDerivOp_smul]
  simp_rw [schwartz_direction_any_basis b w]
  simp only [Finset.smul_sum,smul_smul,basisDirectionTwo,basisValue,basisProjTwo,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,ContinuousLinearMap.coe_snd']
lemma basisToCoordinate_value (b : Module.Basis ι ℝ V) (u : 𝓢(V,F)) (x : V) :
    basisToCoordinate b (basisValue b u x) = value u x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      exact basisDirectionOne_value b (e i) u x
    · funext i j
      exact basisDirectionTwo_value b (e i) (e j) u x
lemma basisValue_norm (b : ι → V) (u : 𝓢(V,F)) (x : V) :
    ‖basisValue b u x‖ ≤ ‖u x‖ + ∑ i : ι, ‖(∂_{b i} u) x‖ +
      ∑ i : ι, ∑ j : ι, ‖(∂_{b j} (∂_{b i} u)) x‖ := by
  have h1 : ‖(fun i : ι => (∂_{b i} u) x)‖ ≤ ∑ i : ι, ‖(∂_{b i} u) x‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
    intro i
    exact Finset.single_le_sum (f := fun i : ι => ‖(∂_{b i} u) x‖)
      (fun i _ => norm_nonneg ((∂_{b i} u) x)) (Finset.mem_univ i)
  have h2 : ‖(fun i : ι => fun j : ι => (∂_{b j} (∂_{b i} u)) x)‖ ≤
      ∑ i : ι, ∑ j : ι, ‖(∂_{b j} (∂_{b i} u)) x‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))).mpr
    intro i
    have hi : ‖(fun j : ι => (∂_{b j} (∂_{b i} u)) x)‖ ≤
        ∑ j : ι, ‖(∂_{b j} (∂_{b i} u)) x‖ := by
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg ((∂_{b j} (∂_{b i} u)) x)))).mpr
      intro j
      exact Finset.single_le_sum (f := fun j : ι => ‖(∂_{b j} (∂_{b i} u)) x‖)
        (fun j _ => norm_nonneg ((∂_{b j} (∂_{b i} u)) x)) (Finset.mem_univ j)
    exact hi.trans (Finset.single_le_sum
      (f := fun i : ι => ∑ j : ι, ‖(∂_{b j} (∂_{b i} u)) x‖)
      (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg ((∂_{b j} (∂_{b i} u)) x))) (Finset.mem_univ i))
  simp only [basisValue,Prod.norm_def]
  have hz0 := norm_nonneg (u x)
  have hz1 := norm_nonneg (fun i : ι => (∂_{b i} u) x)
  have hz2 := norm_nonneg (fun i j : ι => (∂_{b j} (∂_{b i} u)) x)
  apply max_le
  · linarith
  · apply max_le <;> linarith

lemma basis_linear_output_scaled_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : Jet F →L[ℝ] G) (L : V ≃L[ℝ] V) (b : Module.Basis ι ℝ V) (u : 𝓢(V,F)) (z : V)
    {r M : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h : let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L.symm u
      r*‖U (L z)‖ + r^2*∑ i, ‖(∂_{b i} U) (L z)‖ +
        r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} U)) (L z)‖ ≤ M) :
    r^3*‖T (value u z)‖ ≤ ‖T.comp ((linearTransport L).comp (basisToCoordinate b))‖*M := by
  let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L.symm u
  have h13 : r^3 ≤ r := by nlinarith [sq_nonneg r, mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have h23 : r^3 ≤ r^2 := by nlinarith [mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have hn : r^3*‖basisValue b U (L z)‖ ≤ M := by
    apply (mul_le_mul_of_nonneg_left (basisValue_norm b U (L z)) (by positivity : 0 ≤ r^3)).trans
    have ha := mul_le_mul_of_nonneg_right h13 (norm_nonneg (U (L z)))
    have hb := mul_le_mul_of_nonneg_right h23
      (show 0 ≤ ∑ i : ι, ‖(∂_{b i} U) (L z)‖ from Finset.sum_nonneg (fun i _ => norm_nonneg ((∂_{b i} U) (L z))))
    dsimp only at h
    change r*‖U (L z)‖ + r^2*∑ i, ‖(∂_{b i} U) (L z)‖ +
        r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} U)) (L z)‖ ≤ M at h
    nlinarith only [ha,hb,h]
  rw [value_recover_linear L u z,← basisToCoordinate_value b U (L z)]
  let T' := T.comp ((linearTransport L).comp (basisToCoordinate b))
  change r^3*‖T' (basisValue b U (L z))‖ ≤ ‖T'‖*M
  calc
    _ ≤ r^3*(‖T'‖*‖basisValue b U (L z)‖) :=
      mul_le_mul_of_nonneg_left (T'.le_opNorm _) (by positivity)
    _ = ‖T'‖*(r^3*‖basisValue b U (L z)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
end TamingCompatibility.JetOperator

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator GeometricAdjoint Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

include hs in

lemma ddstar_scaled_basis_jet_bound {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ Space) (L : Space ≃L[ℝ] Space) {K : Set Space}
    (hK : IsCompact K) (hKD : K ⊆ D.domain) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (a : TwoForm X), IsSmooth a → antiInvariantPart J a = a →
      ∀ (U : Set Space), IsOpen U → U ⊆ D.domain →
      ∀ (u : 𝓢(Space,C 2)), (∀ z ∈ U, rawPair J α ht p D a z = retract 2 (u z)) →
      ∀ (z : Space), z ∈ U → z ∈ K → ∀ (r M : ℝ), 0 < r → r ≤ 1 →
      (let v := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm u
       r*‖v (L z)‖ + r^2*∑ i, ‖(∂_{b i} v) (L z)‖ +
         r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} v)) (L z)‖ ≤ M) →
      r^3*‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a))
        (extChartAt Model p).symm z‖ ≤ C₀*M := by
  obtain ⟨B,hB,hbound⟩ := JetOperator.exteriorJet_bounded D.domain_open hK hKD
    (deltaComplexA J α ht p D) (deltaComplexB J α ht p D)
    (deltaComplexA_smooth J α hs ht p D) (deltaComplexB_smooth J α hs ht p D)
  let T := (JetOperator.linearTransport L (F := C 2)).comp (JetOperator.basisToCoordinate b)
  refine ⟨B*‖T‖,mul_nonneg hB (norm_nonneg _),fun a ha hanti U hU hUD u hrep z hz hzK r M hr hr1 hj => ?_⟩
  have hM : 0 ≤ M := by
    apply le_trans _ hj
    positivity
  rw [ddstar_local_jet J α hs ht p D ha hanti hU hUD u hrep hz]
  apply (JetOperator.basis_linear_output_scaled_bound
    (JetOperator.exteriorJet (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) z)
    L b u z hr hr1 hj).trans
  apply mul_le_mul_of_nonneg_right _ hM
  exact (ContinuousLinearMap.opNorm_comp_le _ T).trans
    (mul_le_mul_of_nonneg_right (hbound z hzK) (norm_nonneg T))
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftBasisBound
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set ComplexMatrix
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in

lemma closedLift_scaled_basis_local_bound_oai {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ Space) (p : A.centers) (τ : 𝓢(Space,ℝ)) (η : 𝓢(Space,ℂ))
    (L : Space ≃L[ℝ] Space) {U K : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1) (hη : ∀ z ∈ U, η z = 1)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
        (f : antiPre A J α hs ht) (z : Space), z ∈ K →
        ∀ (r M : ℝ), 0 < r → r ≤ 1 →
      (let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))
       r*‖u (L z)‖ + r^2*∑ i, ‖(∂_{b i} u) (L z)‖ +
         r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} u)) (L z)‖ ≤ M) →
      r^3*‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
        (extChartAt Model p.val).symm z -
        ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm z‖ ≤ C₀*M := by
  obtain ⟨C₀,hC,hbound⟩ := ddstar_scaled_basis_jet_bound J α hs ht p.val (D p) b L hK (hKU.trans hUD)
  refine ⟨C₀,hC,fun H Gs f z hz r M hr hr1 hj => ?_⟩
  rw [closedLiftOfInverse_pullback_sub]
  apply hbound (Gs f).val.val (Gs f).val.property (Gs f).property U hU hUD
    (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f)) _ z (hKU hz) hz r M hr hr1 hj
  intro y hy
  exact (localizedRawSchwartz_raw A J α hs ht D hD p τ η (Gs f) (hUD hy)
    (hτ y hy) (hη y hy)).symm

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound_oai.{u_1, u_2} := @OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound_oai.{u_1, u_2}
