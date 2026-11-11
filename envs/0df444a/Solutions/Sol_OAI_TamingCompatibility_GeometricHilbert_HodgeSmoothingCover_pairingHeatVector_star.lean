-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingHeatVector_star
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:13:56.633477+00:00
-- url     : https://prove2.me/submissions/e1c9a6ff-d83c-4208-8e33-66e19148c951

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc033

section
-- module Solutions.OAIQ239_TC.Compat
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

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

lemma resolvent_nonnegative (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) : 0 ≤ ⟪f, resolvent i D hc f⟫ := by
  change 0 ≤ ⟪f, i (weakSolution i D hc f)⟫
  rw [← weakSolution_identity i D hc f (weakSolution i D hc f)]
  exact add_nonneg (real_inner_self_nonneg) (real_inner_self_nonneg)

end TamingCompatibility.Variational

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

lemma hodgeResolvent_nonnegative (r : ℝ) (f : L2 A J α hs ht true) :
    0 ≤ ⟪f,hodgeResolvent A J α hs ht r f⟫ := by
  unfold hodgeResolvent
  split_ifs with hr
  · exact Variational.resolvent_nonnegative _ _ _ f
  · exact real_inner_self_nonneg

end TamingCompatibility.GeometricHilbert

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalEvaluation
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

lemma hodgeAmbientStar_square (v : HodgeGraphSpace A J α hs ht) :
    hodgeAmbientStar A J α hs ht (hodgeAmbientStar A J α hs ht v) = v := by
  apply (WithLp.linearEquiv 2 ℝ _).injective
  apply Prod.ext
  · exact l2Star_square A J α hs ht v.fst
  · rfl

lemma hodgeDomainStar_square (u : hodgeEnergy A J α hs ht) :
    hodgeDomainStar A J α hs ht (hodgeDomainStar A J α hs ht u) = u :=
  Subtype.ext (hodgeAmbientStar_square A J α hs ht u.val)

lemma hodgeInclusion_star (u : hodgeEnergy A J α hs ht) :
    hodgeInclusion A J α hs ht (hodgeDomainStar A J α hs ht u) =
      l2Star A J α hs ht (hodgeInclusion A J α hs ht u) := rfl

lemma hodgeDerivative_star_inner (u v : hodgeEnergy A J α hs ht) :
    ⟪hodgeWeakDerivative A J α hs ht (hodgeDomainStar A J α hs ht u),
      hodgeWeakDerivative A J α hs ht (hodgeDomainStar A J α hs ht v)⟫ =
      ⟪hodgeWeakDerivative A J α hs ht u,hodgeWeakDerivative A J α hs ht v⟫ := by
  change ⟪u.val.snd.snd,v.val.snd.snd⟫ + ⟪u.val.snd.fst,v.val.snd.fst⟫ =
    ⟪u.val.snd.fst,v.val.snd.fst⟫ + ⟪u.val.snd.snd,v.val.snd.snd⟫
  exact add_comm _ _

lemma hodgeDerivative_star_adjoint (u v : hodgeEnergy A J α hs ht) :
    ⟪hodgeWeakDerivative A J α hs ht (hodgeDomainStar A J α hs ht u),
      hodgeWeakDerivative A J α hs ht v⟫ =
      ⟪hodgeWeakDerivative A J α hs ht u,
        hodgeWeakDerivative A J α hs ht (hodgeDomainStar A J α hs ht v)⟫ := by
  conv_lhs => rw [← hodgeDomainStar_square A J α hs ht v]
  exact hodgeDerivative_star_inner A J α hs ht u (hodgeDomainStar A J α hs ht v)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolventStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeWeakSolution_star (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht r hr (l2Star A J α hs ht f) =
      hodgeDomainStar A J α hs ht (hodgeWeakSolution A J α hs ht r hr f) := by
  apply hodgeWeakSolution_unique A J α hs ht r hr
  intro v
  rw [hodgeInclusion_star,l2Star_self_adjoint,hodgeDerivative_star_adjoint]
  have h := hodgeWeakSolution_identity A J α hs ht r hr f (hodgeDomainStar A J α hs ht v)
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply] at h
  simpa only [hodgeInclusion_star,l2Star_self_adjoint] using h

lemma hodgeResolvent_star (r : ℝ) (f : L2 A J α hs ht true) :
    hodgeResolvent A J α hs ht r (l2Star A J α hs ht f) =
      l2Star A J α hs ht (hodgeResolvent A J α hs ht r f) := by
  by_cases hr : 0 < r
  · rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,hodgeWeakSolution_star,hodgeInclusion_star]
  · simp only [hodgeResolvent,dite_eq_right hr,one_apply_eq_self]

lemma hodgeRegularization_star (r : ℝ) (f : L2 A J α hs ht true) :
    hodgeRegularization A J α hs ht r (l2Star A J α hs ht f) =
      l2Star A J α hs ht (hodgeRegularization A J α hs ht r f) := by
  change hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r (l2Star A J α hs ht f))) =
      l2Star A J α hs ht (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
        (hodgeResolvent A J α hs ht r f)))
  rw [hodgeResolvent_star,hodgeResolvent_star,hodgeResolvent_star]
end TamingCompatibility.GeometricHilbert

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolventParameters
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

lemma hodgeWeakSolution_parameter (r s : ℝ) (hr : 0 < r) (hs' : 0 < s)
    (f : L2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht r hr
      (r^2 • f + (s^2-r^2) • hodgeResolvent A J α hs ht s f) =
      s^2 • hodgeWeakSolution A J α hs ht s hs' f := by
  apply hodgeWeakSolution_unique A J α hs ht r hr
  intro v
  rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_left,
    inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h := hodgeWeakSolution_identity A J α hs ht s hs' f v
  rw [hodgeResolvent_eq A J α hs ht s hs', ContinuousLinearMap.comp_apply] at h ⊢
  nlinarith only [h]

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

lemma hodgeResolvent_eigenvalue_positive_le_one (f : L2 A J α hs ht true)
    (hf : f ≠ 0) (x : ℝ) (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    0 < x ∧ x ≤ 1 := by
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hp := hodgeResolvent_nonnegative A J α hs ht 1 f
  rw [hx, real_inner_smul_right, real_inner_self_eq_norm_sq] at hp
  have hx0 : 0 ≤ x := (mul_nonneg_iff_of_pos_right (sq_pos_of_pos hn)).mp hp
  have hb := hodgeResolvent_norm_le A J α hs ht 1 f
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0] at hb
  have hx1 : x ≤ 1 := by nlinarith
  have hne : x ≠ 0 := by
    intro hz
    have hz' : hodgeResolvent A J α hs ht 1 f = hodgeResolvent A J α hs ht 1 0 := by
      rw [hx, hz, zero_smul, map_zero]
    exact hf (hodgeResolvent_injective A J α hs ht 1 zero_lt_one hz')
  exact ⟨lt_of_le_of_ne hx0 (Ne.symm hne), hx1⟩

lemma hodgeResolvent_eigenvector_parameter (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeResolvent A J α hs ht r f = (x / (r^2+(1-r^2)*x)) • f := by
  have hdpos : 0 < r^2 + (1-r^2)*x := by
    have hr2 := sq_pos_of_pos hr
    have hp := mul_nonneg hr2.le (sub_nonneg.mpr hx1)
    by_cases hz : x = 0
    · simpa only [hz, mul_zero, add_zero] using hr2
    · have hxp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hz)
      nlinarith
  have hd := ne_of_gt hdpos
  have h := congrArg (hodgeInclusion A J α hs ht)
    (hodgeWeakSolution_parameter A J α hs ht r 1 hr zero_lt_one f)
  rw [map_smul] at h
  simp only [← ContinuousLinearMap.comp_apply, ← hodgeResolvent_eq A J α hs ht _] at h
  simp only [one_pow, one_smul, hx] at h
  rw [smul_smul, ← add_smul, map_smul] at h
  calc
    hodgeResolvent A J α hs ht r f =
        (r^2+(1-r^2)*x)⁻¹ • ((r^2+(1-r^2)*x) • hodgeResolvent A J α hs ht r f) := by
      rw [inv_smul_smul₀ hd]
    _ = (r^2+(1-r^2)*x)⁻¹ • (x • f) := by rw [h]
    _ = (x / (r^2+(1-r^2)*x)) • f := by
      rw [smul_smul]; congr 1; ring

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeSpectralHeat
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
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeSpectralHeat_eigenvector (t x : ℝ) (f : L2 A J α hs ht true)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeSpectralHeat A J α hs ht D hD t f = hodgeHeatMultiplier t x • f := by
  classical
  let v : Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x :=
    ⟨f, Module.End.mem_eigenspace_iff.mpr hx⟩
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  have hv : E.symm (lp.single 2 x v) = f :=
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv_symm_apply_single v
  have hv' : E f = lp.single 2 x v := by rw [← hv, E.apply_symm_apply]
  apply E.injective
  apply lp.ext
  funext y
  change E (hodgeSpectralHeat A J α hs ht D hD t f) y = E (hodgeHeatMultiplier t x • f) y
  rw [hodgeSpectralHeat_repr, map_smul]
  change hodgeHeatMultiplier t y • E f y = hodgeHeatMultiplier t x • E f y
  rw [hv']
  by_cases hy : y = x
  · subst y; rfl
  · simp [lp.single_apply, hy]

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatSmoothing
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeBoundedSpectralMultiplier_repr (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (f : L2 A J α hs ht true) (x : ℝ) :
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f) x =
      m x • (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f x := by
  change ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
    ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv.symm _)) x = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma hodgeBoundedSpectralMultiplier_eigenvector (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (x : ℝ) (f : L2 A J α hs ht true)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f = m x • f := by
  classical
  let v : Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x :=
    ⟨f, Module.End.mem_eigenspace_iff.mpr hx⟩
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  have hv : E.symm (lp.single 2 x v) = f :=
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv_symm_apply_single v
  have hv' : E f = lp.single 2 x v := by rw [← hv, E.apply_symm_apply]
  apply E.injective
  apply lp.ext
  funext y
  change E (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f) y = E (m x • f) y
  rw [hodgeBoundedSpectralMultiplier_repr, map_smul]
  change m y • E f y = m x • E f y
  rw [hv']
  by_cases hy : y = x
  · subst y; rfl
  · simp [lp.single_apply, hy]

lemma hodgeSpectralHeat_factor (r : ℝ) (hr : 0 < r) :
    hodgeSpectralHeat A J α hs ht D hD (r^2) =
      hodgeRegularization A J α hs ht r * hodgeHeatBoost A J α hs ht D hD r := by
  let L := hodgeSpectralHeat A J α hs ht D hD (r^2) -
    hodgeRegularization A J α hs ht r * hodgeHeatBoost A J α hs ht D hD r
  have hi : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x) ≤ L.ker := by
    apply iSup_le
    intro x f hf
    have hx := Module.End.mem_eigenspace_iff.mp hf
    change L f = 0
    by_cases hzero : f = 0
    · subst f; exact map_zero L
    obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht f hzero x hx
    have hxinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx1
    have hrate : hodgeSpectralRate x = x⁻¹-1 := max_eq_right (sub_nonneg.mpr hxinv)
    have hden : 0 < 1+r^2*hodgeSpectralRate x := by
      have hp := mul_nonneg (sq_nonneg r) (le_max_left 0 (x⁻¹-1))
      dsimp [hodgeSpectralRate] <;> linarith
    have hdpos : 0 < r^2+(1-r^2)*x := by
      have hp := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hx1)
      nlinarith
    have heq : x/(r^2+(1-r^2)*x) = (1+r^2*hodgeSpectralRate x)⁻¹ := by
      rw [hrate] at hden ⊢
      field_simp [ne_of_gt hx0, ne_of_gt hden, ne_of_gt hdpos]
      ring
    have he := hodgeResolvent_eigenvector_parameter A J α hs ht r hr f x hx0.le hx1 hx
    rw [heq] at he
    have hp (n : ℕ) : (hodgeResolvent A J α hs ht r ^ n) f =
        ((1+r^2*hodgeSpectralRate x)⁻¹)^n • f := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, map_smul, he, smul_smul]
        congr 1
    have hb := hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD
      (fun x => (1+r^2*hodgeSpectralRate x)^3 * Real.exp (-(r^2*hodgeSpectralRate x)))
      (6*Real.exp 1) (by positivity)
      (fun x => heat_boost_bound _ (mul_nonneg (sq_nonneg _) (le_max_left _ _))) x f hx
    change hodgeHeatBoost A J α hs ht D hD r f = _ at hb
    dsimp [L]
    rw [sub_apply, mul_apply_eq_comp,
      hodgeSpectralHeat_eigenvector A J α hs ht D hD _ x f hx, hb, map_smul]
    change hodgeHeatMultiplier (r^2) x • f - _ • (hodgeResolvent A J α hs ht r ^ 3) f = 0
    rw [hp 3, smul_smul]
    have hc : ((1+r^2*hodgeSpectralRate x)^3 * Real.exp (-(r^2*hodgeSpectralRate x))) *
        ((1+r^2*hodgeSpectralRate x)⁻¹)^3 = hodgeHeatMultiplier (r^2) x := by
      simp only [hodgeHeatMultiplier, max_eq_left (sq_nonneg r), neg_mul]
      field_simp [ne_of_gt hden]
    rw [hc, sub_self]
  have hcl : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,
      hodgeResolvent_eigenspaces_total A J α hs ht D hD]
    simp
  have htop : ⊤ ≤ L.ker := by
    rw [← hcl]
    exact Submodule.topologicalClosure_minimal _ hi (ContinuousLinearMap.isClosed_ker L)
  ext f
  have hf : L f = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp hf

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatIdentification
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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include D hD in
lemma hodgeSpectral_ext (T U : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true)
    (he : ∀ (x : ℝ) (f : L2 A J α hs ht true),
      hodgeResolvent A J α hs ht 1 f = x • f → T f = U f) : T = U := by
  let L := T-U
  have hi : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x) ≤ L.ker := by
    apply iSup_le
    intro x f hf
    change T f-U f = 0
    exact sub_eq_zero.mpr (he x f (Module.End.mem_eigenspace_iff.mp hf))
  have hcl : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,
      hodgeResolvent_eigenspaces_total A J α hs ht D hD]
    simp
  have htop : ⊤ ≤ L.ker := by
    rw [← hcl]
    exact Submodule.topologicalClosure_minimal _ hi (ContinuousLinearMap.isClosed_ker L)
  ext f
  have hf : T f-U f = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp hf

lemma hodgeBoundedSpectralMultiplier_commutes (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true)
    (hT : ∀ f, hodgeResolvent A J α hs ht 1 (T f) = T (hodgeResolvent A J α hs ht 1 f)) :
    hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm * T =
      T * hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm := by
  apply hodgeSpectral_ext A J α hs ht D hD
  intro x f hx
  have hTx : hodgeResolvent A J α hs ht 1 (T f) = x • T f := by rw [hT, hx, map_smul]
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD m K hK hm x (T f) hTx,
    hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD m K hK hm x f hx,
    map_smul]

lemma hodgeSpectralHeat_star (t : ℝ) (f : L2 A J α hs ht true) :
    hodgeSpectralHeat A J α hs ht D hD t (l2Star A J α hs ht f) =
      l2Star A J α hs ht (hodgeSpectralHeat A J α hs ht D hD t f) := by
  have he := hodgeBoundedSpectralMultiplier_commutes A J α hs ht D hD
    (hodgeHeatMultiplier t) 1 zero_le_one
    (fun x => (abs_of_pos (hodgeHeatMultiplier_pos t x)).trans_le (hodgeHeatMultiplier_le_one t x))
    (l2Star A J α hs ht) (hodgeResolvent_star A J α hs ht 1)
  exact congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f) he

attribute [local instance] unitMeasurable unitBorel
end TamingCompatibility.GeometricHilbert
end

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairingStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingEvaluation_star (b : PreL2 A J α hs ht true) (x : X) :
    C.pairingEvaluation (preStar A J α hs ht b) x =
      (C.pairingEvaluation b x).comp (l2Star A J α hs ht) := by
  have he : (fun f => C.pairingEvaluation (preStar A J α hs ht b) x f) =
      (fun f => C.pairingEvaluation b x (l2Star A J α hs ht f)) :=
    (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr).equalizer
      (C.pairingEvaluation (preStar A J α hs ht b) x).continuous
      ((C.pairingEvaluation b x).continuous.comp (l2Star A J α hs ht).continuous) (by
        funext a
        dsimp only [Function.comp_apply]
        have h := hodgeRegularization_smoothShift_cube A J α hs ht r hr a
        have hstar : hodgeRegularization A J α hs ht r
            (l2Star A J α hs ht (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a))) =
            smoothL2 A J α hs ht true (preStar A J α hs ht a) := by
          rw [hodgeRegularization_star,h,l2Star_smooth]
        rw [C.pairingEvaluation_smooth _ _ _ a h,
          C.pairingEvaluation_smooth _ _ _ (preStar A J α hs ht a) hstar]
        exact hodgeStar_pairing J α ht b.val a.val x)
  ext f
  exact congrFun he f

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgePairingHeatStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}

omit [T2Space X] in
lemma hodgeHeatBoost_star {r : ℝ} (hr : 0 < r) (f : L2 A J α hs ht true) :
    hodgeHeatBoost A J α hs ht D hD r (l2Star A J α hs ht f) =
      l2Star A J α hs ht (hodgeHeatBoost A J α hs ht D hD r f) := by
  apply hodgeRegularization_injective A J α hs ht r hr
  have he (v : L2 A J α hs ht true) :
      hodgeRegularization A J α hs ht r (hodgeHeatBoost A J α hs ht D hD r v) =
        hodgeSpectralHeat A J α hs ht D hD (r^2) v :=
    (congrArg (fun L : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => L v)
      (hodgeSpectralHeat_factor A J α hs ht D hD r hr)).symm
  rw [he,hodgeRegularization_star,he,hodgeSpectralHeat_star]

namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingHeatEvaluation_star (b : PreL2 A J α hs ht true) (x : X) :
    C.pairingHeatEvaluation (preStar A J α hs ht b) x =
      (C.pairingHeatEvaluation b x).comp (l2Star A J α hs ht) := by
  ext f
  change C.pairingEvaluation (preStar A J α hs ht b) x (hodgeHeatBoost A J α hs ht D hD r f) =
    C.pairingEvaluation b x (hodgeHeatBoost A J α hs ht D hD r (l2Star A J α hs ht f))
  rw [C.pairingEvaluation_star,ContinuousLinearMap.comp_apply,hodgeHeatBoost_star hr]

lemma pairingHeatVector_star_oai (b : PreL2 A J α hs ht true) (x : X) :
    C.pairingHeatVector (preStar A J α hs ht b) x =
      l2Star A J α hs ht (C.pairingHeatVector b x) := by
  apply ext_inner_right ℝ
  intro f
  rw [l2Star_self_adjoint]
  simp only [pairingHeatVector,ContinuousLinearMap.adjoint_inner_left,Real.inner_apply,one_mul]
  exact congrArg (fun L : L2 A J α hs ht true →L[ℝ] ℝ => L f) (C.pairingHeatEvaluation_star b x)

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingHeatVector_star_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingHeatVector_star_oai.{u_1}
