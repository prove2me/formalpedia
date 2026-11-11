-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:13:59.138424+00:00
-- url     : https://prove2.me/submissions/afcba0bc-26d1-41ac-90e8-8ce8c6f81e92

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Star
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
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.HodgeThree
open RealInnerProductSpace FormMetric ExteriorForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Frame
variable (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)

include h0 h1 h2 h3 hF in
lemma star_injective_frame : Function.Injective (star F) := by
  intro α β h
  apply sharp_injective
  apply (tripleBasis b).repr.injective
  ext i
  have hi := congrArg (fun a : Form (E := E) 1 => a ![b i]) h
  rw [star_on_frame b J h0 h1 h2 h3 F hF,
    star_on_frame b J h0 h1 h2 h3 F hF] at hi
  have he := mul_left_cancel₀ (pow_ne_zero (i : ℕ) (by norm_num : (-1 : ℝ) ≠ 0)) (neg_injective hi)
  simpa only [tripleBasis_repr] using he
end Frame

lemma star_injective (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
    (hdim : Module.finrank ℝ E = 4) (F : Form (E := E) 2)
    (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫) : Function.Injective (star F) := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis J hJ hdim
  exact star_injective_frame b J.toContinuousLinearMap h0 h1 h2 h3 F hF

end TamingCompatibility.HodgeThree

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FormEquiv
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
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap MetricForms MetricModel ExteriorForms
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

variable (g : Metric E) (J : E →L[ℝ] E)
  (hJ : ∀ u, J (J u) = -u)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hJ horth hdim hF

lemma starThree_injective : Function.Injective (starThree g F) := by
  intro α β h
  apply (formEquiv g 3).injective
  have hp := HodgeThree.star_injective (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF
  apply hp
  exact (formEquiv g 1).symm.injective h

lemma starThree_eq_zero (α : MetricForms.Form E 3) : starThree g F α = 0 ↔ α = 0 := by
  rw [← starThree_zero g F]
  exact (starThree_injective g J hJ horth hdim F hF).eq_iff

end TamingCompatibility.MetricHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_StarTwoComp
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instNormedAddCommGroupTangentSpaceRealSpaceModel
attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instNormedSpaceRealTangentSpaceSpaceModel
attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instFiniteDimensionalRealTangentSpaceSpaceModel
lemma starThree_eq_zero (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 3) : starThree J α ht β = 0 ↔ β = 0 := by
  constructor
  · intro h
    funext x
    exact (MetricHodge.starThree_eq_zero (tangentMetric J α ht x) (J.endomorphism x) (J.square x)
      ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
      (by change Module.finrank ℝ Space = 4; simp [Space]) (invariantPart J α x)
      (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (β x)).mp (congrFun h x)
  · intro h
    subst β
    funext x
    exact MetricHodge.starThree_zero _ _

end TamingCompatibility.ManifoldHodge

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

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeClosedSmooth
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

lemma preStar_self_adjoint (a b : PreL2 A J α hs ht true) :
    ⟪preStar A J α hs ht a,b⟫ = ⟪a,preStar A J α hs ht b⟫ := by
  conv_lhs => rw [← preStar_square A J α hs ht b]
  exact (preStar A J α hs ht).inner_map_map a (preStar A J α hs ht b)

lemma hodgePreD_adjoint (a : PreL2 A J α hs ht false) (b : PreL2 A J α hs ht true) :
    ⟪hodgePreD A J α hs ht a,b⟫ = ⟪a,hodgeDelta A J α hs ht b⟫ := by
  have h := hodgeGraph_weak A J α hs ht b a
  change ⟪smoothL2 A J α hs ht true (hodgePreD A J α hs ht a),
    smoothL2 A J α hs ht true b⟫ =
      ⟪smoothL2 A J α hs ht false a,smoothL2 A J α hs ht false (hodgeDelta A J α hs ht b)⟫ at h
  simpa only [(smoothL2 A J α hs ht true).inner_map_map,
    (smoothL2 A J α hs ht false).inner_map_map] using h

lemma hodgeDelta_star_eq_zero_iff (a : PreL2 A J α hs ht true) :
    hodgeDelta A J α hs ht (preStar A J α hs ht a) = 0 ↔ IsClosed a.val := by
  change _ ↔ ManifoldForms.Closed (a.val : Form X 2)
  rw [closed_iff_exteriorDerivative_eq_zero (α := (a.val : Form X 2)) a.property]
  change (⟨codifferential J α ht (starTwo J α ht a.val),_⟩ : PreL2 A J α hs ht false) = 0 ↔ _
  rw [Subtype.ext_iff]
  change -starThree J α ht (exteriorDerivative (starTwo J α ht (starTwo J α ht a.val))) = 0 ↔ _
  rw [starTwo_square,neg_eq_zero,starThree_eq_zero]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma hodgePreD_closed (a : PreL2 A J α hs ht false) :
    IsClosed (hodgePreD A J α hs ht a).val := a.property.closed_exteriorDerivative

lemma hodgeCoexactPart_pair (a b : PreL2 A J α hs ht true) :
    ⟪hodgeCoexactPart A J α hs ht a,b⟫ =
      ⟪hodgeDelta A J α hs ht (preStar A J α hs ht a),
        hodgeDelta A J α hs ht (preStar A J α hs ht b)⟫ := by
  rw [hodgeCoexactPart,preStar_self_adjoint,hodgePreD_adjoint]

lemma hodgeCoexactPart_closed_pair (a b : PreL2 A J α hs ht true)
    (hb : IsClosed b.val) : ⟪hodgeCoexactPart A J α hs ht a,b⟫ = 0 := by
  rw [hodgeCoexactPart_pair,(hodgeDelta_star_eq_zero_iff A J α hs ht b).mpr hb,inner_zero_right]

lemma hodgeLaplacian_closed (a : PreL2 A J α hs ht true) (ha : IsClosed a.val) :
    hodgeLaplacian A J α hs ht a = hodgePreD A J α hs ht (hodgeDelta A J α hs ht a) := by
  rw [hodgeLaplacian_apply,(hodgeDelta_star_eq_zero_iff A J α hs ht a).mpr ha,map_zero,map_zero,add_zero]

lemma hodgeSmoothShift_closed_iff (r : ℝ) (a : PreL2 A J α hs ht true) :
    IsClosed (hodgeSmoothShift A J α hs ht r a).val ↔ IsClosed a.val := by
  constructor
  · intro ha
    let v := hodgeCoexactPart A J α hs ht a
    have h := hodgeCoexactPart_closed_pair A J α hs ht a
      (hodgeSmoothShift A J α hs ht r a) ha
    rw [hodgeSmoothShift_apply,inner_add_right,real_inner_smul_right,hodgeLaplacian_apply,
      inner_add_right,hodgeCoexactPart_closed_pair A J α hs ht a
        (hodgePreD A J α hs ht (hodgeDelta A J α hs ht a))
        (hodgePreD_closed A J α hs ht _),zero_add] at h
    change ⟪v,a⟫ + r^2*⟪v,v⟫ = 0 at h
    have hp : 0 ≤ r^2*⟪v,v⟫ := mul_nonneg (sq_nonneg _) real_inner_self_nonneg
    have he : ⟪hodgeDelta A J α hs ht (preStar A J α hs ht a),
        hodgeDelta A J α hs ht (preStar A J α hs ht a)⟫ = 0 := by
      rw [← hodgeCoexactPart_pair]
      exact le_antisymm (by linarith) (by rw [hodgeCoexactPart_pair]; exact real_inner_self_nonneg)
    exact (hodgeDelta_star_eq_zero_iff A J α hs ht a).mp (inner_self_eq_zero.mp he)
  · intro ha
    rw [hodgeSmoothShift_apply,hodgeLaplacian_closed A J α hs ht a ha]
    exact IsClosed.add ha ((hodgePreD_closed A J α hs ht _).smul _)
      a.property ((hodgePreD A J α hs ht (hodgeDelta A J α hs ht a)).property.smul _)
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeClosedResolvent
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

omit [T2Space X] in
lemma hodgeSmoothShift_power_closed_iff (r : ℝ) (j : ℕ) (a : PreL2 A J α hs ht true) :
    IsClosed ((hodgeSmoothShift A J α hs ht r ^ j) a).val ↔ IsClosed a.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ']
    change IsClosed (hodgeSmoothShift A J α hs ht r ((hodgeSmoothShift A J α hs ht r ^ j) a)).val ↔ _
    rw [hodgeSmoothShift_closed_iff,ih]

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma hodgeIsExact_closed (a : PreL2 A J α hs ht true) (ha : hodgeIsExact A J α hs ht a) :
    IsClosed a.val := by
  obtain ⟨ξ,rfl⟩ := ha
  exact hodgePreD_closed A J α hs ht ξ

omit [T2Space X] in
lemma hodgeSmoothShift_exact_iff (r : ℝ) (a : PreL2 A J α hs ht true) :
    hodgeIsExact A J α hs ht (hodgeSmoothShift A J α hs ht r a) ↔ hodgeIsExact A J α hs ht a := by
  constructor
  · intro ha
    have hc := (hodgeSmoothShift_closed_iff A J α hs ht r a).mp
      (hodgeIsExact_closed A J α hs ht _ ha)
    obtain ⟨ξ,hξ⟩ := ha
    refine ⟨ξ-r^2 • hodgeDelta A J α hs ht a,?_⟩
    rw [map_sub,map_smul,← hξ,hodgeSmoothShift_apply,hodgeLaplacian_closed A J α hs ht a hc]
    simp only [add_sub_cancel_right]
  · intro ha
    have hc := hodgeIsExact_closed A J α hs ht a ha
    obtain ⟨ξ,hξ⟩ := ha
    refine ⟨ξ+r^2 • hodgeDelta A J α hs ht a,?_⟩
    rw [map_add,map_smul,← hξ,hodgeSmoothShift_apply,hodgeLaplacian_closed A J α hs ht a hc]

omit [T2Space X] in
lemma hodgeSmoothShift_power_exact_iff (r : ℝ) (j : ℕ) (a : PreL2 A J α hs ht true) :
    hodgeIsExact A J α hs ht ((hodgeSmoothShift A J α hs ht r ^ j) a) ↔ hodgeIsExact A J α hs ht a := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ']
    change hodgeIsExact A J α hs ht (hodgeSmoothShift A J α hs ht r
      ((hodgeSmoothShift A J α hs ht r ^ j) a)) ↔ _
    rw [hodgeSmoothShift_exact_iff,ih]

include D hD in

theorem hodgeRegularization_smooth_closed_exact (r : ℝ) (hr : 0 < r)
    (f : PreL2 A J α hs ht true) :
    ∃ b : PreL2 A J α hs ht true,
      smoothL2 A J α hs ht true b = hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true f) ∧
      (IsClosed b.val ↔ IsClosed f.val) ∧
      (hodgeIsExact A J α hs ht b ↔ hodgeIsExact A J α hs ht f) := by
  obtain ⟨b,hb⟩ := hodgeRegularization_smooth A J α hs ht D hD r hr f
  have hi := hodgeRegularization_smooth_inverse A J α hs ht r hr f b hb
  refine ⟨b,hb,?_,?_⟩
  · rw [← hi,hodgeSmoothShift_power_closed_iff]
  · rw [← hi,hodgeSmoothShift_power_exact_iff]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeHarmonicRegular
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.swapMap_apply
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
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_harmonic_raw_all_orders (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (u : hodgeEnergy A J α hs ht)
    (hu : hodgeWeakDerivative A J α hs ht u = 0) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ n : ℕ, MemSobolevLoc V n (hodgeRawDistribution A J α hs ht D hD p τ u) := by
  obtain ⟨φ,hφ,hφU,W,hW,hqW,hWU,hφone⟩ := SchwartzCutoff.exists_one_near hU hq
  have hφD := hφU.trans hUD
  let a := patchA J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let b := patchB J α hs ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset) (φ.smooth ⊤) hφ hφD
  have ha : ∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p).toData i z := by
    intro z hz i
    simp only [a,patchA,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hb : ∀ z ∈ W, b z = normalB J α ht p.val (D p).toData z := by
    intro z hz
    simp only [b,patchB,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hρ : ∀ z ∈ W, ρ z = chartDensity J α p.val z := by
    intro z hz
    simp only [ρ,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  let ζ : 𝓢(Space,ℂ) := 0
  let G := fun i j z => ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p.val (D p).toData i j z
  have hG : ∀ i j, G i j q = chartDensity J α p.val q * ∑ t, (D p).frame t q i * (D p).frame t q j := by
    intro i j
    simp only [G,hρ q hqW,hφone q hqW,one_mul,GeometricChart.normalMetric,
      LocalMatrixOperator.frameCovector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,mul_comm]
  obtain ⟨V,hV,hqV,hVW,hall⟩ := full_shifted_square_uniform_regular hW q hqW
    (coordinateMetric J α ht p.val q) (fun i => (D p).frame i q)
    ((D p).frame_gram q (hUD hq)) a b ρ ζ G
    (patchA_polarized J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD ρ)
    (chartDensity J α p.val q) (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq))) hG
  refine ⟨V,hV,hqV,hVW.trans hWU,fun n => ?_⟩
  apply (hall n _
    (memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ u) W) ?_).mono
    (by simp)
  intro χ hc hχW
  have hz : smulLeftCLM (C 6) χ (fullShiftedSquare a b ρ ζ
      (hodgeRawDistribution A J α hs ht D hD p τ u)) = 0 := by
    rw [← map_zero (smulLeftCLM (C 6) χ)]
    apply localize_eq_of_real_tests _ χ hc hχW
    intro ψ hψ hψW
    ext j
    change (ComplexMatrix.square EuclideanEnergy.e a b ρ
      (hodgeRawDistribution A J α hs ht D hD p τ u)
      (SchwartzMap.postcompCLM Complex.ofRealCLM ψ)) j +
      (smulLeftCLM (C 6) 0 (hodgeRawDistribution A J α hs ht D hD p τ u)
        (SchwartzMap.postcompCLM Complex.ofRealCLM ψ)) j = 0
    rw [hodge_raw_square_energy A J α hs ht D hD p τ hW (hWU.trans hUD)
      (fun z hz => hτ z (hWU hz)) a b ρ ha hb hρ ψ hψ hψW j u,hu,inner_zero_left]
    have ht0 : SchwartzMap.smulLeftCLM ℂ (0 : 𝓢(Space,ℂ))
        (SchwartzMap.postcompCLM Complex.ofRealCLM ψ) = 0 := by
      ext z
      rw [SchwartzMap.smulLeftCLM_apply (0 : 𝓢(Space,ℂ)).hasTemperateGrowth]
      exact zero_smul _ _
    simp only [Complex.ofReal_zero,zero_add,TemperedDistribution.smulLeftCLM_apply_apply]
    change ((hodgeRawDistribution A J α hs ht D hD p τ u)
      (SchwartzMap.smulLeftCLM ℂ (0 : 𝓢(Space,ℂ))
        (SchwartzMap.postcompCLM Complex.ofRealCLM ψ))) j = 0
    rw [ht0,map_zero]
    rfl
  rw [hz]
  simpa only [map_zero] using (0 : 𝓢(Space,C 6)).memSobolev (s := (n:ℝ)) (p := 2)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set HilbertSobolev ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_harmonic_local_smooth (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (u : hodgeEnergy A J α hs ht)
    (hu : hodgeWeakDerivative A J α hs ht u = 0) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧ ∃ g : Space →ᵇ C 6,
      ContDiff ℝ ∞ (g : Space → C 6) ∧ ∀ χ : 𝓢(Space,ℂ),
        HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
        smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ u) =
          smulLeftCLM (C 6) χ (EuclideanSobolev.boundedDistribution g) := by
  obtain ⟨W,hW,hqW,hWU,hall⟩ :=
    hodge_harmonic_raw_all_orders A J α hs ht D hD p τ hU hUD hτ q hq u hu
  obtain ⟨V,hV,hqV,hVW,g,hg,he⟩ := exists_local_smooth_representative hW hqW hall
  exact ⟨V,hV,hqV,hVW.trans hWU,g,hg,he⟩
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open HilbertSobolev
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in
lemma hodge_harmonic_weak_patch (u : hodgeEnergy A J α hs ht)
    (hu : hodgeWeakDerivative A J α hs ht u = 0) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ w : PreL2 A J α hs ht true,
      ∀ (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ), tsupport ρ ⊆ V →
        ∀ a : PreL2 A J α hs ht true,
          ⟪hodgeInclusion A J α hs ht u,smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ =
          ⟪smoothL2 A J α hs ht true w,smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,-,-,U,hU,hxU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hxp hw
  obtain ⟨V,hV,hxV,hVU,g,hgs,hgd⟩ := hodge_harmonic_local_smooth A J α hs ht D hD p τ
    hU hUD hτ (extChartAt Model p.val x) hxU u hu
  obtain ⟨W,hW,hxW,hWV,w,hw⟩ := hodge_exists_patch A J α hs ht D p hV (hVU.trans hUD) hxV g hgs
  let Z := (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' W
  have hZ : IsOpen Z := (continuousOn_extChartAt p.val).isOpen_inter_preimage (isOpen_extChartAt_source p.val) hW
  refine ⟨Z,hZ,⟨hxs,hxW⟩,w,fun ρ hρ hρZ a => ?_⟩
  obtain ⟨q,hqc,hqW,hq⟩ := hodge_supported_test A J α hs ht D p hW
    (hWV.trans (hVU.trans hUD)) ρ hρ hρZ a
  rw [← hq]
  refine hodge_pair_all_tests_eq A J α hs ht D p (hWV.trans (hVU.trans hUD)) _ _ ?_ q hqc hqW
  intro φ hc hφW k
  exact hodge_local_pairing_eq A J α hs ht D hD p τ hW (hWV.trans (hVU.trans hUD))
    (fun z hz => hτ z (hVU (hWV hz))) _ g
    (fun χ hc hχ => tests_eq_of_localize hV hgd χ hc (hχ.trans hWV)) w hw φ hc hφW k
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeHarmonicSmooth
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
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in

theorem hodge_harmonic_smooth (u : hodgeEnergy A J α hs ht)
    (hu : hodgeWeakDerivative A J α hs ht u = 0) :
    ∃ b : PreL2 A J α hs ht true, hodgeSmooth A J α hs ht b = u := by
  classical
  choose V hV hxV w hw using hodge_harmonic_weak_patch A J α hs ht D hD u hu
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion_of_mem x (hxV x))
  have hc : (univ : Set X) ⊆ ⋃ p : s, V p.val := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => V p.val) (fun p => hV p.val) hc
  apply hodge_glue_weak_patches A J α hs ht (fun p : s => ρ p) (fun p => (ρ p).contMDiff)
    (fun x => ?_) _ (fun p : s => w p.val) (fun p => hw p.val (ρ p) (ρ p).contMDiff (hρ p))
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
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
lemma hodgeSmoothShift_dense (r : ℝ) (hr : 0 < r) :
    DenseRange (fun a : PreL2 A J α hs ht true =>
      smoothL2 A J α hs ht true (hodgeSmoothShift A J α hs ht r a)) := by
  apply (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr).mono
  rintro _ ⟨a,rfl⟩
  refine ⟨(hodgeSmoothShift A J α hs ht r ^ 2) a,?_⟩
  have he (K : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true) :
      (K ^ 3) a = K ((K ^ 2) a) := by rw [show 3 = 2+1 from rfl,pow_succ']; rfl
  dsimp only
  rw [he]

include D hD in
lemma hodgeResolvent_fixed_of_weak_harmonic (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true)
    (hf : ∀ a : PreL2 A J α hs ht true,
      ⟪f,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ = 0) :
    hodgeResolvent A J α hs ht r f = f := by
  apply ext_inner_right ℝ
  have hsym (u v : L2 A J α hs ht true) :
      ⟪hodgeResolvent A J α hs ht r u,v⟫ = ⟪u,hodgeResolvent A J α hs ht r v⟫ :=
    hodgeResolvent_symmetric A J α hs ht r u v
  have he : (fun y => ⟪hodgeResolvent A J α hs ht r f,y⟫) =
      (fun y : L2 A J α hs ht true => ⟪f,y⟫) :=
    (hodgeSmoothShift_dense A J α hs ht D hD r hr).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (by
      funext a
      dsimp only [Function.comp_apply]
      rw [hsym,
        hodgeResolvent_smoothShift A J α hs ht r hr,hodgeSmoothShift_apply,
        map_add,map_smul,inner_add_right,real_inner_smul_right,hf,mul_zero,add_zero])
  exact congrFun he

include D hD in
lemma hodge_weak_harmonic_graph (f : L2 A J α hs ht true)
    (hf : ∀ a : PreL2 A J α hs ht true,
      ⟪f,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ = 0) :
    ∃ u : hodgeEnergy A J α hs ht,
      hodgeInclusion A J α hs ht u = f ∧ hodgeWeakDerivative A J α hs ht u = 0 := by
  let u := hodgeWeakSolution A J α hs ht 1 zero_lt_one f
  have hfix := hodgeResolvent_fixed_of_weak_harmonic A J α hs ht D hD 1 zero_lt_one f hf
  refine ⟨u,?_,?_⟩
  · rw [hodgeResolvent_eq A J α hs ht 1 zero_lt_one] at hfix
    exact hfix
  · have h := hodgeWeakSolution_identity A J α hs ht 1 zero_lt_one f u
    rw [hfix,one_pow,one_mul,add_eq_left] at h
    exact inner_self_eq_zero.mp h

omit [T2Space X] in
lemma hodgeSmooth_closed_of_weakDerivative_zero (b : PreL2 A J α hs ht true)
    (hb : hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht b) = 0) : IsClosed b.val := by
  apply (hodgeDelta_star_eq_zero_iff A J α hs ht b).mp
  apply (smoothL2 A J α hs ht false).injective
  have h := congrArg (fun z : HodgeDerivativePair A J α hs ht => z.snd) hb
  exact h

include D hD in

theorem hodge_weak_harmonic_smooth (f : L2 A J α hs ht true)
    (hf : ∀ a : PreL2 A J α hs ht true,
      ⟪f,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ = 0) :
    ∃ b : PreL2 A J α hs ht true, smoothL2 A J α hs ht true b = f ∧ IsClosed b.val := by
  obtain ⟨u,hu,hDu⟩ := hodge_weak_harmonic_graph A J α hs ht D hD f hf
  obtain ⟨b,hb⟩ := hodge_harmonic_smooth A J α hs ht D hD u hDu
  refine ⟨b,?_,?_⟩
  · rw [← hodgeInclusion_smooth,hb,hu]
  · apply hodgeSmooth_closed_of_weakDerivative_zero A J α hs ht b
    rw [hb,hDu]
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

omit [T2Space X] in
lemma hodgeWeakClosedL2_isClosed : _root_.IsClosed (hodgeWeakClosedL2 A J α hs ht : Set (L2 A J α hs ht true)) := by
  change _root_.IsClosed {v : L2 A J α hs ht true | ∀ ξ : PreL2 A J α hs ht false,
    ⟪v,l2Star A J α hs ht (testDerivative A J α hs ht ξ)⟫ = 0}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun _ => isClosed_eq (continuous_id.inner continuous_const) continuous_const)

omit [T2Space X] in
lemma hodgeSmooth_mem_weakClosed (a : PreL2 A J α hs ht true) (ha : IsClosed a.val) :
    smoothL2 A J α hs ht true a ∈ hodgeWeakClosedL2 A J α hs ht := by
  intro ξ
  rw [← smoothL2_preD,l2Star_smooth,(smoothL2 A J α hs ht true).inner_map_map,
    real_inner_comm,preStar_self_adjoint,hodgePreD_adjoint,
    (hodgeDelta_star_eq_zero_iff A J α hs ht a).mpr ha,inner_zero_right]

omit [T2Space X] in
lemma hodgeSmooth_mem_closedL2 (a : PreL2 A J α hs ht true) (ha : IsClosed a.val) :
    smoothL2 A J α hs ht true a ∈ hodgeClosedL2 A J α hs ht :=
  subset_closure ⟨a,ha,rfl⟩

omit [T2Space X] in
lemma hodgeClosedL2_le_weakClosed : hodgeClosedL2 A J α hs ht ≤ hodgeWeakClosedL2 A J α hs ht := by
  apply Submodule.topologicalClosure_minimal _ ?_ (hodgeWeakClosedL2_isClosed A J α hs ht)
  rintro _ ⟨a,ha,rfl⟩
  exact hodgeSmooth_mem_weakClosed A J α hs ht a ha

include D hD in
lemma hodge_closed_orthogonal_zero (v : L2 A J α hs ht true)
    (hv : v ∈ hodgeWeakClosedL2 A J α hs ht)
    (ho : v ∈ (hodgeClosedL2 A J α hs ht)ᗮ) : v = 0 := by
  have hh : ∀ a : PreL2 A J α hs ht true,
      ⟪v,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ = 0 := by
    intro a
    have he := ho (smoothL2 A J α hs ht true (hodgePreD A J α hs ht (hodgeDelta A J α hs ht a)))
      (hodgeSmooth_mem_closedL2 A J α hs ht _ (hodgePreD_closed A J α hs ht _))
    rw [real_inner_comm] at he
    rw [hodgeLaplacian_apply,map_add,inner_add_right,he,zero_add,← l2Star_smooth,smoothL2_preD]
    exact hv _
  obtain ⟨b,hb,hbc⟩ := hodge_weak_harmonic_smooth A J α hs ht D hD v hh
  have h := ho (smoothL2 A J α hs ht true b) (hodgeSmooth_mem_closedL2 A J α hs ht b hbc)
  rw [hb] at h
  exact inner_self_eq_zero.mp h

include D hD in

theorem hodgeClosedL2_eq_weakClosed : hodgeClosedL2 A J α hs ht = hodgeWeakClosedL2 A J α hs ht := by
  let C := hodgeClosedL2 A J α hs ht
  let W := hodgeWeakClosedL2 A J α hs ht
  have hC : _root_.IsClosed (C : Set (L2 A J α hs ht true)) :=
    Submodule.isClosed_topologicalClosure _
  let : CompleteSpace C := hC.completeSpace_coe
  have hb : Cᗮ ⊓ W = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    exact (Submodule.mem_bot ℝ).mpr (hodge_closed_orthogonal_zero A J α hs ht D hD v hv.2 hv.1)
  have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hodgeClosedL2_le_weakClosed A J α hs ht)
  change C ⊔ Cᗮ ⊓ W = W at h
  rwa [hb,sup_bot_eq] at h

include D hD in

theorem hodge_pair_weakClosed_eq_zero (U V : L2 A J α hs ht true)
    (hU : ∀ a : PreL2 A J α hs ht true, IsClosed a.val → ⟪U,smoothL2 A J α hs ht true a⟫ = 0)
    (hV : V ∈ hodgeWeakClosedL2 A J α hs ht) : ⟪U,V⟫ = 0 := by
  have ho : U ∈ (hodgeClosedL2 A J α hs ht)ᗮ := by
    rw [hodgeClosedL2,Submodule.orthogonal_closure]
    rintro _ ⟨a,ha,rfl⟩
    rw [real_inner_comm]
    exact hU a ha
  rw [← hodgeClosedL2_eq_weakClosed A J α hs ht D hD] at hV
  rw [real_inner_comm]
  exact ho V hV
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairing
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

include D hD in
lemma hodgeCubeRepresents_annihilates_closed (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (U : L2 A J α hs ht true)
    (hU : hodgeCubeRepresents A J α hs ht r F U)
    (hF : ∀ a : PreL2 A J α hs ht true, IsClosed a.val → F a = 0)
    (b : PreL2 A J α hs ht true) (hbc : IsClosed b.val) :
    ⟪U,smoothL2 A J α hs ht true b⟫ = 0 := by
  obtain ⟨a,ha,hac,_⟩ := hodgeRegularization_smooth_closed_exact A J α hs ht D hD r hr b
  have hi := hodgeRegularization_smooth_inverse A J α hs ht r hr b a ha
  rw [← hi,hU a]
  exact hF a (hac.mpr hbc)

include D hD in
lemma hodgeCubeRepresents_star_weakClosed (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (V : L2 A J α hs ht true)
    (hV : hodgeCubeRepresents A J α hs ht r F V)
    (hF : ∀ ξ : PreL2 A J α hs ht false, F (hodgePreD A J α hs ht ξ) = 0) :
    l2Star A J α hs ht V ∈ hodgeWeakClosedL2 A J α hs ht := by
  intro ξ
  rw [l2Star_inner,← smoothL2_preD]
  obtain ⟨a,ha,_,hae⟩ := hodgeRegularization_smooth_closed_exact A J α hs ht D hD r hr
    (hodgePreD A J α hs ht ξ)
  have hi := hodgeRegularization_smooth_inverse A J α hs ht r hr (hodgePreD A J α hs ht ξ) a ha
  have he : hodgeIsExact A J α hs ht a := hae.mpr ⟨ξ,rfl⟩
  obtain ⟨η,hη⟩ := he
  rw [← hi,hV a,hη]
  exact hF η

include D hD in

theorem hodge_regularized_zero_pairing (r : ℝ) (hr : 0 < r)
    (F F' : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (U V : L2 A J α hs ht true)
    (hU : hodgeCubeRepresents A J α hs ht r F U)
    (hV : hodgeCubeRepresents A J α hs ht r F' V)
    (hF : ∀ a : PreL2 A J α hs ht true, IsClosed a.val → F a = 0)
    (hF' : ∀ ξ : PreL2 A J α hs ht false, F' (hodgePreD A J α hs ht ξ) = 0) :
    ⟪U,l2Star A J α hs ht V⟫ = 0 := by
  exact hodge_pair_weakClosed_eq_zero A J α hs ht D hD U (l2Star A J α hs ht V)
    (hodgeCubeRepresents_annihilates_closed A J α hs ht D hD r hr F U hU hF)
    (hodgeCubeRepresents_star_weakClosed A J α hs ht D hD r hr F' V hV hF')

attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {r : ℝ} {hr : 0 < r}
variable (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma regularize_cubeRepresents (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    hodgeCubeRepresents A J α hs ht r (unitMeasureCurrent J g μ) (C.regularize g μ) := by
  intro a
  exact C.regularize_smoothShift_cube g μ a
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] in
lemma hodgeRegularization_l2_represents (Q : L2 A J α hs ht true) {r : ℝ} (hr : 0 < r) :
    hodgeCubeRepresents A J α hs ht r (l2CurrentSource A J α hs ht Q)
      (hodgeRegularization A J α hs ht r Q) := by
  intro a
  rw [hodgeRegularization_symmetric,hodgeRegularization_smoothShift_cube A J α hs ht r hr]
  rfl

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel

lemma positiveL2Source_represents
    (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
    (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr) :
    hodgeCubeRepresents A J α hs ht r (positiveL2Source A J α hs ht μ)
      (S.regularize (hermitianMetric J α hs ht) μ) := S.regularize_cubeRepresents _ μ
end TamingCompatibility.GeometricHilbert

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

omit [T2Space X] in
lemma hodgeCubeRepresents_add {r : ℝ}
    {F G : PreL2 A J α hs ht true →ₗ[ℝ] ℝ} {U V : L2 A J α hs ht true}
    (hU : hodgeCubeRepresents A J α hs ht r F U) (hV : hodgeCubeRepresents A J α hs ht r G V) :
    hodgeCubeRepresents A J α hs ht r (F+G) (U+V) := by
  intro a
  rw [inner_add_left,hU a,hV a]
  rfl

lemma hodge_residual_energy_zero_oai
    (μ ν : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Q : L2 A J α hs ht true) (hQ : l2Star A J α hs ht Q = Q)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (hν : ∀ ξ : PreL2 A J α hs ht false,
      (positiveL2Source A J α hs ht ν + l2CurrentSource A J α hs ht Q)
        (hodgePreD A J α hs ht ξ) = 0)
    (r : ℝ) (hr : 0 < r) :
    let P := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ r
    let P' := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) ν r
    let V := hodgeRegularization A J α hs ht r Q
    ⟪P,l2Star A J α hs ht P'⟫+⟪P,V⟫+⟪P',V⟫+‖V‖^2 = 0 := by
  dsimp only
  let S := hodgeSmoothingCover A J α hs ht D hD r hr
  let g := hermitianMetric J α hs ht
  let V := hodgeRegularization A J α hs ht r Q
  have hV : l2Star A J α hs ht V = V := by
    dsimp only [V]
    rw [← hodgeRegularization_star,hQ]
  have hrep := hodgeRegularization_l2_represents A J α hs ht Q hr
  have he := hodge_regularized_zero_pairing A J α hs ht D hD r hr
    (positiveL2Source A J α hs ht μ+l2CurrentSource A J α hs ht Q)
    (positiveL2Source A J α hs ht ν+l2CurrentSource A J α hs ht Q)
    (S.regularize g μ+V) (S.regularize g ν+V)
    (hodgeCubeRepresents_add A J α hs ht (positiveL2Source_represents A J α hs ht D hD μ r hr S) hrep)
    (hodgeCubeRepresents_add A J α hs ht (positiveL2Source_represents A J α hs ht D hD ν r hr S) hrep)
    hT hν
  have hcross : ⟪V,l2Star A J α hs ht (S.regularize g ν)⟫ = ⟪S.regularize g ν,V⟫ := by
    rw [← l2Star_self_adjoint,hV,real_inner_comm]
  rw [map_add,inner_add_left,inner_add_right,inner_add_right,hV,hcross,real_inner_self_eq_norm_sq] at he
  simp only [hodgePositiveCurrentFamily,dite_eq_left hr]
  change ⟪S.regularize g μ,l2Star A J α hs ht (S.regularize g ν)⟫+
    ⟪S.regularize g μ,V⟫+⟪S.regularize g ν,V⟫+‖V‖^2 = 0
  linarith
end TamingCompatibility.GeometricHilbert

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero_oai.{u_1}
