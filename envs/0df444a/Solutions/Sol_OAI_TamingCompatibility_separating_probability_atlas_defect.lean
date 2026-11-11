-- Prove2me | solution 1 for OAI.TamingCompatibility.separating_probability_atlas_defect
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:37:32.00624+00:00
-- url     : https://prove2.me/submissions/ee3ceb3d-3126-4e9b-bfb9-7feace8bf6c3

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc029
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_separating_probability_smooth_defect
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_geometric_smooth_inverse
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_raw_smooth_near

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_BundleTotalSpaceT2
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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
open Bundle Filter
open scoped Topology

lemma bundle_totalSpace_t2 {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [T2Space B] [T2Space F] (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle F E] : T2Space (TotalSpace F E) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro p q hpq
  by_cases hb : p.proj = q.proj
  · let e := trivializationAt F E p.proj
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hq : q ∈ e.source := e.mem_source.mpr (hb ▸ mem_baseSet_trivializationAt F E p.proj)
    have he : e p ≠ e q := fun h => hpq (e.injOn hp hq h)
    exact (e.toOpenPartialHomeomorph.continuousAt hp).disjoint
      (disjoint_nhds_nhds.mpr he) (e.toOpenPartialHomeomorph.continuousAt hq)
  · exact (FiberBundle.continuous_proj F E).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hb) (FiberBundle.continuous_proj F E).continuousAt
end TamingCompatibility

end

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

lemma coclosed_selfdual_closed (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) {β : TwoForm X} (hβ : IsSmooth β)
    (hself : starTwo J α ht β = β) (hc : codifferential J α ht β = 0) : IsClosed β := by
  change -(starThree J α ht (ManifoldForms.exteriorDerivative (starTwo J α ht β))) = 0 at hc
  rw [hself, neg_eq_zero,starThree_eq_zero J α ht] at hc
  exact (ManifoldForms.closed_iff_exteriorDerivative_eq_zero hβ).mpr hc

lemma coclosed_antiInvariant_closed (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) {β : TwoForm X} (hβ : IsSmooth β)
    (hanti : antiInvariantPart J β = β) (hc : codifferential J α ht β = 0) : IsClosed β := by
  apply coclosed_selfdual_closed J α ht hβ _ hc
  rw [← hanti]
  exact starTwo_antiInvariant J α ht β

end TamingCompatibility.ManifoldHodge

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RawNormal
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartReconstruction
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma manifoldTest_eq {b : TwoForm X} (hb : antiInvariantPart J b = b)
    (q : Space → EuclideanEnergy.Pair) (hqD : tsupport q ⊆ D.domain)
    (hraw : ∀ z ∈ D.domain, q z = rawPair J α ht p D b z)
    (hbzero : ∀ x ∉ (extChartAt Model p).symm '' D.domain, b x = 0) :
    manifoldTest J α ht p D q = b := by
  funext x
  by_cases hx : x ∈ (extChartAt Model p).symm '' D.domain
  · obtain ⟨z,hz,rfl⟩ := hx
    apply form_eq_of_chart_pullback p _ _ ((extChartAt Model p).map_target (D.domain_subset hz))
    rw [(extChartAt Model p).right_inv (D.domain_subset hz)]
    change TamingCompatibility.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z =
      TamingCompatibility.pullback b (extChartAt Model p).symm z
    rw [pullback_manifoldTest J α ht p D hqD (D.domain_subset hz)]
    have he : TamingCompatibility.pullback b (extChartAt Model p).symm z =
        coordinateTest J α ht p D (rawPair J α ht p D b) z :=
      rawScalar_expansion J α ht p D hb hz
    rw [he]
    simp only [coordinateTest,LocalMatrixOperator.frameTest,hraw z hz]
  · rw [hbzero x hx,manifoldTest_zero_off J α ht p D q]
    exact fun h => hx ((image_mono hqD) h)
end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiEnergyWeak
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma antiGraph_weak (a : antiPre A J α hs ht) (b : PreL2 A J α hs ht false) :
    inner ℝ (testDerivative A J α hs ht b) (antiGraph A J α hs ht a).fst =
      inner ℝ (smoothL2 A J α hs ht false b) (antiGraph A J α hs ht a).snd := by
  let db : PreL2 A J α hs ht true := ⟨exteriorDerivative b.val,b.property.exteriorDerivative⟩
  have h := GeometricAdjoint.formal_adjoint A J α hs ht b.property a.val.property
  have he : l2Pairing A J α ht db a.val = l2Pairing A J α ht b (antiDelta A J α hs ht a) := h
  exact ((smoothL2 A J α hs ht true).inner_map_map db a.val).trans
    ((preL2_inner A J α hs ht true db a.val).trans (he.trans
      (((smoothL2 A J α hs ht false).inner_map_map b (antiDelta A J α hs ht a)).trans
        (preL2_inner A J α hs ht false b (antiDelta A J α hs ht a))).symm))

lemma antiEnergy_weak (u : antiEnergy A J α hs ht) (b : PreL2 A J α hs ht false) :
    inner ℝ (testDerivative A J α hs ht b) u.val.fst =
      inner ℝ (smoothL2 A J α hs ht false b) u.val.snd := by
  let S : Set (WithLp 2 (L2 A J α hs ht true × L2 A J α hs ht false)) :=
    {v | inner ℝ (testDerivative A J α hs ht b) v.fst =
      inner ℝ (smoothL2 A J α hs ht false b) v.snd}
  have hc : _root_.IsClosed S := isClosed_eq
    (continuous_const.inner (WithLp.fstL 2 ℝ _ _).continuous)
    (continuous_const.inner (WithLp.sndL 2 ℝ _ _).continuous)
  have hr : (LinearMap.range (antiGraph A J α hs ht) : Set _) ⊆ S := by
    rintro _ ⟨a,rfl⟩
    exact antiGraph_weak A J α hs ht a b
  exact (closure_minimal hr hc) u.property

lemma antiEnergy_fst_injective : Function.Injective
    (fun u : antiEnergy A J α hs ht => u.val.fst) := by
  suffices hz : ∀ u : antiEnergy A J α hs ht, u.val.fst = 0 → u = 0 by
    intro u v huv
    have he : u-v=0 := hz (u-v) (by change u.val.fst - v.val.fst = 0; exact sub_eq_zero.mpr huv)
    exact sub_eq_zero.mp he
  intro u hu
  have htest (b : PreL2 A J α hs ht false) :
      inner ℝ (smoothL2 A J α hs ht false b) u.val.snd = 0 := by
    rw [← antiEnergy_weak A J α hs ht u b,hu,inner_zero_right]
  have hall : ∀ v : L2 A J α hs ht false, inner ℝ v u.val.snd = 0 := by
    intro v
    exact (smoothL2_dense A J α hs ht false).induction_on v
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) htest
  have hz : u.val.snd = 0 := inner_self_eq_zero.mp (hall u.val.snd)
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℝ (L2 A J α hs ht true × L2 A J α hs ht false)).injective
  exact Prod.ext hu hz
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricCompact
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma energyInclusion_injective : Function.Injective (energyInclusion A J α hs ht) :=
  antiEnergy_fst_injective A J α hs ht

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.componentTest_apply _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

lemma rawPair_manifoldTest {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ D.domain) :
    rawPair J α ht p D (manifoldTest J α ht p D q) z = q z := by
  have he : TamingCompatibility.pullback (manifoldTest J α ht p D q)
      (extChartAt Model p).symm z = coordinateTest J α ht p D q z :=
    pullback_manifoldTest J α ht p D hqD (D.domain_subset hz)
  unfold rawPair rawScalar
  rw [he]
  ext i
  fin_cases i <;>
    simp [EuclideanEnergy.pair,coordinateTest,frameTest,realPart_apply,imagPart_apply,
      D.frame_gram z hz]

end TamingCompatibility.GeometricChart

end
end

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_WeakNormal
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_WeightedRawPairing
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma densityTest_apply (p : A.centers) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain) (z : Space) :
    densityTest A J α hs ht D p φ hc hφD z = φ z * (2*chartDensity J α p.val z) := rfl

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma densityTest_support (p : A.centers) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain) :
    tsupport (densityTest A J α hs ht D p φ hc hφD) ⊆ tsupport φ :=
  tsupport_smul_subset_left _ _

lemma smooth_raw_component_pair (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) (w : antiPre A J α hs ht) :
    (rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht w)
      (SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD)))) j =
    (⟪energyInclusion A J α hs ht (antiToEnergy A J α hs ht w),energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  rw [rawDistribution_smooth,embedded_component_apply]
  change _ = (⟪smoothL2 A J α hs ht true w.val,energyInclusion A J α hs ht
    (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
      (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ)
  rw [smooth_energy_pair]
  congr 1
  change _ = ∫ x, GeometricAdjoint.pairing J α ht w.val.val
    (manifoldTest J α ht p.val (D p) (componentTest j φ)) x ∂geometricVolume A J α
  rw [pairing_manifoldTest_integral J α ht p.val (D p) A hs w.val.property w.property
    ((componentTest j φ).smooth ⊤) (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [componentTest_inner,densityTest_apply]
  by_cases hz : z ∈ tsupport φ
  · rw [cutoff_realPair_raw A J α ht D hD p w.val τ (hUD (hφU hz)) (hτ z (hφU hz))]
    fin_cases j <;> simp [rawPair,EuclideanEnergy.pair,componentTest_apply] <;> ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp [componentTest_apply,image_eq_zero_of_notMem_tsupport hz]

lemma raw_component_pair (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) (u : antiEnergy A J α hs ht) :
    (rawDistribution A J α hs ht D hD p τ u
      (SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD)))) j =
    (⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM (densityTest A J α hs ht D p φ hc (hφU.trans hUD))
  let v := testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))
  have hLc : Continuous (fun w => (rawDistribution A J α hs ht D hD p τ w ψ) j) := by
    generalize rawDistribution A J α hs ht D hD p τ = L
    exact (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp
      ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) (C 2) ψ).continuous.comp L.continuous)
  have hRc : Continuous (fun w => (⟪energyInclusion A J α hs ht w,
      energyInclusion A J α hs ht (antiToEnergy A J α hs ht v)⟫ : ℂ)) :=
    Complex.continuous_ofReal.comp ((energyInclusion A J α hs ht).continuous.inner continuous_const)
  exact (antiToEnergy_dense A J α hs ht).induction_on u (isClosed_eq hLc hRc)
    (fun w => smooth_raw_component_pair A J α hs ht D hD p τ hUD hτ φ hc hφU j w)

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalSmoothPairing
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma local_pairing_eq (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (u : antiEnergy A J α hs ht) (g : Space →ᵇ C 2)
    (hg : ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ U →
      rawDistribution A J α hs ht D hD p τ u χ = EuclideanSobolev.boundedDistribution g χ)
    (w : antiPre A J α hs ht) (hw : ∀ z ∈ U,
      rawPair J α ht p.val (D p) w.val.val z = retract 2 (g z))
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) :
    ⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ =
    ⟪smoothL2 A J α hs ht true w.val,energyInclusion A J α hs ht
      (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
        (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ := by
  let θ := densityTest A J α hs ht D p φ hc (hφU.trans hUD)
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM θ
  have hθ : tsupport θ ⊆ tsupport φ := densityTest_support A J α hs ht D p φ hc (hφU.trans hUD)
  have hψ : tsupport ψ ⊆ tsupport θ := tsupport_comp_subset (map_zero Complex.ofRealCLM) θ
  have he := hg ψ (hc.of_isClosed_subset (isClosed_tsupport ψ) (hψ.trans hθ))
    (hψ.trans (hθ.trans hφU))
  have hp := raw_component_pair A J α hs ht D hD p τ hUD hτ φ hc hφU j u
  change (rawDistribution A J α hs ht D hD p τ u ψ) j = _ at hp
  rw [he] at hp
  have hr := congrArg Complex.re hp
  rw [bounded_real_component,Complex.ofReal_re] at hr
  rw [← hr,smooth_energy_pair]
  change _ = ∫ x, GeometricAdjoint.pairing J α ht w.val.val
    (manifoldTest J α ht p.val (D p) (componentTest j φ)) x ∂geometricVolume A J α
  rw [pairing_manifoldTest_integral J α ht p.val (D p) A hs w.val.property w.property
    ((componentTest j φ).smooth ⊤) (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  change (φ z * (2*chartDensity J α p.val z)) * (g z j).re = _
  by_cases hz : z ∈ tsupport φ
  · have hzraw := congrArg (fun v : EuclideanEnergy.Pair => v j) (hw z (hφU hz))
    rw [← retract_apply 2 (g z) j,← hzraw]
    fin_cases j <;> simp [rawPair,EuclideanEnergy.pair,componentTest_apply] <;> ring
  · simp [image_eq_zero_of_notMem_tsupport hz,componentTest_apply]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiSmoothMultiply
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma rawPair_fun_smul (ρ : X → ℝ) (a : TwoForm X) (z : Space) :
    rawPair J α ht p D (fun x => ρ x • a x) z =
      ρ ((extChartAt Model p).symm z) • rawPair J α ht p D a z := by
  ext j
  fin_cases j <;> rfl
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)

lemma supported_anti_test (p : A.centers) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (hρU : ∀ x ∈ tsupport ρ, x ∈ (extChartAt Model p.val).source ∧ extChartAt Model p.val x ∈ U)
    (a : antiPre A J α hs ht) :
    ∃ q : 𝓢(Space,EuclideanEnergy.Pair), ∃ hc : HasCompactSupport (q : Space → EuclideanEnergy.Pair),
      ∃ hqU : tsupport q ⊆ U,
        testAnti A J α hs ht D p q hc (hqU.trans hUD) = antiMultiply A J α hs ht ρ hρ a := by
  let K := (extChartAt Model p.val) '' tsupport ρ
  have hK : IsCompact K := (isClosed_tsupport ρ).isCompact.image_of_continuousOn
    ((continuousOn_extChartAt p.val).mono (fun x hx => (hρU x hx).1))
  have hKU : K ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact (hρU x hx).2
  obtain ⟨η,hηc,hηU,hηone⟩ := SchwartzCutoff.exists_one_on_compact hK hU hKU
  let b := antiMultiply A J α hs ht ρ hρ a
  let q := SchwartzCutoff.schwartz (D p).domain_open (rawPair_smooth J α ht p.val (D p) b.val.property)
    (η.smooth ⊤) hηc (hηU.trans hUD)
  have hqc : HasCompactSupport (q : Space → EuclideanEnergy.Pair) := SchwartzCutoff.compact hηc
  have hqU : tsupport q ⊆ U := (tsupport_smul_subset_left _ _).trans hηU
  refine ⟨q,hqc,hqU,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change manifoldTest J α ht p.val (D p) q = b.val.val
  apply manifoldTest_eq J α ht p.val (D p) b.property q (hqU.trans hUD)
  · intro z hz
    change η z • rawPair J α ht p.val (D p) (fun x => ρ x • a.val.val x) z =
      rawPair J α ht p.val (D p) (fun x => ρ x • a.val.val x) z
    rw [rawPair_fun_smul]
    by_cases hr : ρ ((extChartAt Model p.val).symm z) = 0
    · change ρ ((chartAt Space p.val).symm z) = 0 at hr
      simp [hr]
    · rw [hηone z ⟨(extChartAt Model p.val).symm z,subset_closure hr,
        (extChartAt Model p.val).right_inv ((D p).domain_subset hz)⟩,one_smul]
  · intro x hx
    change ρ x • a.val.val x = 0
    have hz : ρ x = 0 := by
      by_contra hn
      have hh := hρU x (subset_closure hn)
      exact hx ⟨extChartAt Model p.val x,hUD hh.2,(extChartAt Model p.val).left_inv hh.1⟩
    rw [hz,zero_smul]

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TestLinear
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

namespace TamingCompatibility.ComplexMatrix
open Set
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma pair_decompose (q : 𝓢(E,R 2)) :
    (q : E → R 2) = componentTest (0 : Fin 2) (realComponent q 0) + componentTest (1 : Fin 2) (realComponent q 1) := by
  ext x j
  fin_cases j <;> simp [componentTest_apply,EuclideanSpace.single]
end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)

lemma pair_all_tests_eq (p : A.centers) {U : Set Space} (hUD : U ⊆ (D p).domain)
    (u v : L2 A J α hs ht true)
    (h : ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
      (hφU : tsupport φ ⊆ U) (j : Fin 2),
      ⟪u,smoothL2 A J α hs ht true
        (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
          ((componentTest_support j φ).trans (hφU.trans hUD))).val⟫ =
      ⟪v,smoothL2 A J α hs ht true
        (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
          ((componentTest_support j φ).trans (hφU.trans hUD))).val⟫)
    (q : 𝓢(Space,EuclideanEnergy.Pair)) (hc : HasCompactSupport (q : Space → EuclideanEnergy.Pair))
    (hqU : tsupport q ⊆ U) :
    ⟪u,smoothL2 A J α hs ht true (testAnti A J α hs ht D p q hc (hqU.trans hUD)).val⟫ =
    ⟪v,smoothL2 A J α hs ht true (testAnti A J α hs ht D p q hc (hqU.trans hUD)).val⟫ := by
  let φ (j : Fin 2) := realComponent q j
  have hφc (j : Fin 2) : HasCompactSupport (φ j : Space → ℝ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (realComponent_support q j)
  have hφU (j : Fin 2) : tsupport (φ j) ⊆ U := (realComponent_support q j).trans hqU
  let w (j : Fin 2) := testAnti A J α hs ht D p (componentTest j (φ j))
    (componentTest_compact j (φ j) (hφc j)) ((componentTest_support j (φ j)).trans ((hφU j).trans hUD))
  have he : testAnti A J α hs ht D p q hc (hqU.trans hUD) = w 0 + w 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p) q =
      manifoldTest J α ht p.val (D p) (componentTest 0 (φ 0)) +
      manifoldTest J α ht p.val (D p) (componentTest 1 (φ 1))
    rw [← manifoldTest_add]
    exact congrArg (manifoldTest J α ht p.val (D p)) (pair_decompose q)
  rw [he]
  change ⟪u,smoothL2 A J α hs ht true ((w 0).val + (w 1).val)⟫ =
    ⟪v,smoothL2 A J α hs ht true ((w 0).val + (w 1).val)⟫
  rw [map_add,inner_add_right,inner_add_right]
  exact congrArg₂ (·+·) (h (φ 0) (hφc 0) (hφU 0) 0) (h (φ 1) (hφc 1) (hφU 1) 1)

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_LocalPatchConstruction
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_patch (p : A.centers) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    {z : Space} (hz : z ∈ U) (g : Space →ᵇ C 2) (hg : ContDiff ℝ ∞ (g : Space → C 2)) :
    ∃ W : Set Space, IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧ ∃ w : antiPre A J α hs ht,
      ∀ y ∈ W, rawPair J α ht p.val (D p) w.val.val y = retract 2 (g y) := by
  obtain ⟨η,hc,hηU,W,hW,hzW,hWU,hη⟩ := SchwartzCutoff.exists_one_near hU hz
  let q : Space → EuclideanEnergy.Pair := fun y => η y • retract 2 (g y)
  have hq : ContDiff ℝ ∞ q := (η.smooth ⊤).smul ((retract 2).contDiff.comp hg)
  have hqs : tsupport q ⊆ tsupport η := tsupport_smul_subset_left _ _
  have hqc : HasCompactSupport q := hc.of_isClosed_subset (isClosed_tsupport q) hqs
  let ψ := hqc.toSchwartzMap hq
  let w := testAnti A J α hs ht D p ψ hqc (hqs.trans (hηU.trans hUD))
  refine ⟨W,hW,hzW,hWU,w,fun y hy => ?_⟩
  change rawPair J α ht p.val (D p) (manifoldTest J α ht p.val (D p) q) y = _
  rw [rawPair_manifoldTest J α ht p.val (D p) (hqs.trans (hηU.trans hUD)) (hUD (hWU hy))]
  change η y • retract 2 (g y) = _
  rw [hη y hy,one_smul]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalWeakPatch
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma exists_weak_patch (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ w : antiPre A J α hs ht,
      ∀ (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ), tsupport ρ ⊆ V →
        ∀ a : antiPre A J α hs ht,
          ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ =
          ⟪smoothL2 A J α hs ht true w.val,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht D hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,U,hU,hxU,hUD,hτ,g,hgs,hgd⟩ := raw_smooth_near A J α hs ht D hD p
    (extChartAt Model p.val x) hxp hw f u heq
  obtain ⟨W,hW,hxW,hWU,w,hw⟩ := exists_patch A J α hs ht D p hU hUD hxU g hgs
  let V := (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' W
  have hV : IsOpen V := (continuousOn_extChartAt p.val).isOpen_inter_preimage (isOpen_extChartAt_source p.val) hW
  refine ⟨V,hV,⟨hxs,hxW⟩,w,fun ρ hρ hρV a => ?_⟩
  obtain ⟨q,hqc,hqW,hq⟩ := supported_anti_test A J α hs ht D p hW (hWU.trans hUD) ρ hρ hρV a
  rw [← hq]
  refine pair_all_tests_eq A J α hs ht D p (hWU.trans hUD) _ _ ?_ q hqc hqW
  intro φ hc hφW j
  exact local_pairing_eq A J α hs ht D hD p τ (hWU.trans hUD)
    (fun z hz => hτ z (hWU hz)) u g (fun χ hc hχ => hgd χ hc (hχ.trans hWU))
    w hw φ hc hφW j

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TwoDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma two_direction_inner_sq_le (z u v : E) (huv : ⟪u,v⟫ = 0) (hv : ‖v‖ = ‖u‖) :
    ⟪z,u⟫^2 + ⟪z,v⟫^2 ≤ ‖z‖^2*‖u‖^2 := by
  by_cases hu : u = 0
  · have hv0 : v = 0 := norm_eq_zero.mp (by simpa [hu] using hv)
    simp [hu,hv0]
  have hu2 : 0 < ‖u‖^2 := pow_pos (norm_pos_iff.mpr hu) 2
  have hvu : ⟪v,u⟫ = 0 := by rw [real_inner_comm,huv]
  have hzu : ⟪u,z⟫ = ⟪z,u⟫ := real_inner_comm _ _
  have hzv : ⟪v,z⟫ = ⟪z,v⟫ := real_inner_comm _ _
  have h : 0 ≤ ⟪‖u‖^2 • z - ⟪z,u⟫ • u - ⟪z,v⟫ • v,
    ‖u‖^2 • z - ⟪z,u⟫ • u - ⟪z,v⟫ • v⟫ := real_inner_self_nonneg
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    huv,hvu,hzu,hzv] at h
  simp only [real_inner_self_eq_norm_sq,hv] at h
  nlinarith
end TamingCompatibility.RadialPotential

end

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

lemma mem_nullspace_iff (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) :
    f ∈ Fredholm.nullspace (resolvent i D hc) ↔ ∃ u : V, i u = f ∧ D u = 0 := by
  rw [Fredholm.mem_nullspace]
  constructor
  · intro hf
    refine ⟨weakSolution i D hc f, hf, ?_⟩
    have he := weakSolution_identity i D hc f (weakSolution i D hc f)
    change i (weakSolution i D hc f) = f at hf
    rw [hf] at he
    have hz : ⟪D (weakSolution i D hc f), D (weakSolution i D hc f)⟫ = 0 := by linarith
    exact inner_self_eq_zero.mp hz
  · rintro ⟨u, rfl, hu⟩
    have he : weakSolution i D hc (i u) = u := by
      apply hc.continuousLinearEquivOfBilin.injective
      apply ext_inner_right ℝ
      intro v
      rw [hc.continuousLinearEquivOfBilin_apply,
        hc.continuousLinearEquivOfBilin_apply, energy_apply, energy_apply,
        weakSolution_identity, hu, inner_zero_left, add_zero]
    change i (weakSolution i D hc (i u)) = i u
    rw [he]

end TamingCompatibility.Variational

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFredholm
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma mem_harmonicAnti (f : L2 A J α hs ht true) :
    f ∈ harmonicAnti A J α hs ht ↔ ∃ u : antiEnergy A J α hs ht,
      energyInclusion A J α hs ht u = f ∧ weakDelta A J α hs ht u = 0 :=
  Variational.mem_nullspace_iff (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht) f

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothPatchGlue
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma smooth_multiply_pair (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a b : antiPre A J α hs ht) :
    ⟪smoothL2 A J α hs ht true b.val,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ =
    ⟪smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ b).val,smoothL2 A J α hs ht true a.val⟫ := by
  rw [(smoothL2 A J α hs ht true).inner_map_map,(smoothL2 A J α hs ht true).inner_map_map,
    preL2_inner,preL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (MetricForms.pairing_smul_right _ _ _ _).trans (MetricForms.pairing_smul_left _ _ _ _).symm

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma anti_partition_sum {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (a : antiPre A J α hs ht) : ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) a = a := by
  have he := map_sum (((smoothForms X 2).subtype).comp (antiPre A J α hs ht).subtype)
    (fun i => antiMultiply A J α hs ht (ρ i) (hρ i) a) Finset.univ
  apply Subtype.ext
  apply Subtype.ext
  refine he.trans ?_
  funext x
  rw [Finset.sum_apply]
  change (∑ i, ρ i x • a.val.val x) = a.val.val x
  rw [← Finset.sum_smul,h1,one_smul]

lemma energy_eq_of_pair_smooth (u v : antiEnergy A J α hs ht)
    (h : ∀ a : antiPre A J α hs ht,
      ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true a.val⟫ =
      ⟪energyInclusion A J α hs ht v,smoothL2 A J α hs ht true a.val⟫) : u = v := by
  have he : (fun z : antiEnergy A J α hs ht =>
      ⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht z⟫) =
      (fun z : antiEnergy A J α hs ht =>
      ⟪energyInclusion A J α hs ht v,energyInclusion A J α hs ht z⟫) :=
    (antiToEnergy_dense A J α hs ht).equalizer
      (continuous_const.inner (energyInclusion A J α hs ht).continuous)
      (continuous_const.inner (energyInclusion A J α hs ht).continuous) (funext h)
  apply energyInclusion_injective A J α hs ht
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hh := congrFun he (u-v)
  rw [map_sub] at hh
  rw [inner_sub_left,hh,sub_self]

lemma glue_weak_patches {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (u : antiEnergy A J α hs ht) (w : ι → antiPre A J α hs ht)
    (hw : ∀ i a, ⟪energyInclusion A J α hs ht u,
        smoothL2 A J α hs ht true (antiMultiply A J α hs ht (ρ i) (hρ i) a).val⟫ =
      ⟪smoothL2 A J α hs ht true (w i).val,
        smoothL2 A J α hs ht true (antiMultiply A J α hs ht (ρ i) (hρ i) a).val⟫) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  classical
  let b := ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) (w i)
  refine ⟨b,(energy_eq_of_pair_smooth A J α hs ht u (antiToEnergy A J α hs ht b) ?_).symm⟩
  intro a
  have ha := congrArg (fun c : antiPre A J α hs ht => smoothL2 A J α hs ht true c.val)
    (anti_partition_sum A J α hs ht ρ hρ h1 a)
  have hsum (t : ι → antiPre A J α hs ht) :
      smoothL2 A J α hs ht true (∑ i, t i).val = ∑ i, smoothL2 A J α hs ht true (t i).val := by
    exact map_sum ((smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype) t Finset.univ
  rw [hsum] at ha
  change ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true a.val⟫ =
    ⟪smoothL2 A J α hs ht true b.val,smoothL2 A J α hs ht true a.val⟫
  rw [← ha,inner_sum]
  conv_rhs => rw [show b = ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) (w i) from rfl,hsum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [hw,smooth_multiply_pair,ha]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_GlobalSmoothRegularity
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

theorem weak_solution_smooth (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  classical
  choose V hV hxV w hw using exists_weak_patch A J α hs ht D hD f u heq
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion_of_mem x (hxV x))
  have hc : (univ : Set X) ⊆ ⋃ p : s, V p.val := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => V p.val) (fun p => hV p.val) hc
  apply glue_weak_patches A J α hs ht (fun p : s => ρ p) (fun p => (ρ p).contMDiff)
    (fun x => ?_) u (fun p : s => w p.val) (fun p => hw p.val (ρ p) (ρ p).contMDiff (hρ p))
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)

include hD in
lemma weak_kernel_smooth (u : antiEnergy A J α hs ht) (hu : weakDelta A J α hs ht u = 0) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  apply weak_solution_smooth A J α hs ht D hD 0 u
  intro v
  rw [hu,inner_zero_left]
  change 0 = ⟪smoothL2 A J α hs ht true 0,energyInclusion A J α hs ht v⟫
  rw [map_zero,inner_zero_left]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothGeometricInverse
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma harmonicAnti_smooth (f : L2 A J α hs ht true) (hf : f ∈ harmonicAnti A J α hs ht) :
    ∃ b : antiPre A J α hs ht, smoothL2 A J α hs ht true b.val = f ∧
      codifferential J α ht b.val.val = 0 := by
  obtain ⟨u,hu,hd⟩ := (mem_harmonicAnti A J α hs ht f).mp hf
  obtain ⟨b,hb⟩ := weak_kernel_smooth A J α hs ht D hD u hd
  refine ⟨b,?_,?_⟩
  · rw [← hb] at hu
    exact hu
  · rw [← hb] at hd
    change smoothL2 A J α hs ht false (antiDelta A J α hs ht b) = 0 at hd
    have he := (smoothL2 A J α hs ht false).injective (hd.trans (map_zero _).symm)
    exact congrArg Subtype.val he

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_GeometricSeparatingProbability
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

local instance unitT2 [T2Space X] (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : T2Space (MetricUnit g) := by
  let : T2Space (TangentBundle Model X) := bundle_totalSpace_t2 (TangentSpace Model : X → Type)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_DualEnergyInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma energy_inverse_dual_bound (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (K : Submodule ℝ H) [CompleteSpace K] (G : H →L[ℝ] V)
    (hgraph : ∀ u, ‖u‖^2 = ‖i u‖^2 + ‖D u‖^2)
    (hweak : ∀ f v, ⟪D (G f),D v⟫ = ⟪f-K.starProjection f,i v⟫)
    (horth : ∀ f, i (G f) ∈ Kᗮ) (f : H) (M : ℝ) (hM : 0 ≤ M)
    (hdual : ∀ v, |⟪f,i v⟫| ≤ M * ‖v‖) :
    ‖G f‖ ≤ (1 + (‖D‖ * ‖G‖)^2) * M := by
  let u := G f
  let q := ‖D‖ * ‖G‖
  have hq : 0 ≤ q := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hproj (a : H) : ⟪K.starProjection a,i u⟫ = 0 :=
    K.inner_right_of_mem_orthogonal (K.starProjection_apply_mem a) (horth f)
  have hw := hweak (i u) u
  rw [inner_sub_left,hproj,sub_zero,real_inner_self_eq_norm_sq] at hw
  have hDG : ‖D (G (i u))‖ ≤ q * ‖i u‖ := calc
    ‖D (G (i u))‖ ≤ ‖D‖ * ‖G (i u)‖ := D.le_opNorm _
    _ ≤ ‖D‖ * (‖G‖ * ‖i u‖) := mul_le_mul_of_nonneg_left (G.le_opNorm _) (norm_nonneg _)
    _ = _ := by dsimp only [q] <;> ring
  have hsq : ‖i u‖^2 ≤ q * ‖i u‖ * ‖D u‖ := calc
    ‖i u‖^2 = ⟪D (G (i u)),D u⟫ := hw.symm
    _ ≤ ‖D (G (i u))‖ * ‖D u‖ := real_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hDG (norm_nonneg _)
  have hi : ‖i u‖ ≤ q * ‖D u‖ := by
    by_cases hz : ‖i u‖ = 0
    · rw [hz]; positivity
    · have hp : 0 < ‖i u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  have heg : ‖u‖^2 ≤ (1+q^2) * ‖D u‖^2 := by
    rw [hgraph]
    have h := sq_le_sq₀ (norm_nonneg (i u)) (mul_nonneg hq (norm_nonneg (D u)))
    have hh := h.mpr hi
    nlinarith
  have heq := hweak f u
  change ⟪D u,D u⟫ = _ at heq
  rw [inner_sub_left,hproj,sub_zero,real_inner_self_eq_norm_sq] at heq
  have hd : ‖D u‖^2 ≤ M * ‖u‖ := by
    rw [heq]
    exact (le_abs_self _).trans (hdual u)
  have hc : 0 ≤ 1+q^2 := by positivity
  have hb := heg.trans (mul_le_mul_of_nonneg_left hd hc)
  change ‖u‖ ≤ (1+q^2)*M
  by_cases hz : ‖u‖ = 0
  · rw [hz]; exact mul_nonneg hc hM
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith
end TamingCompatibility.Variational

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_ScaledDual
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume ComplexMatrix
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

theorem geometric_smooth_dual_inverse :
    ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
      (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
        ⟪f-(harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
      (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
      (∀ f : antiPre A J α hs ht, ∃ a : antiPre A J α hs ht,
        antiToEnergy A J α hs ht a = G (smoothL2 A J α hs ht true f.val)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f M, 0 ≤ M →
        (∀ v : antiEnergy A J α hs ht,
          |⟪f,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) → ‖G f‖ ≤ C*M := by
  obtain ⟨-,G,hweak,horth,-,hsm⟩ := geometric_smooth_inverse A J α hs ht D hD
  refine ⟨G,hweak,horth,hsm,1+(‖weakDelta A J α hs ht‖*‖G‖)^2,by positivity,?_⟩
  intro f M hM hb
  apply Variational.energy_inverse_dual_bound (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (harmonicAnti A J α hs ht) G _ hweak horth f M hM hb
  intro u
  exact WithLp.prod_norm_sq_eq_of_L2 u.val
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma exists_smooth_inverse_dual_data :
    ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
      ∃ H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht,
        (∀ f, smoothL2 A J α hs ht true (H f).val =
          (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val)) ∧
        (∀ f, IsClosed (H f).val.val) ∧
        (∀ f, antiToEnergy A J α hs ht (Gs f) = G (smoothL2 A J α hs ht true f.val)) ∧
        (∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
            weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
          (∀ v : antiEnergy A J α hs ht,
            |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
          ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C*M := by
  classical
  let i : antiPre A J α hs ht →ₗ[ℝ] L2 A J α hs ht true :=
    (smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype
  have hi : Function.Injective i := (smoothL2 A J α hs ht true).injective.comp Subtype.val_injective
  let j := (harmonicAnti A J α hs ht).starProjection.toLinearMap.comp i
  have hH : ∀ f, ∃ h : antiPre A J α hs ht, i h = j f := by
    intro f
    obtain ⟨h,hh,-⟩ := harmonicAnti_smooth A J α hs ht D hD (j f)
      ((harmonicAnti A J α hs ht).starProjection_apply_mem (i f))
    exact ⟨h,hh⟩
  let H := InjectiveLinearLift.lift i hi j hH
  have hHspec (f) : i (H f) = j f := InjectiveLinearLift.lift_spec i hi j hH f
  have hHclosed (f) : IsClosed (H f).val.val := by
    obtain ⟨h,hh,hc⟩ := harmonicAnti_smooth A J α hs ht D hD (j f)
      ((harmonicAnti A J α hs ht).starProjection_apply_mem (i f))
    have he : H f = h := hi ((hHspec f).trans hh.symm)
    rw [he]
    exact coclosed_antiInvariant_closed J α ht h.val.property h.property hc
  obtain ⟨G,hG,-,hGs,C,hC,hdual⟩ := geometric_smooth_dual_inverse A J α hs ht D hD
  have hanti : Function.Injective (antiToEnergy A J α hs ht) := by
    intro a b hab
    apply hi
    exact congrArg (energyInclusion A J α hs ht) hab
  let Gs := InjectiveLinearLift.lift (antiToEnergy A J α hs ht) hanti (G.toLinearMap.comp i) hGs
  have hGspec (f) : antiToEnergy A J α hs ht (Gs f) = G (i f) :=
    InjectiveLinearLift.lift_spec (antiToEnergy A J α hs ht) hanti (G.toLinearMap.comp i) hGs f
  refine ⟨G,H,Gs,hHspec,hHclosed,hGspec,?_,C,hC,?_⟩
  · intro f v
    rw [hGspec,hG]
    change ⟪i f - j f,energyInclusion A J α hs ht v⟫ =
      ⟪i (f-H f),energyInclusion A J α hs ht v⟫
    rw [map_sub,hHspec]
  · intro f M hM hb
    rw [hGspec]
    exact hdual (i f) M hM hb

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_HermitianRadialProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hermitianGraph_complex_pair (K : E →L[ℝ] E) (hK : ∀ v, K (K v) = -v) (v : E) :
    ⟪hermitianGraph K v, hermitianGraph K (K v)⟫ = 0 ∧
      ‖hermitianGraph K (K v)‖ = ‖hermitianGraph K v‖ := by
  constructor
  · rw [hermitianGraph_inner,hK,inner_neg_right,real_inner_comm]
    ring
  · have he : ‖hermitianGraph K (K v)‖^2 = ‖hermitianGraph K v‖^2 := by
      rw [hermitianGraph_norm_sq,hermitianGraph_norm_sq,hK,norm_neg]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hermitianDefect_nonneg (K : E →L[ℝ] E)
    (hK : ∀ v, K (K v) = -v) (z v : E) : 0 ≤ hermitianDefect K z v := by
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK v
  have h := two_direction_inner_sq_le (hermitianGraph K z)
    (hermitianGraph K v) (hermitianGraph K (K v)) ho hn
  dsimp only [hermitianDefect]
  linarith

end TamingCompatibility.RadialPotential

end
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

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialUnitCoordinates
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

omit [CompactSpace X] [T2Space X] in
lemma unitRadialDefect_continuousOn (p : X) (b : Space) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitRadialDefect J α hs ht p b) (unitChartDomain J α hs ht p K) := by
  let G := hermitianGraph (coordinateJ J p b)
  have hz := G.continuous.comp_continuousOn ((unitChartBase_continuousOn J α hs ht p hKT).sub (continuousOn_const (c := b)))
  have hv := G.continuous.comp_continuousOn (unitChartVector_continuousOn J α hs ht p hKT)
  have hjv := G.continuous.comp_continuousOn ((coordinateJ J p b).continuous.comp_continuousOn
    (unitChartVector_continuousOn J α hs ht p hKT))
  exact ((hz.norm.pow 2).mul (hv.norm.pow 2) |>.sub ((hz.inner hv).pow 2)).sub ((hz.inner hjv).pow 2)

omit [CompactSpace X] [T2Space X] in
lemma unitRadialRadius_continuousOn (p : X) (b : Space) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitRadialRadius J α hs ht p b) (unitChartDomain J α hs ht p K) :=
  ((hermitianGraph (coordinateJ J p b)).continuous.comp_continuousOn
    ((unitChartBase_continuousOn J α hs ht p hKT).sub (continuousOn_const (c := b)))).norm

omit [CompactSpace X] [T2Space X] in
lemma unitRadialDefect_nonneg (p : X) {b : Space} (hb : b ∈ (extChartAt Model p).target)
    (u : MetricUnit (hermitianMetric J α hs ht)) : 0 ≤ unitRadialDefect J α hs ht p b u :=
  hermitianDefect_nonneg _ (coordinateJ_square J p hb) _ _

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FourthMomentKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Bundle Set TopologicalSpace
lemma bundle_totalSpace_secondCountable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [SecondCountableTopology B] [SecondCountableTopology F] (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] :
    SecondCountableTopology (TotalSpace F E) := by
  let e : B → Trivialization F (π F E) := fun b => trivializationAt F E b
  obtain ⟨s,hsc,hs⟩ := isOpen_iUnion_countable (fun b => (e b).baseSet) (fun b => (e b).open_baseSet)
  have hcover : (⋃ b : B, (e b).baseSet) = univ := by
    apply eq_univ_iff_forall.mpr
    intro b
    exact mem_iUnion.mpr ⟨b,mem_baseSet_trivializationAt F E b⟩
  rw [hcover] at hs
  let := hsc.to_subtype
  let U : s → Set (TotalSpace F E) := fun b => (e b.val).source
  have (b : s) : SecondCountableTopology (U b) :=
    (e b.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := U) (fun b => (e b.val).open_source)
  apply eq_univ_iff_forall.mpr
  intro v
  have hv : v.proj ∈ ⋃ b ∈ s, (e b).baseSet := hs.symm ▸ mem_univ _
  obtain ⟨b,hb,hv⟩ := mem_iUnion₂.mp hv
  exact mem_iUnion.mpr ⟨⟨b,hb⟩,(e b).mem_source.mpr hv⟩
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [SecondCountableTopology X]
lemma unitSecondCountable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    SecondCountableTopology (MetricUnit g) := by
  have : SecondCountableTopology (TangentBundle Model X) :=
    bundle_totalSpace_secondCountable (TangentSpace Model : X → Type)
  exact TopologicalSpace.Subtype.secondCountableTopology {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1}
end TamingCompatibility

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefectCombination
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompactSpace X] [T2Space X] in
lemma smoothUnitDefect_nonneg (p : X) {b : Space} (hb : b ∈ (extChartAt Model p).target)
    (r s : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) :
    0 ≤ smoothUnitDefect J α hs ht p b r s u :=
  Set.indicator_nonneg (fun v _ => div_nonneg
    (mul_nonneg (by norm_num) (unitRadialDefect_nonneg J α hs ht p hb v)) (sq_nonneg _)) u

omit [MeasurableSpace X] [BorelSpace X] in
lemma smoothUnitDefect_integrable (p : X) (b : Space) (r : ℝ) {s : ℝ} (hs' : 0 < s)
    (hball : Metric.closedBall b r ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    Integrable (smoothUnitDefect J α hs ht p b r s) μ := by
  have hc := unitChartDomain_closed J α hs ht p (isCompact_closedBall b r) hball
  apply (integrable_indicator_iff hc.measurableSet).mpr
  apply ContinuousOn.integrableOn_compact hc.isCompact
  exact ((continuousOn_const.mul (unitRadialDefect_continuousOn J α hs ht p b hball)).div
    ((continuousOn_const.add ((unitRadialRadius_continuousOn J α hs ht p b hball).pow 2)).pow 2)
    (fun u _ => by positivity))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransverseIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace MeasureTheory
open scoped _root_.MeasureTheory
open Filter
open scoped Topology ENNReal

lemma integrable_nonneg_limit_of_uniform_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} {G : ℕ → Ω → ℝ} {f : Ω → ℝ}
    {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ n, _root_.MeasureTheory.Integrable (G n) μ) (hpos : ∀ n x, 0 ≤ G n x)
    (hbound : ∀ n, ∫ x, G n x ∂μ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (f x))) :
    _root_.MeasureTheory.Integrable f μ ∧ ∫ x, f x ∂μ ≤ C := by
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae _
    (fun n => (hG n).aestronglyMeasurable) (Eventually.of_forall hlim)
  have hfpos : ∀ x, 0 ≤ f x := fun x => ge_of_tendsto (hlim x) (Eventually.of_forall (fun n => hpos n x))
  have hlinear (n : ℕ) : ∫⁻ x, ‖G n x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
    rw [show (fun x => ‖G n x‖ₑ) = fun x => ENNReal.ofReal (G n x) by
      funext x; rw [Real.enorm_eq_ofReal (hpos n x)]]
    rw [← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hG n) (Eventually.of_forall (hpos n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hnorm : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
    calc
      ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, liminf (fun n => ‖G n x‖ₑ) atTop ∂μ :=
        _root_.MeasureTheory.lintegral_congr (fun x => (hlim x).enorm.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
        _root_.MeasureTheory.lintegral_liminf_le' (fun n => (hG n).aestronglyMeasurable.aemeasurable.enorm)
      _ ≤ ENNReal.ofReal C := liminf_le_of_le (by isBoundedDefault) (by
          intro b hb
          obtain ⟨n,hn⟩ := hb.exists
          exact hn.trans (hlinear n))
  have hfi : _root_.MeasureTheory.Integrable f μ := ⟨hmeas,hnorm.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hfi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [_root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hfpos)]
  simpa only [Real.enorm_eq_ofReal (hfpos _)] using hnorm

end MeasureTheory

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefectFinite
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma unitRadialDefect_zero_of_radius (p : X) (b : Space)
    {u : MetricUnit (hermitianMetric J α hs ht)} (hu : unitRadialRadius J α hs ht p b u = 0) :
    unitRadialDefect J α hs ht p b u = 0 := by
  have hz : hermitianGraph (coordinateJ J p b) (unitChartBase J α hs ht p u-b) = 0 :=
    norm_eq_zero.mp hu
  simp only [unitRadialDefect,hermitianDefect,hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
    zero_mul,inner_zero_left,sub_zero]

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma smoothUnitDefect_tendsto (p : X) (b : Space) (r : ℝ)
    (u : MetricUnit (hermitianMetric J α hs ht)) :
    Tendsto (fun s : ℝ => smoothUnitDefect J α hs ht p b r s u)
      (𝓝 0) (𝓝 (smoothUnitDefect J α hs ht p b r 0 u)) := by
  by_cases hu : u ∈ unitChartDomain J α hs ht p (Metric.closedBall b r)
  · simp only [smoothUnitDefect,Set.indicator_of_mem hu]
    by_cases hz : unitRadialRadius J α hs ht p b u = 0
    · simp only [unitRadialDefect_zero_of_radius J α hs ht p b hz,mul_zero,zero_div]
      exact tendsto_const_nhds
    · have hh := (tendsto_const_nhds (x := (2 : ℝ) * unitRadialDefect J α hs ht p b u)).div
        ((((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).pow 2).add_const ((unitRadialRadius J α hs ht p b u)^2)).pow 2)
        (by simpa only [zero_pow (by norm_num : 2 ≠ 0),zero_add] using pow_ne_zero 2 (pow_ne_zero 2 hz))
      exact hh
  · simp only [smoothUnitDefect,Set.indicator_of_notMem hu]
    exact tendsto_const_nhds

omit [MeasurableSpace X] [BorelSpace X] in

lemma singularDefect_integrable_of_bounds (p : X) (b : Space) {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hball : Metric.closedBall b r ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hbound : ∀ s ∈ Ioc (0:ℝ) r,
      ∫ u, smoothUnitDefect J α hs ht p b r s u ∂μ ≤ C) :
    Integrable (smoothUnitDefect J α hs ht p b r 0) μ ∧
      ∫ u, smoothUnitDefect J α hs ht p b r 0 u ∂μ ≤ C := by
  let seq : ℕ → ℝ := fun n => r/(n+1)
  have hseq (n : ℕ) : seq n ∈ Ioc (0:ℝ) r := by
    dsimp [seq]
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hseq0 : Tendsto seq atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [seq, Function.comp_apply,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp hh).const_mul r
  have hb : b ∈ (extChartAt Model p).target := hball (Metric.mem_closedBall_self hr.le)
  exact integrable_nonneg_limit_of_uniform_integral hC
    (fun n => smoothUnitDefect_integrable J α hs ht p b r (hseq n).1 hball μ)
    (fun n u => smoothUnitDefect_nonneg J α hs ht p hb r (seq n) u)
    (fun n => hbound (seq n) (hseq n))
    (fun u => (smoothUnitDefect_tendsto J α hs ht p b r u).comp hseq0)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianTestFactory
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume Set Filter
open scoped Manifold ContDiff Topology SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma exists_radial_test_data (p : A.centers) {z : Space} (hz : z ∈ (D p).domain)
    (hwz : coordinateWeight A p z ≠ 0) :
    ∃ τ ρ φ : 𝓢(Space,ℝ), ∃ U : Set Space, ∃ R : ℝ,
      IsOpen U ∧ z ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ y ∈ U, τ y * coordinateWeight A p y = 1) ∧
      (∀ y ∈ U, ρ y = chartDensity J α p.val y) ∧
      HasCompactSupport (φ : Space → ℝ) ∧ tsupport φ ⊆ (D p).domain ∧
      0 < R ∧ 2*R ≤ 1 ∧ Metric.closedBall z (4*R) ⊆ U ∧
      (∀ y ∈ Metric.closedBall z (4*R), φ y = 1) ∧
      ∀ b ∈ Metric.closedBall z R, Metric.closedBall b (2*R) ⊆ Metric.closedBall z (4*R) := by
  obtain ⟨τ,ρ,U,hU,hzU,hUD,hτ,hρ⟩ := exists_coordinate_observer A J α hs ht D p hz hwz
  obtain ⟨φ,hφ,hφU,V,hV,hzV,hVU,hφone⟩ := SchwartzCutoff.exists_one_near hU hzU
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV z hzV
  let R := min (r/8) (1/2:ℝ)
  have hR : 0 < R := lt_min (by positivity) (by norm_num)
  have hRr : R ≤ r/8 := min_le_left _ _
  have hR1 : R ≤ 1/2 := min_le_right _ _
  have hballV : Metric.closedBall z (4*R) ⊆ V := by
    intro y hy
    apply hrV
    rw [Metric.mem_ball]
    have hd : dist y z ≤ 4*R := Metric.mem_closedBall.mp hy
    linarith
  refine ⟨τ,ρ,φ,U,R,hU,hzU,hUD,hτ,hρ,hφ,hφU.trans hUD,hR,by linarith,
    hballV.trans hVU,fun y hy => hφone y (hballV hy),?_⟩
  intro b hb y hy
  rw [Metric.mem_closedBall] at hb hy ⊢
  have ht := dist_triangle y b z
  linarith
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialAtlasProducer
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open GeometricHilbert GeometricHilbert.Hermitian Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

theorem separating_probability_atlas_defect_oai
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (A : FiniteCharts X) (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) (x : X) (hp : A.partition p x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt Model p.val x) r ⊆ (extChartAt Model p.val).target ∧
      Integrable (smoothUnitDefect J α hs ht p.val (extChartAt Model p.val x) r 0) μ := by
  obtain ⟨G,H,Gs,hH,_hHclosed,_hGs,hweak,B,hB,hdual⟩ :=
    exists_smooth_inverse_dual_data A J α hs ht D hA
  have hx := hA p (subset_closure hp)
  have hz : extChartAt Model p.val x ∈ (D p).domain :=
    (D p).small_ball_subset (Metric.ball_subset_closedBall hx.2)
  have hxsrc := (D p).source_subset (hA p (subset_closure hp))
  have hwz : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxsrc] using hp
  obtain ⟨τ,ρ,φ,U,R,hU,_hzU,hUD,hτ,hρ,hφc,hφD,hR,hR1,hballU,hφone,hcenters⟩ :=
    exists_radial_test_data A J α hs ht D p hz hwz
  obtain ⟨C,r,hC,hr,hrR,hbound⟩ := separating_probability_smooth_defect
    J α hs ht A D hA H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    (φ.smooth ⊤) hφc hφD (Metric.closedBall (extChartAt Model p.val x) (4*R))
    (isCompact_closedBall _ _) hballU hφone R hR
    (Metric.closedBall (extChartAt Model p.val x) R) (isCompact_closedBall _ _) hcenters hR1 μ hann
  have hb : extChartAt Model p.val x ∈ Metric.closedBall (extChartAt Model p.val x) R :=
    Metric.mem_closedBall_self hR.le
  have htarget : Metric.closedBall (extChartAt Model p.val x) r ⊆ (extChartAt Model p.val).target :=
    (Metric.closedBall_subset_closedBall (hrR.trans (by linarith))).trans
      ((hcenters _ hb).trans (hballU.trans (hUD.trans (D p).domain_subset)))
  exact ⟨r,hr,htarget,(singularDefect_integrable_of_bounds J α hs ht p.val
    (extChartAt Model p.val x) hr hC htarget μ (fun s hs => hbound s hs _ hb)).1⟩
end TamingCompatibility

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.separating_probability_atlas_defect_oai.{u_1} := @OAI.TamingCompatibility.separating_probability_atlas_defect_oai.{u_1}
