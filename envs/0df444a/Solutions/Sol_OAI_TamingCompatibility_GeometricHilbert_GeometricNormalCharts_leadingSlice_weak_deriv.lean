-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:22:18.40379+00:00
-- url     : https://prove2.me/submissions/a735599b-b8bc-4362-bb96-4681127da1c1

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc023
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_ParametrixData_cutoff_form_weak_deriv
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_centeredDisplacement_hasFDerivAt
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_leadingSlice_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_residualSlice_pairing_integral

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricTensor
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma coordinateJet_contDiff (G : MetricDerivative (V := V)) :
    ContDiff ℝ ∞ (coordinateJet G) := by
  exact contDiff_id.sub (((christoffel G).contDiff.comp contDiff_id).clm_apply
    contDiff_id |>.const_smul (1/2 : ℝ))

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricDerivativeSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricDerivativeSpace
lemma normalMetric_eq_pullback (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    normalMetric g B (p,z) =
      (g (p+B p (coordinateJet (metricJet g B p) z))).bilinearComp
        (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z)
        (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z) := by
  rw [(centeredDisplacement_hasFDerivAt g B hg hB hsym p z).fderiv]
  ext v w
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_NormalDensityJacobian
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_1
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_1
lemma normal_density_jacobian (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    volumeDensity (normalMetric g B (p,z)) =
      |LinearMap.det (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z).toLinearMap| *
      volumeDensity (g (p+B p (coordinateJet (metricJet g B p) z))) := by
  rw [normalMetric_eq_pullback g B hg hB hsym]
  exact MetricDensity.density_pullMetric (stdOrthonormalBasis ℝ Space).toBasis _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.CoordinateOperator
open HodgeNormalSymbol EuclideanEnergy
open scoped RealInnerProductSpace ContDiff
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma basis_expansion (v : V) : v = ∑ i, v i • e i := by
  simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e]
    using ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v).symm

end TamingCompatibility.GeometricHilbert.CoordinateOperator


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_2
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_2
lemma normalMap_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : ContDiff ℝ ∞ (normalMap g B q) :=
  contDiff_const.add ((B q).contDiff.comp (coordinateJet_contDiff _))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open _root_.MeasureTheory MeasureTheory.Measure Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace W] [CompleteSpace Q] in
lemma differential_congr_nhds (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) {u v : V → W} {x : V} (h : u =ᶠ[𝓝 x] v) :
    differential e a b u x = differential e a b v x := by
  simp only [differential,h.fderiv_eq,h.eq_of_nhds]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace W] [CompleteSpace Q] in
lemma differential_zero_off (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (u : V → W) {x : V} (hx : x ∉ tsupport u) :
    differential e a b u x = 0 := by
  have he : u =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [differential_congr_nhds e a b he]
  simp [differential]

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalInverse
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedSpace
variable (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q = Bq)

lemma geometricNormalChart_symm_right {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q Bq hBq).target) :
    normalMap g B x.1 ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 := by
  have he := congrArg Prod.snd ((geometricNormalChart g B hg hB q Bq hBq).right_inv hx)
  change normalMap g B ((geometricNormalChart g B hg hB q Bq hBq).symm x).1
    ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 at he
  rw [geometricNormalChart_symm_fst g B hg hB q Bq hBq hx] at he
  exact he

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {E F W : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup W]
attribute [local instance] Classical.propDecidable

lemma push_apply (C : OpenPartialHomeomorph E F) (f : E → W) {x : E} (hx : x ∈ C.source) :
    push C f (C x) = f x := by
  simp [push,C.map_source hx,C.left_inv hx]

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPatch
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedSpace
lemma leadingPatch_apply (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source) :
    leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (x.1,normalMap g B x.1 x.2) =
      leadingCoordinate J α ht p D g B ψ χ t x :=
  KernelExtension.push_apply _ _ hx

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixInitial
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialSliceMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialSliceMetricTensorNormedSpace
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)

lemma normalMap_slice_injective (q : Space) :
    InjOn (normalMap g B q) {z | (q,z) ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source} := by
  intro z hz w hw he
  have hc : geometricNormalChart g B hg hB q₀ Bq hBq (q,z) =
      geometricNormalChart g B hg hB q₀ Bq hBq (q,w) := by
    simpa only [geometricNormalChart_apply,Prod.mk.injEq,true_and] using he
  exact congrArg Prod.snd ((geometricNormalChart g B hg hB q₀ Bq hBq).injOn hz hw hc)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAtlasPatches
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r863d6f_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r863d6f_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma normalCutoff_tsupport : tsupport (D.normalCutoff : Space → ℝ) ⊆ Metric.closedBall (0 : Space) D.radius := by
  rw [D.normalCutoff.tsupport_eq]
  apply Metric.closedBall_subset_closedBall
  change D.radius/2 ≤ D.radius
  linarith [D.radius_pos]

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization NormalJets NormalMetricCalculus
open CoordinateOperator Filter Set _root_.MeasureTheory HodgeNormalSymbol
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma ParametrixData.density_actual {p : X} (D : ParametrixData J α ht p)
    {z : Space} (hz : z ∈ D.actualDomain) :
    volumeDensity (D.metricExtension z) = chartDensity J α p z := by
  rw [D.metric_actual z hz,coordinateMetric_bilinear J α ht p
    (D.chart.domain_subset (D.actual_subset hz))]
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixFormWeak
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_8_r863d6f_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_8_r863d6f_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma weakSliceDomain_open (q : Space) : IsOpen (E.weakSliceDomain q) :=
  (parametrixDomain_open J α ht p E.chart E.metricExtension E.frameExtension E.metric_smooth
    E.frame_smooth (extChartAt Model p p) E.centerFrame E.centerFrame_eq E.actualDomain
    E.actual_open).preimage (continuous_const.prodMk continuous_id)

lemma cutoff_weakSliceDomain {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius) :
    tsupport (E.normalCutoff : Space → ℝ) ⊆ E.weakSliceDomain q :=
  fun _ hz => E.tube ⟨hq,E.normalCutoff_tsupport hz⟩

lemma weakSliceDomain_normal {q z : Space} (hz : z ∈ E.weakSliceDomain q) :
    (q,z) ∈ normalDomain J α ht p E.chart E.metricExtension E.frameExtension := hz.1.2.1

lemma weakSliceDomain_actual {q z : Space} (hz : z ∈ E.weakSliceDomain q) :
    normalMap E.metricExtension E.frameExtension q z ∈ E.actualDomain := hz.2

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupMetricTensorSpace_9_r863d6f_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_9_r863d6f_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
omit [CompactSpace X] in
lemma leadingSlice_normal (p : A.centers) (q : Space) (t : ℝ) (u : W) {z : Space}
    (hz : (q,z) ∈ (E p).normalChart.source) :
    leadingSlice J α ht A E p q t u (normalMap (E p).metricExtension (E p).frameExtension q z) =
      normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension (q,z)
        ((E p).normalCutoff z • NormalHeatResidual.modelSection t (coordinatePartition A p q • u) z) := by
  unfold leadingSlice partitionLeading
  rw [leadingPatch_apply J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val) (E p).centerFrame
    (E p).centerFrame_eq (coordinatePartition A p) (E p).normalCutoff t hz]
  simp only [leadingCoordinate,smul_apply,NormalHeatResidual.modelSection,map_smul,smul_smul]
  congr 1
  ring

omit [CompactSpace X] in
lemma leadingSlice_tsupport (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (leadingSlice J α ht A E p q t u) ⊆
      normalMap (E p).metricExtension (E p).frameExtension q ''
        tsupport ((E p).normalCutoff : Space → ℝ) := by
  classical
  apply closure_minimal _
    (((E p).normalCutoff.hasCompactSupport).image
      (normalMap_contDiff (E p).metricExtension (E p).frameExtension q).continuous).isClosed
  intro y hy
  have htarget : (q,y) ∈ (E p).normalChart.target := by
    by_contra hn
    apply hy
    change (if (q,y) ∈ (E p).normalChart.target then
      leadingCoordinate J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
        (coordinatePartition A p) (E p).normalCutoff t ((E p).normalChart.symm (q,y)) else 0) u = 0
    rw [ite_eq_right hn,zero_apply]
  let z := ((E p).normalChart.symm (q,y)).2
  have hf : ((E p).normalChart.symm (q,y)).1 = q :=
    geometricNormalChart_symm_fst (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq htarget
  have hz : (q,z) ∈ (E p).normalChart.source := by
    have heq : (q,z) = (E p).normalChart.symm (q,y) := Prod.ext hf.symm rfl
    rw [heq]
    exact (E p).normalChart.map_target htarget
  have he : normalMap (E p).metricExtension (E p).frameExtension q z = y :=
    geometricNormalChart_symm_right (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq htarget
  refine ⟨z,?_,he⟩
  by_contra hn
  apply hy
  rw [← he,leadingSlice_normal J α ht A E p q t u hz,
    image_eq_zero_of_notMem_tsupport hn]
  simp

omit [CompactSpace X] in
lemma leadingSlice_normal_nhds (p : A.centers) (q : Space) (t : ℝ) (u : W) {z : Space}
    (hz : z ∈ (E p).weakSliceDomain q) :
    (leadingSlice J α ht A E p q t u ∘ normalMap (E p).metricExtension (E p).frameExtension q)
      =ᶠ[𝓝 z] (fun w => normalGauge J α ht p.val (E p).chart
        (E p).metricExtension (E p).frameExtension (q,w)
        ((E p).normalCutoff w • NormalHeatResidual.modelSection t (coordinatePartition A p q • u) w)) := by
  filter_upwards [((E p).weakSliceDomain_open q).mem_nhds hz] with w hw
  exact leadingSlice_normal J α ht A E p q t u hw.1.1.1

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchLocalInitial
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CoordinateOperator
open EuclideanEnergy HodgeNormalSymbol OperatorCalculus
open scoped RealInnerProductSpace

lemma sum_pullCoefficient_inverse (a : Fin 4 → W →L[ℝ] Q)
    (L : V ≃L[ℝ] V) (du : V →L[ℝ] W) :
    (∑ j, pullCoefficient a L.symm.toContinuousLinearMap j (du (L (e j)))) =
      ∑ i, a i (du (e i)) := by
  simp only [pullCoefficient,_root_.sum_apply,_root_.smul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, (L.symm (e i) j) • a i (du (L (e j)))) =
        a i (du (L (∑ j, (L.symm (e i) j) • e j))) := by
      simp only [map_sum,map_smul]
    _ = a i (du (e i)) := by rw [← basis_expansion (L.symm (e i)),L.apply_symm_apply]

lemma firstOrder_inverse_pull (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (u : V → W) (φ : V → V) (z : V) (L : V ≃L[ℝ] V)
    (hφ : HasFDerivAt φ L.toContinuousLinearMap z) (hu : DifferentiableAt ℝ u (φ z)) :
    firstOrder (fun i y => pullCoefficient (fun k => a k (φ y)) L.symm.toContinuousLinearMap i)
      (fun y => b (φ y)) (u ∘ φ) z = firstOrder a b u (φ z) := by
  simp only [firstOrder,(hu.hasFDerivAt.comp z hφ).fderiv,ContinuousLinearMap.comp_apply,
    Function.comp_apply]
  exact congrArg (fun w => w + b (φ z) (u (φ z)))
    (sum_pullCoefficient_inverse (fun k => a k (φ z)) L (fderiv ℝ u (φ z)))

end TamingCompatibility.GeometricHilbert.CoordinateOperator

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms HodgeNormalSymbol EuclideanEnergy OperatorCalculus CoordinateOperator NormalJets
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma pulled_firstOrder (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (q z : Space)
    (hL : (normalDifferential g B q z).IsInvertible)
    (u : Space → W) (hu : DifferentiableAt ℝ u (normalMap g B q z)) :
    differential e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
      (u ∘ normalMap g B q) z = HodgeChart.normalOperator J α ht p D u (normalMap g B q z) := by
  obtain ⟨L,hL⟩ := hL
  have hφ : HasFDerivAt (normalMap g B q) L.toContinuousLinearMap z := by
    rw [hL]
    exact centeredDisplacement_hasFDerivAt g B hg hB hsym q z
  unfold differential pulledA pulledB
  rw [← hL,ContinuousLinearMap.inverse_equiv]
  exact firstOrder_inverse_pull (HodgeChart.normalA J α ht p D) (HodgeChart.normalB J α ht p D)
    u (normalMap g B q) z L hφ hu

lemma pulled_energy (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (q z : Space)
    (hL : (normalDifferential g B q z).IsInvertible)
    (u v : Space → W) (hu : DifferentiableAt ℝ u (normalMap g B q z))
    (hv : DifferentiableAt ℝ v (normalMap g B q z)) :
    ⟪differential e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
      (u ∘ normalMap g B q) z,
      differential e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
      (v ∘ normalMap g B q) z⟫ =
    ⟪HodgeChart.normalOperator J α ht p D u (normalMap g B q z),
      HodgeChart.normalOperator J α ht p D v (normalMap g B q z)⟫ := by
  rw [pulled_firstOrder J α ht p D g B hg hB hsym q z hL u hu,
    pulled_firstOrder J α ht p D g B hg hB hsym q z hL v hv]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalSliceIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_10_r863d6f_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_10_r863d6f_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma normal_slice_integral {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    (F : Space → ℝ)
    (hF : Function.support F ⊆ normalMap E.metricExtension E.frameExtension q ''
      tsupport (E.normalCutoff : Space → ℝ)) :
    (∫ y, volumeDensity (E.metricExtension y) * F y) =
      ∫ z in E.weakSliceDomain q, normalDensity E.metricExtension E.frameExtension (q,z) *
        F (normalMap E.metricExtension E.frameExtension q z) := by
  let U := E.weakSliceDomain q
  let φ := normalMap E.metricExtension E.frameExtension q
  have hf : ∀ y, y ∉ φ '' U → volumeDensity (E.metricExtension y) * F y = 0 := by
    intro y hy
    have hFy : F y = 0 := by
      by_contra hn
      obtain ⟨z,hz,rfl⟩ := hF hn
      exact hy ⟨z,E.cutoff_weakSliceDomain hq hz,rfl⟩
    rw [hFy,mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf]
  have hi : InjOn φ U := (normalMap_slice_injective E.metricExtension E.frameExtension
    E.metric_smooth E.frame_smooth (extChartAt Model p p) E.centerFrame E.centerFrame_eq q).mono
      (fun _ hz => hz.1.1.1)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (E.weakSliceDomain_open q).measurableSet
    (fun z (_ : z ∈ U) => ((normalMap_contDiff E.metricExtension E.frameExtension q).differentiable
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt.hasFDerivAt.hasFDerivWithinAt) hi]
  apply setIntegral_congr_fun (E.weakSliceDomain_open q).measurableSet
  intro z _
  dsimp only
  rw [normalDensity,normal_density_jacobian E.metricExtension E.frameExtension E.metric_smooth
    E.frame_smooth E.metric_symmetric]
  change |(fderiv ℝ φ z).toLinearMap.det| *
      (volumeDensity (E.metricExtension (φ z)) * F (φ z)) =
    (|(fderiv ℝ φ z).toLinearMap.det| * volumeDensity (E.metricExtension (φ z))) * F (φ z)
  ring

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_11_r863d6f_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_11_r863d6f_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma cutoffSection_tsupport (q : Space) (t : ℝ) (u : W) :
    tsupport (E.cutoffSection q t u) ⊆ tsupport (E.normalCutoff : Space → ℝ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hn
  exact hz (by simp only [cutoffSection,image_eq_zero_of_notMem_tsupport hn,zero_smul,map_zero])

end ParametrixData
variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupMetricTensorSpace_11_r863d6f_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_11_r863d6f_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hE in
lemma leadingSlice_energy_point (hs : IsSmooth α) (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a)
    {z : Space} (hz : z ∈ (E p).weakSliceDomain q) :
    let D := (E p).chart
    let g := (E p).metricExtension
    let B := (E p).frameExtension
    ⟪differential EuclideanEnergy.e (pulledA J α ht p.val D g B q) (pulledB J α ht p.val D g B q)
        (HodgeChart.rawVector J α ht p.val D a ∘ normalMap g B q) z,
      differential EuclideanEnergy.e (pulledA J α ht p.val D g B q) (pulledB J α ht p.val D g B q)
        ((E p).cutoffSection q t (coordinatePartition A p q • u)) z⟫ =
    ⟪HodgeChart.normalOperator J α ht p.val D (HodgeChart.rawVector J α ht p.val D a)
        (normalMap g B q z),
      HodgeChart.normalOperator J α ht p.val D (leadingSlice J α ht A E p q t u)
        (normalMap g B q z)⟫ := by
  dsimp only
  have he : (leadingSlice J α ht A E p q t u ∘
      normalMap (E p).metricExtension (E p).frameExtension q) =ᶠ[𝓝 z]
      (E p).cutoffSection q t (coordinatePartition A p q • u) :=
    leadingSlice_normal_nhds J α ht A E p q t u hz
  rw [← differential_congr_nhds EuclideanEnergy.e
    (pulledA J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension q)
    (pulledB J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension q) he]
  apply pulled_energy J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    (E p).metric_smooth (E p).frame_smooth (E p).metric_symmetric q z
    ((E p).weakSliceDomain_normal hz).1.2
  · exact ((HodgeChart.rawVector_smooth J α ht p.val (E p).chart ha).contDiffAt
      ((E p).chart.domain_open.mem_nhds ((E p).actual_subset
        ((E p).weakSliceDomain_actual hz)))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact (leadingSlice_smooth J α ht A E hE hs p q htp u).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.differentiableAt

include hE in
lemma leadingSlice_energy_integral (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    let D := (E p).chart
    let g := (E p).metricExtension
    let B := (E p).frameExtension
    (∫ y, chartDensity J α p.val y *
      ⟪HodgeChart.normalOperator J α ht p.val D (HodgeChart.rawVector J α ht p.val D a) y,
        HodgeChart.normalOperator J α ht p.val D (leadingSlice J α ht A E p q t u) y⟫) =
    ∫ z, normalDensity g B (q,z) *
      ⟪differential EuclideanEnergy.e (pulledA J α ht p.val D g B q) (pulledB J α ht p.val D g B q)
          (HodgeChart.rawVector J α ht p.val D a ∘ normalMap g B q) z,
        differential EuclideanEnergy.e (pulledA J α ht p.val D g B q) (pulledB J α ht p.val D g B q)
          ((E p).cutoffSection q t (coordinatePartition A p q • u)) z⟫ := by
  dsimp only
  let F := fun y =>
    ⟪HodgeChart.normalOperator J α ht p.val (E p).chart
        (HodgeChart.rawVector J α ht p.val (E p).chart a) y,
      HodgeChart.normalOperator J α ht p.val (E p).chart (leadingSlice J α ht A E p q t u) y⟫
  have hFs : Function.support F ⊆ tsupport (leadingSlice J α ht A E p q t u) := by
    intro y hy
    by_contra hn
    exact hy (by dsimp only [F]; rw [HodgeChart.normalOperator_zero_off J α ht p.val
      (E p).chart _ hn,inner_zero_right])
  have hd : (∫ y, chartDensity J α p.val y * F y) =
      ∫ y, volumeDensity ((E p).metricExtension y) * F y := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : F y = 0
    · simp only [hy,mul_zero]
    · obtain ⟨z,hz,rfl⟩ := leadingSlice_tsupport J α ht A E p q t u (hFs hy)
      rw [(E p).density_actual J α ht ((E p).weakSliceDomain_actual
        ((E p).cutoff_weakSliceDomain hq hz))]
  change (∫ y, chartDensity J α p.val y * F y) = _
  rw [hd,(E p).normal_slice_integral hq F (hFs.trans (leadingSlice_tsupport J α ht A E p q t u))]
  rw [setIntegral_congr_fun ((E p).weakSliceDomain_open q).measurableSet
    (fun z hz => congrArg (fun w => normalDensity (E p).metricExtension (E p).frameExtension (q,z) * w)
      (leadingSlice_energy_point J α ht A E hE hs p q htp u a ha hz).symm)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hn : z ∉ tsupport ((E p).cutoffSection q t (coordinatePartition A p q • u)) :=
    fun hh => hz ((E p).cutoff_weakSliceDomain hq ((E p).cutoffSection_tsupport q t _ hh))
  rw [differential_zero_off EuclideanEnergy.e _ _ _ hn,inner_zero_right,mul_zero]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchPairing
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
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_12_r863d6f_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_12_r863d6f_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma slice_pairing_integral {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    (f k kN : Space → W)
    (hk : Function.support k ⊆ normalMap E.metricExtension E.frameExtension q ''
      tsupport (E.normalCutoff : Space → ℝ))
    (hN : Function.support kN ⊆ tsupport (E.normalCutoff : Space → ℝ))
    (he : ∀ z ∈ E.weakSliceDomain q, k (normalMap E.metricExtension E.frameExtension q z) = kN z) :
    (∫ y, chartDensity J α p y * ⟪f y,k y⟫) =
      ∫ z, normalDensity E.metricExtension E.frameExtension (q,z) *
        ⟪f (normalMap E.metricExtension E.frameExtension q z),kN z⟫ := by
  let F := fun y => ⟪f y,k y⟫
  have hFs : Function.support F ⊆ Function.support k := by
    intro y hy hkzero
    exact hy (by simp only [F,hkzero,inner_zero_right])
  have hd : (∫ y, chartDensity J α p y * F y) =
      ∫ y, volumeDensity (E.metricExtension y) * F y := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : F y = 0
    · simp only [hy,mul_zero]
    · obtain ⟨z,hz,rfl⟩ := hk (hFs hy)
      rw [E.density_actual J α ht (E.weakSliceDomain_actual (E.cutoff_weakSliceDomain hq hz))]
  change (∫ y, chartDensity J α p y * F y) = _
  rw [hd,E.normal_slice_integral hq F (hFs.trans hk)]
  rw [setIntegral_congr_fun (E.weakSliceDomain_open q).measurableSet
    (fun z hz => congrArg (fun w => normalDensity E.metricExtension E.frameExtension (q,z) *
      ⟪f (normalMap E.metricExtension E.frameExtension q z),w⟫) (he z hz))]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hNz : kN z = 0 := Function.notMem_support.mp (fun hh => hz (E.cutoff_weakSliceDomain hq (hN hh)))
  rw [hNz,inner_zero_right,mul_zero]

end ParametrixData
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

local instance instNormedAddCommGroupMetricTensorSpace_12_r863d6f_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_12_r863d6f_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma leadingSlice_pairing_integral (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) (f : Space → W) :
    (∫ y, chartDensity J α p.val y * ⟪f y,leadingSlice J α ht A E p q t u y⟫) =
    ∫ z, normalDensity (E p).metricExtension (E p).frameExtension (q,z) *
      ⟪f (normalMap (E p).metricExtension (E p).frameExtension q z),
        (E p).cutoffSection q t (coordinatePartition A p q • u) z⟫ :=
  (E p).slice_pairing_integral hq f _ _
    ((subset_tsupport _).trans (leadingSlice_tsupport J α ht A E p q t u))
    ((subset_tsupport _).trans ((E p).cutoffSection_tsupport q t _))
    (fun _ hz => leadingSlice_normal J α ht A E p q t u hz.1.1.1)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupMetricTensorSpace_13_r863d6f_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_13_r863d6f_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hE in
lemma leadingSlice_weak_deriv_oai (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    HasDerivAt (fun s => ∫ y, chartDensity J α p.val y *
      ⟪HodgeChart.rawVector J α ht p.val (E p).chart a y,leadingSlice J α ht A E p q s u y⟫)
      ((∫ y, chartDensity J α p.val y *
        ⟪HodgeChart.rawVector J α ht p.val (E p).chart a y,residualSlice J α ht A E p q t u y⟫) -
       (∫ y, chartDensity J α p.val y *
        ⟪HodgeChart.normalOperator J α ht p.val (E p).chart (HodgeChart.rawVector J α ht p.val (E p).chart a) y,
          HodgeChart.normalOperator J α ht p.val (E p).chart (leadingSlice J α ht A E p q t u) y⟫)) t := by
  simp only [leadingSlice_pairing_integral J α ht A E p hq,
    residualSlice_pairing_integral J α ht A E p hq,
    leadingSlice_energy_integral J α ht A E hE hs p hq htp u a ha]
  exact (E p).cutoff_form_weak_deriv hs hq htp (coordinatePartition A p q • u) a ha

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv_oai.{u_1}
