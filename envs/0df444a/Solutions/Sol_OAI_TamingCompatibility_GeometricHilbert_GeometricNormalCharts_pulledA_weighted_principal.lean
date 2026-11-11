-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:09:15.960192+00:00
-- url     : https://prove2.me/submissions/fc11dfa9-cca5-47ef-b73e-1e12b107eb45

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_centeredDisplacement_hasFDerivAt
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_pulled_principal

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

lemma normalJacobian_contDiff (G : MetricDerivative (V := V)) :
    ContDiff ℝ ∞ (normalJacobian G) := contDiff_const.sub (christoffel G).contDiff

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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
lemma normalDifferential_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : ContDiff ℝ ∞ (normalDifferential g B q) :=
  contDiff_const.clm_comp (normalJacobian_contDiff _)
lemma normalMap_fderiv (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (q z : Space) :
    fderiv ℝ (normalMap g B q) z = normalDifferential g B q z :=
  (centeredDisplacement_hasFDerivAt g B hg hB hsym q z).fderiv

lemma normalDifferential_eventually_invertible (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) (hBq : (B q).IsInvertible) :
    ∀ᶠ z in 𝓝 0, (normalDifferential g B q z).IsInvertible := by
  have hmem : B q ∈ Set.range (fun e : Space ≃L[ℝ] Space => e.toContinuousLinearMap) := hBq
  have he := (normalDifferential_contDiff g B q).continuous.continuousAt (x := (0 : Space))
    ((ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := Space) (F := Space)).mem_nhds
      (by simpa using hmem))
  exact he

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pulledA_weighted_principal_oai (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v)
    (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (hgact : ∀ x ∈ U, g x = (coordinateMetric J α ht p x).bilinear)
    (q : Space) (hq : q ∈ U) (hBq : (B q).IsInvertible) (i j : Fin 4) :
    let ρ := fun z => volumeDensity (normalMetric g B (q,z))
    let a := pulledA J α ht p D g B q
    (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z) =ᶠ[𝓝 0]
      (fun z => (2*(ρ z*principal (normalMetric g B (q,z)) i j)) •
        ContinuousLinearMap.id ℝ W) := by
  dsimp only
  have hmap : ∀ᶠ z in 𝓝 0, normalMap g B q z ∈ U :=
    (normalMap_contDiff g B q).continuous.continuousAt
      (by simpa using hU.mem_nhds hq)
  filter_upwards [hmap,normalDifferential_eventually_invertible g B q hBq] with z hz hL
  obtain ⟨L,hL⟩ := hL
  have hg' : normalMetric g B (q,z) =
      MetricDensity.pullMetric (coordinateMetric J α ht p (normalMap g B q z)).bilinear
        L.toContinuousLinearMap := by
    rw [normalMetric_eq_pullback g B hg hB hsym]
    change MetricDensity.pullMetric (g (normalMap g B q z))
      (fderiv ℝ (normalMap g B q) z) = _
    rw [normalMap_fderiv g B hg hB hsym, ←hL, hgact _ hz]
  have hp := pulled_principal (coordinateMetric J α ht p (normalMap g B q z))
    (fun k => D.frame k (normalMap g B q z))
    (D.frame_gram _ (hUD hz)) L i j
  simp only [weightedPrincipal, map_smul, ContinuousLinearMap.smul_comp]
  rw [←smul_add]
  have ha (k : Fin 4) : pulledA J α ht p D g B q k z =
      pullCoefficient (HodgeFrozenEnergy.coefficient (fun l => D.frame l (normalMap g B q z)))
        L.symm.toContinuousLinearMap k := by
    simp only [pulledA,←hL,ContinuousLinearMap.inverse_equiv]
    rfl
  rw [ha i,ha j,hp,smul_smul,hg']
  congr 1
  ring

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

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal_oai.{u_1}
