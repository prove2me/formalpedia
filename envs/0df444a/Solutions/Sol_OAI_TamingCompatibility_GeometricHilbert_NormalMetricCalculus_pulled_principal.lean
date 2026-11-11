-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:18.074705+00:00
-- url     : https://prove2.me/submissions/ad4d7d78-271d-4b0b-bae7-b65bff1e27b3

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_MetricCalculus
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
section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity
open scoped ContDiff RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedAddCommGroupMetricTensorV
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedSpaceRealMetricTensorV
lemma metricOperator_apply (M : MetricTensor (V := V)) (u : V) :
    metricOperator M u = (InnerProductSpace.toDual ℝ V).symm (M u) := rfl

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMatrixEnergy
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
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy

theorem normalSymbol_adjoint_polarized (ξ η : V) :
    (normalSymbol ξ).adjoint ∘L normalSymbol η +
      (normalSymbol η).adjoint ∘L normalSymbol ξ =
      (2*⟪ξ,η⟫) • ContinuousLinearMap.id ℝ W := by
  apply ContinuousLinearMap.ext
  intro a
  apply ext_inner_left ℝ
  intro b
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.smul_apply,
    ContinuousLinearMap.id_apply,inner_smul_right,inner_add_right]
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  exact normalSymbol_polarized ξ η b a
end TamingCompatibility.HodgeNormalSymbol

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricOperatorInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open scoped RealInnerProductSpace
open NormalJets GeometricNormalCharts
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma metricOperator_inner (M : MetricTensor (V := V)) (u v : V) :
    ⟪metricOperator M u,v⟫ = M u v := by
  simp only [metricOperator_apply, InnerProductSpace.toDual_symm_apply]

lemma cometric_eq_frame (M : MetricTensor (V := V)) (B : V ≃L[ℝ] V)
    (hB : ∀ u v, M (B u) (B v) = ⟪u,v⟫) :
    cometric M = B.toContinuousLinearMap ∘L B.toContinuousLinearMap.adjoint := by
  have hM (u v : V) : M u v = ⟪B.symm u,B.symm v⟫ := by
    simpa only [B.apply_symm_apply] using hB (B.symm u) (B.symm v)
  have hc : metricOperator M ∘L (B.toContinuousLinearMap ∘L B.toContinuousLinearMap.adjoint) =
      ContinuousLinearMap.id ℝ V := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    change ⟪metricOperator M (B (B.toContinuousLinearMap.adjoint u)),v⟫ = ⟪u,v⟫
    rw [metricOperator_inner,hM,B.symm_apply_apply,ContinuousLinearMap.adjoint_inner_left]
    change ⟪u,B (B.symm v)⟫ = _
    rw [B.apply_symm_apply]
  have hi : Function.Injective (metricOperator M) := by
    intro u v he
    have hh (w) := congrArg (fun f : V => ⟪f,w⟫) he
    simp only [metricOperator_inner,hM] at hh
    apply B.symm.injective
    apply ext_inner_right ℝ
    intro z
    simpa only [B.symm_apply_apply] using hh (B z)
  apply ContinuousLinearMap.inverse_eq hc
  apply ContinuousLinearMap.ext
  intro u
  apply hi
  have hh := congrArg (fun f : V →L[ℝ] V => f (metricOperator M u)) hc
  exact hh

lemma principal_pullback_frame (M : MetricTensor (V := V)) (B L : V ≃L[ℝ] V)
    (hB : ∀ u v, M (B u) (B v) = ⟪u,v⟫) (i j : Fin 4) :
    principal (MetricDensity.pullMetric M L.toContinuousLinearMap) i j =
      ⟪(B.toContinuousLinearMap.adjoint ∘L L.symm.toContinuousLinearMap.adjoint)
          (EuclideanSpace.basisFun (Fin 4) ℝ i),
        (B.toContinuousLinearMap.adjoint ∘L L.symm.toContinuousLinearMap.adjoint)
          (EuclideanSpace.basisFun (Fin 4) ℝ j)⟫ := by
  have hBL : ∀ u v, MetricDensity.pullMetric M L.toContinuousLinearMap
      ((B.trans L.symm) u) ((B.trans L.symm) v) = ⟪u,v⟫ := by
    intro u v
    change M (L (L.symm (B u))) (L (L.symm (B v))) = _
    simpa only [L.apply_symm_apply] using hB u v
  rw [principal,cometric_eq_frame _ (B.trans L.symm) hBL]
  change ⟪(B.trans L.symm).toContinuousLinearMap
    ((B.trans L.symm).toContinuousLinearMap.adjoint _),_⟫ = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have he : (B.trans L.symm).toContinuousLinearMap =
      L.symm.toContinuousLinearMap ∘L B.toContinuousLinearMap := rfl
  rw [he,ContinuousLinearMap.adjoint_comp]

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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

lemma pullCoefficient_symbol (b : Fin 4 → V) (C : V →L[ℝ] V) (j : Fin 4) :
    pullCoefficient (HodgeFrozenEnergy.coefficient b) C j =
      normalSymbol (WithLp.toLp 2 (fun k => C (b k) j)) := by
  have hξ : (WithLp.toLp 2 (fun k => C (b k) j) : V) =
      ∑ i, (C (e i) j) • LocalMatrixOperator.frameCovector b i := by
    ext k
    change C (b k) j = _
    conv_lhs => rw [basis_expansion (b k)]
    simp [LocalMatrixOperator.frameCovector,map_sum,map_smul,
      mul_comm]
  rw [hξ]
  change _ = symbolMap _
  simp only [map_sum,map_smul,symbolMap_apply]
  rfl

lemma pullCoefficient_polarized (b : Fin 4 → V) (C : V →L[ℝ] V) (i j : Fin 4) :
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) C i).adjoint ∘L
        pullCoefficient (HodgeFrozenEnergy.coefficient b) C j +
      (pullCoefficient (HodgeFrozenEnergy.coefficient b) C j).adjoint ∘L
        pullCoefficient (HodgeFrozenEnergy.coefficient b) C i =
      (2 * ⟪(WithLp.toLp 2 (fun k => C (b k) i) : V),
        WithLp.toLp 2 (fun k => C (b k) j)⟫) • ContinuousLinearMap.id ℝ W := by
  simp only [pullCoefficient_symbol]
  exact normalSymbol_adjoint_polarized _ _

end TamingCompatibility.GeometricHilbert.CoordinateOperator


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_FirstJetGauge
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open scoped RealInnerProductSpace
open NormalJets GeometricNormalCharts CoordinateOperator HodgeNormalSymbol
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma pulled_covector (b : Fin 4 → V) (C : V →L[ℝ] V) (i : Fin 4) :
    (WithLp.toLp 2 (fun k => C (b k) i) : V) =
      (frameMap b).adjoint (C.adjoint (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,
    EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left]
  simp [frameMap_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct]

lemma pulled_principal_oai (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (L : V ≃L[ℝ] V) (i j : Fin 4) :
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i).adjoint ∘L
      pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j +
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j).adjoint ∘L
      pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i =
      (2 * principal (MetricDensity.pullMetric g.bilinear L.toContinuousLinearMap) i j) •
        ContinuousLinearMap.id ℝ W := by
  rw [pullCoefficient_polarized,principal_pullback_frame g.bilinear (frameEquiv g b hb) L
    (frameMap_metric g b hb),pulled_covector,pulled_covector]
  rfl

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal_oai := @OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal_oai
