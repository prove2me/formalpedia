-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:09:14.752483+00:00
-- url     : https://prove2.me/submissions/b7bd1c6a-ee4b-4152-b0de-ab3bb87ce4e7

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021

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

lemma christoffel_symm (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (u v : V) :
    christoffel G u v = christoffel G v u := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffel_apply, christoffelValue_inner]
  rw [hG w u v]
  ring

lemma coordinateJet_hasFDerivAt (G : MetricDerivative (V := V)) (z : V) :
    HasFDerivAt (coordinateJet G)
      (ContinuousLinearMap.id ℝ V - (1/2 : ℝ) •
        (christoffel G z + (christoffel G).flip z)) z := by
  convert! (hasFDerivAt_id z).sub
    (((christoffel G).hasFDerivAt.clm_apply (hasFDerivAt_id z)).const_smul (1/2 : ℝ)) using 1
  all_goals try with_reducible_and_instances rfl

lemma coordinateJet_hasFDerivAt_normal (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (z : V) :
    HasFDerivAt (coordinateJet G) (normalJacobian G z) z := by
  convert coordinateJet_hasFDerivAt G z using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [normalJacobian, sub_apply, smul_apply, add_apply,
    ContinuousLinearMap.flip_apply]
  rw [christoffel_symm G hG v z]
  module

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalChart
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelCLM_apply
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

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.instNormedSpaceRealContinuousLinearMapId_solutions
local instance instNormedAddCommGroupMetricTensor_r9bb0db_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensor_r9bb0db_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
omit [FiniteDimensional ℝ V] in

lemma metricDerivative_symmetric (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : HasFDerivAt g G 0)
    (hsym : ∀ z v w, g z v w = g z w v) :
    ∀ u v w, G u v w = G u w v := by
  intro u v w
  have hvw := (hg.clm_apply (hasFDerivAt_const v (0 : V))).clm_apply
    (hasFDerivAt_const w (0 : V))
  have hwv := (hg.clm_apply (hasFDerivAt_const w (0 : V))).clm_apply
    (hasFDerivAt_const v (0 : V))
  have heq : (fun z => g z v w) = (fun z => g z w v) := funext fun z => hsym z v w
  rw [heq] at hvw
  have he := congrArg (fun L : V →L[ℝ] ℝ => L u) (hvw.unique hwv)
  simpa using he

end TamingCompatibility.GeometricHilbert.NormalJets

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Set Metric
open scoped ContDiff
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] in
lemma dpos_eq (F : P × V → W) (hF : Differentiable ℝ F) (p : P) (z : V) :
    dpos F (p,z) = fderiv ℝ (fun u => F (p,u)) z := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (c := p) z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)
  have hh := (hF (p,z)).hasFDerivAt.comp z hd
  exact hh.fderiv.symm

end TamingCompatibility.GeometricHilbert.UniformJets

end

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricDerivativeSpace
lemma affineMetric_symm (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ∀ x v w, g x v w = g x w v)
    (pz : Space × Space) (v w : Space) : affineMetric g B pz v w = affineMetric g B pz w v :=
  hg _ _ _

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricDerivativeSpace
lemma metricJet_eq (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) (p : Space) :
    metricJet g B p = fderiv ℝ (fun z => affineMetric g B (p,z)) 0 :=
  UniformJets.dpos_eq _ ((affineMetric_contDiff g B hg hB).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p 0

lemma centeredDisplacement_hasFDerivAt (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    HasFDerivAt (fun u => p+B p (coordinateJet (metricJet g B p) u))
      ((B p).comp (normalJacobian (metricJet g B p) z)) z := by
  have hM : ContDiff ℝ ∞ (fun z => affineMetric g B (p,z)) :=
    (affineMetric_contDiff g B hg hB).comp (contDiff_const.prodMk contDiff_id)
  have hder : HasFDerivAt (fun z => affineMetric g B (p,z)) (metricJet g B p) 0 := by
    rw [metricJet_eq g B hg hB]
    exact (hM.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt
  have hG := metricDerivative_symmetric _ _ hder (fun z => affineMetric_symm g B hsym (p,z))
  exact ((B p).hasFDerivAt.comp z (coordinateJet_hasFDerivAt_normal _ hG z)).const_add p

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

lemma pulled_principal (g : MetricModel.Metric V) (b : Fin 4 → V)
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

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
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
lemma normalMap_fderiv (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (q z : Space) :
    fderiv ℝ (normalMap g B q) z = normalDifferential g B q z :=
  (centeredDisplacement_hasFDerivAt g B hg hB hsym q z).fderiv

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeCompactResidual
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_6
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_6
lemma pulledA_scalar_at_oai (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
    (hx : (q,z) ∈ regularSet J α ht p D g B)
    (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
    (i j : Fin 4) :
    (pulledA J α ht p D g B q i z).adjoint ∘L pulledA J α ht p D g B q j z +
      (pulledA J α ht p D g B q j z).adjoint ∘L pulledA J α ht p D g B q i z =
      (2*normalPrincipal g B i j (q,z)) • ContinuousLinearMap.id ℝ W := by
  obtain ⟨L,hL⟩ := hx.2
  have hm : normalMetric g B (q,z) =
      MetricDensity.pullMetric (coordinateMetric J α ht p (normalMap g B q z)).bilinear
        L.toContinuousLinearMap := by
    rw [normalMetric_eq_pullback g B hg hB hsym]
    change MetricDensity.pullMetric (g (normalMap g B q z))
      (fderiv ℝ (normalMap g B q) z) = _
    rw [normalMap_fderiv g B hg hB hsym,←hL,hgact]
  have hp := pulled_principal (coordinateMetric J α ht p (normalMap g B q z))
    (fun k => D.frame k (normalMap g B q z)) (D.frame_gram _ hx.1) L i j
  have ha (k : Fin 4) : pulledA J α ht p D g B q k z =
      pullCoefficient (HodgeFrozenEnergy.coefficient (fun l => D.frame l (normalMap g B q z)))
        L.symm.toContinuousLinearMap k := by
    simp only [pulledA,←hL,ContinuousLinearMap.inverse_equiv]
    rfl
  rw [ha i,ha j,hp]
  simp only [normalPrincipal,hm]

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at_oai.{u_1}
