-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_unitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:09:06.885695+00:00
-- url     : https://prove2.me/submissions/08bcb5a4-00b9-4de1-8703-7666f5a9d3bc

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc017
import Definitions.Def_OAIQ239Tc018
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_ActualData_jets

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.OrthogonalJets
open scoped RealInnerProductSpace ContDiff
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gauge_unitary (A : V →L[ℝ] End (W := W))
    (hA : ∀ z, (A z).adjoint = - A z) (z : V) : gauge A z ∈ unitary (End (W := W)) := by
  let _ : NormedAlgebra ℚ (End (W := W)) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  exact (skewAdjoint.mem_iff).mpr (hA z)

end TamingCompatibility.GeometricHilbert.OrthogonalJets


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_FirstJetGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open scoped ContDiff RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma halfJet_skew (q : ι → V →L[ℝ] ℝ) (b : ι → End (W := W))
    (hb : ∀ i, (b i).adjoint = -b i) (z : V) :
    (halfJet q b z).adjoint = - halfJet q b z := by
  simp [halfJet, map_sum, map_smul, hb, smul_neg, Finset.sum_neg_distrib]

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open FirstJetGauge
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
lemma firstMatrix_eq (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) : firstMatrix e a b ρ = actualSquareFirst e a b ρ := by
  funext j x
  unfold firstMatrix actualSquareFirst squareFirst principalMatrix weightedPrincipal
  rfl
end TamingCompatibility.GeometricHilbert.OperatorCalculus

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

attribute [local irreducible] normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_5
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_5
lemma normalGauge_unitary_oai (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B) (z : Space) :
    normalGauge J α ht p D g B (q,z) ∈ unitary (W →L[ℝ] W) := by
  obtain ⟨ha,hb,hρ,hρone,hρzero,hpr,hskew⟩ := hactual.jets J α hs ht p D q g B hg hB
  unfold normalGauge
  apply OrthogonalJets.gauge_unitary
  intro v
  apply halfJet_skew
  intro j
  have he : normalFirst J α ht p D g B j (q,0) =
      actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun z => volumeDensity (normalMetric g B (q,z))) j 0 := by
    unfold normalFirst normalDensity
    rw [firstMatrix_eq]
  rw [he]
  exact hskew j

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_unitary_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_unitary_oai.{u_1}
