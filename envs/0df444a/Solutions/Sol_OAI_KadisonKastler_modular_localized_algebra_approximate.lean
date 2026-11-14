-- Prove2me | solution 1 for OAI.KadisonKastler.modular_localized_algebra_approximate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:58:08.581711+00:00
-- url     : https://prove2.me/submissions/588bd8d7-73eb-42b3-b413-a1847a911dd2

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K072
import Definitions.Def_Q260K042

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularGraphApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebraic approximation of modular translates in graph norm

The full closed-graph invariance gives simultaneous approximation of a
translated algebra vector and its adjoint vector by the same algebra
element. These are graph-norm approximations; no operator-norm bound is
asserted.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))

include hsep

/-- Simultaneous approximation of both coordinates of the closed graph. -/
theorem tomitaClosed_graph_approximate {x y : H}
    (hxy : (x, y) ∈ (tomitaClosedLinearOperator M J Ω 1).graph)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : Algebra M, ‖a.val Ω - x‖ < ε ∧ ‖J (star a.val Ω) - y‖ < ε := by
  rw [tomitaClosedLinearOperator_graph J Ω 1 hsep] at hxy
  let v := tomitaProductCoordinates.symm (x, y)
  have hv : v ∈ closure (Set.range (rescaledGraphMap M J Ω 1)) := hxy
  obtain ⟨w, ⟨a, rfl⟩, ha⟩ := (Metric.mem_closure_iff.mp hv) ε hε
  refine ⟨a, ?_, ?_⟩
  · have h := (PiLp.dist_apply_le (rescaledGraphMap M J Ω 1 a) v 0).trans_lt
      (show dist (rescaledGraphMap M J Ω 1 a) v < ε by rwa [dist_comm])
    have hv0 : v 0 = x := rfl
    simpa only [rescaledGraphMap_apply, rescaledGraphVector_zero, hv0, dist_eq_norm] using h
  · have h := (PiLp.dist_apply_le (rescaledGraphMap M J Ω 1 a) v 1).trans_lt
      (show dist (rescaledGraphMap M J Ω 1 a) v < ε by rwa [dist_comm])
    have hv1 : v 1 = y := rfl
    simpa only [rescaledGraphMap_apply, rescaledGraphVector_one, hv1, one_smul, dist_eq_norm] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The positive self-adjoint square root of the modular operator

Removing the linear polar unitary from the closed Tomita operator gives an
unbounded operator with graph `(r a, q a)`, where the two commuting positive
roots satisfy `r² + q² = 1`. These coordinates prove self-adjointness directly.
-/

namespace KadisonKastler

noncomputable section

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

private theorem modularPositiveOperator_graph_transport (x y : H) :
    (x, y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph ↔
      (x, tomitaLinearPolarUnitary J Ω hsep hcyc y) ∈
        (tomitaClosedLinearOperator M J Ω 1).graph := by
  simp only [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨v, hv, hy⟩
    refine ⟨v, hv, ?_⟩
    change (tomitaClosedLinearOperator M J Ω 1) v = _
    rw [← hy]
    exact ((tomitaLinearPolarUnitary J Ω hsep hcyc).apply_symm_apply _).symm
  · rintro ⟨v, hv, hy⟩
    refine ⟨v, hv, ?_⟩
    change (tomitaLinearPolarUnitary J Ω hsep hcyc).symm
      ((tomitaClosedLinearOperator M J Ω 1) v) = y
    rw [hy, LinearIsometryEquiv.symm_apply_apply]

theorem modularPositiveOperator_graph_iff (x y : H) :
    (x, y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph ↔
      ∃ a : H, tomitaGraphRoot (M := M) J Ω a = x ∧
        tomitaGraphComplementRoot (M := M) J Ω a = y := by
  rw [modularPositiveOperator_graph_transport,
    tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc]
  exact exists_congr fun a => and_congr_right fun _ =>
    (tomitaLinearPolarUnitary J Ω hsep hcyc).injective.eq_iff

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularThresholdBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative widths of the bounded modular spectral coordinates -/

namespace KadisonKastler

theorem modularCutThreshold_relative_width {r δ s : ℝ} (hδ : 0 ≤ δ)
    (hslo : modularCutThreshold (r+δ) ≤ s) (hshi : s ≤ modularCutThreshold r) :
    |s-modularCutThreshold r| ≤ (Real.exp δ-1)*modularCutThreshold r ∧
      |s-modularCutThreshold r| ≤ (Real.exp δ-1)*(1-modularCutThreshold r) := by
  have hE : 1 ≤ Real.exp δ := Real.one_le_exp_iff.mpr hδ
  have hA : 0 < Real.exp r := Real.exp_pos r
  have hAE : 0 < Real.exp r*Real.exp δ := mul_pos hA (Real.exp_pos δ)
  have hden : 0 < 1+Real.exp r*Real.exp δ := by positivity
  have hden' : 0 < 1+Real.exp r := by positivity
  have hbase : 0 ≤ Real.exp δ-1 := sub_nonneg.mpr hE
  have hratio : Real.exp r/(1+Real.exp r*Real.exp δ) ≤ 1 := by
    apply (div_le_one hden).mpr
    have hh := mul_le_mul_of_nonneg_left hE hA.le
    nlinarith
  have hdiff : modularCutThreshold r-modularCutThreshold (r+δ) =
      ((Real.exp δ-1)/(1+Real.exp r)) *
        (Real.exp r/(1+Real.exp r*Real.exp δ)) := by
    unfold modularCutThreshold
    rw [Real.exp_add]
    field_simp
    ring
  have hfirst : modularCutThreshold r - modularCutThreshold (r+δ) ≤
      (Real.exp δ-1)*modularCutThreshold r := by
    rw [hdiff]
    calc
      _ ≤ ((Real.exp δ-1)/(1+Real.exp r))*1 :=
        mul_le_mul_of_nonneg_left hratio (div_nonneg hbase hden'.le)
      _ = _ := by simp only [mul_one, modularCutThreshold, div_eq_mul_inv]
  have hsecond : modularCutThreshold r - modularCutThreshold (r+δ) ≤
      (Real.exp δ-1)*(1-modularCutThreshold r) := by
    have heq : modularCutThreshold r-modularCutThreshold (r+δ) =
        ((Real.exp δ-1)*(1-modularCutThreshold r))/(1+Real.exp r*Real.exp δ) := by
      unfold modularCutThreshold
      rw [Real.exp_add]
      field_simp
      ring
    rw [heq]
    exact div_le_self (mul_nonneg hbase
      (sub_nonneg.mpr (modularCutThreshold_lt_one r).le)) (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hshi)]
  constructor <;> linarith

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeSquareRootBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative square-root errors -/

namespace KadisonKastler

theorem relative_sqrt_sub_bound {s t ε : ℝ} (hs : 0 ≤ s) (ht : 0 < t)
    (h : |s-t| ≤ ε*t) :
    |Real.sqrt s-Real.sqrt t| ≤ ε*Real.sqrt t := by
  have htroot := Real.sqrt_pos.mpr ht
  have hsroot := Real.sqrt_nonneg s
  have hsquare := Real.sq_sqrt hs
  have htsquare := Real.sq_sqrt ht.le
  have hfactor : |Real.sqrt s-Real.sqrt t| * (Real.sqrt s+Real.sqrt t) = |s-t| := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt s+Real.sqrt t), ← abs_mul]
    congr 1
    nlinarith
  have hle : |Real.sqrt s-Real.sqrt t| * Real.sqrt t ≤ ε*t :=
    (mul_le_mul_of_nonneg_left (by linarith : Real.sqrt t ≤ Real.sqrt s+Real.sqrt t)
      (abs_nonneg _)).trans (hfactor.le.trans h)
  have he : ε*t = (ε*Real.sqrt t)*Real.sqrt t := by rw [mul_assoc, ← pow_two, htsquare]
  rw [he] at hle
  exact (mul_le_mul_iff_left₀ htroot).mp hle

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventLocalizedMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vector measures of vectors between two resolvent cuts -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventVectorMeasure_below_cut (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (r : ℝ) (hx : resolventLowerCut R r x = x) :
    ∀ᵐ s ∂resolventVectorMeasure R hR x, s.val < r := by
  let v : ResolventCyclicL2 R hR x :=
    ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ 1
  have hv : resolventCyclicIsometry R hR x v = x := resolventCyclicIsometry_one R hR x
  have he : resolventScalarMultiplier R hR x (resolventCutIndicator R r)
      (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v = v := by
    apply (resolventCyclicIsometry R hR x).injective
    rw [resolventCyclicIsometry_cut, hv, hx]
  have ha := resolventScalarMultiplier_apply_ae R hR x (resolventCutIndicator R r)
    (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v
  rw [he] at ha
  filter_upwards [ha, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (resolventVectorMeasure R hR x) (1 : C(spectrum ℝ R, ℂ))] with s hs hv'
  change v s = 1 at hv'
  rw [hv', mul_one] at hs
  by_contra hn
  simp [resolventCutIndicator, hn] at hs

theorem resolventVectorMeasure_above_cut (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (r : ℝ) (hx : resolventLowerCut R r x = 0) :
    ∀ᵐ s ∂resolventVectorMeasure R hR x, r ≤ s.val := by
  let v : ResolventCyclicL2 R hR x :=
    ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ 1
  have hv : resolventCyclicIsometry R hR x v = x := resolventCyclicIsometry_one R hR x
  have he : resolventScalarMultiplier R hR x (resolventCutIndicator R r)
      (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v = 0 := by
    apply (resolventCyclicIsometry R hR x).injective
    rw [resolventCyclicIsometry_cut, hv, hx, map_zero]
  have ha := resolventScalarMultiplier_apply_ae R hR x (resolventCutIndicator R r)
    (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v
  rw [he] at ha
  filter_upwards [ha, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (resolventVectorMeasure R hR x) (1 : C(spectrum ℝ R, ℂ)),
    Lp.coeFn_zero ℂ 2 (resolventVectorMeasure R hR x)] with s hs hv' hz
  change v s = 1 at hv'
  rw [hv', mul_one, hz] at hs
  by_contra hn
  have hsr : s.val < r := lt_of_not_ge hn
  simp [resolventCutIndicator, hsr] at hs

theorem resolventContinuousCalculus_local_bound
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) (l u : ℝ)
    (hlo : resolventLowerCut R l x = 0) (hhi : resolventLowerCut R u x = x)
    (f : C(spectrum ℝ R, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ s : spectrum ℝ R, l ≤ s.val → s.val < u → ‖f s‖ ≤ C) :
    ‖resolventContinuousCalculus R hR f x‖ ≤ C * ‖x‖ := by
  have ha := (resolventVectorMeasure_above_cut R hR x l hlo).and
    (resolventVectorMeasure_below_cut R hR x u hhi)
  have hi : Integrable (fun s => ‖f s‖^2) (resolventVectorMeasure R hR x) :=
    (f.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle := integral_mono_ae hi (integrable_const (C^2)) (ha.mono fun s hs =>
    pow_le_pow_left₀ (norm_nonneg _) (hb s hs.1 hs.2) 2)
  have hn := resolventContinuousVector_norm_sq R hR x f
  have hone := resolventContinuousVector_norm_sq R hR x 1
  change ‖resolventContinuousCalculus R hR f x‖^2 = _ at hn
  have hunit : resolventContinuousCalculus R hR (1 : C(spectrum ℝ R, ℂ)) x = x := by
    rw [map_one, one_apply_eq_self]
  change ‖resolventContinuousCalculus R hR (1 : C(spectrum ℝ R, ℂ)) x‖^2 = _ at hone
  rw [hunit] at hone
  simp only [ContinuousMap.one_apply, norm_one, one_pow] at hone
  rw [integral_const, smul_eq_mul] at hle
  rw [integral_const, smul_eq_mul, mul_one] at hone
  rw [← hn, ← hone] at hle
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  simpa only [mul_pow, mul_comm] using hle

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventLocalRootBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative root estimates from a localized vector measure -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventSqrt_local_error
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (hpos : 0 ≤ R)
    (x : H) (l u : ℝ)
    (hlo : resolventLowerCut R l x = 0) (hhi : resolventLowerCut R u x = x)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε)
    (hb : ∀ s : spectrum ℝ R, l ≤ s.val → s.val < u → |s.val-t| ≤ ε*t) :
    ‖CFC.sqrt R x - (Real.sqrt t : ℂ) • x‖ ≤ ε * Real.sqrt t * ‖x‖ := by
  let f : C(spectrum ℝ R, ℂ) := resolventSqrtFunction R - ContinuousMap.const _ (Real.sqrt t : ℂ)
  have he : resolventContinuousCalculus R hR f x =
      CFC.sqrt R x-(Real.sqrt t : ℂ) • x := by
    simp only [f, map_sub, resolventContinuousCalculus_sqrt R hR hpos, sub_apply]
    congr 1
    have hc : ContinuousMap.const (spectrum ℝ R) (Real.sqrt t : ℂ) =
        (Real.sqrt t : ℂ) • (1 : C(spectrum ℝ R, ℂ)) := by ext; simp
    rw [hc, map_smul, map_one, smul_apply, one_apply_eq_self]
  rw [← he]
  apply resolventContinuousCalculus_local_bound R hR x l u hlo hhi f (by positivity)
  intro s hs hu
  change ‖((Real.sqrt s.val : ℂ) - (Real.sqrt t : ℂ))‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact relative_sqrt_sub_bound (spectrum_nonneg_of_nonneg hpos s.property) ht (hb s hs hu)

theorem resolventComplementSqrt_local_error
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (hpos : 0 ≤ 1-R)
    (x : H) (l u : ℝ)
    (hlo : resolventLowerCut R l x = 0) (hhi : resolventLowerCut R u x = x)
    {t ε : ℝ} (ht : t < 1) (hε : 0 ≤ ε)
    (hspec : ∀ s : spectrum ℝ R, s.val ≤ 1)
    (hb : ∀ s : spectrum ℝ R, l ≤ s.val → s.val < u → |s.val-t| ≤ ε*(1-t)) :
    ‖CFC.sqrt (1-R) x - (Real.sqrt (1-t) : ℂ) • x‖ ≤ ε * Real.sqrt (1-t) * ‖x‖ := by
  let f : C(spectrum ℝ R, ℂ) :=
    resolventComplementSqrtFunction R - ContinuousMap.const _ (Real.sqrt (1-t) : ℂ)
  have he : resolventContinuousCalculus R hR f x =
      CFC.sqrt (1-R) x-(Real.sqrt (1-t) : ℂ) • x := by
    simp only [f, map_sub, resolventContinuousCalculus_complement_sqrt R hR hpos, sub_apply]
    congr 1
    have hc : ContinuousMap.const (spectrum ℝ R) (Real.sqrt (1-t) : ℂ) =
        (Real.sqrt (1-t) : ℂ) • (1 : C(spectrum ℝ R, ℂ)) := by ext; simp
    rw [hc, map_smul, map_one, smul_apply, one_apply_eq_self]
  rw [← he]
  apply resolventContinuousCalculus_local_bound R hR x l u hlo hhi f (by positivity)
  intro s hs hu
  change ‖((Real.sqrt (1-s.val) : ℂ) - (Real.sqrt (1-t) : ℂ))‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  apply relative_sqrt_sub_bound (sub_nonneg.mpr (hspec s)) (sub_pos.mpr ht)
  simpa only [show (1-s.val)-(1-t)= -(s.val-t) by ring, abs_neg] using hb s hs hu

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularLocalizedGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A localized vector gives an approximate modular graph pair

The error depends only on the width of the logarithmic interval. No bound
on its center is needed, and both graph coordinates approximate the same
original vector after their separate positive scalar normalizations.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_scaled_error {a ε : ℝ} (ha : 0 < a) (v x : H)
    (h : ‖v-(a : ℂ) • x‖ ≤ ε*a*‖x‖) :
    ‖((a : ℂ)⁻¹) • v-x‖ ≤ ε*‖x‖ := by
  have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have he : ((a : ℂ)⁻¹) • v-x = ((a : ℂ)⁻¹) • (v-(a : ℂ) • x) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hane, one_smul]
  rw [he, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  calc
    _ ≤ a⁻¹*(ε*a*‖x‖) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha.le)
    _ = ε*‖x‖ := by field_simp

variable {M : VonNeumannAlgebra H}

theorem modular_localized_graph_pair
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (ξ : H) {r δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : modularUpperCut M J Ω r ξ=ξ)
    (hhi : modularUpperCut M J Ω (r+δ) ξ=0) :
    ∃ (x y : H) (q : ℝ), 0 < q ∧
      (x,(q : ℂ) • y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph ∧
      ‖x-ξ‖ ≤ (Real.exp δ-1)*‖ξ‖ ∧ ‖y-ξ‖ ≤ (Real.exp δ-1)*‖ξ‖ := by
  let R := graphResolvent M J Ω 1
  let t := modularCutThreshold r
  let a := Real.sqrt t
  let b := Real.sqrt (1-t)
  have ht : 0 < t := modularCutThreshold_pos r
  have ht1 : t < 1 := modularCutThreshold_lt_one r
  have ha : 0 < a := Real.sqrt_pos.mpr ht
  have hb : 0 < b := Real.sqrt_pos.mpr (sub_pos.mpr ht1)
  have hε : 0 ≤ Real.exp δ-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hδ)
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hRpos : 0 ≤ R := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (graphResolvent_positive J Ω 1)
  have hRcomp : 0 ≤ 1-R := by
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    have hs := (tomitaGraphComplementRoot_nonneg (M := M) J Ω).isSelfAdjoint.star_eq
    simpa only [hs] using star_mul_self_nonneg (tomitaGraphComplementRoot (M := M) J Ω)
  have hroot : ‖tomitaGraphRoot (M := M) J Ω ξ-(a : ℂ) • ξ‖ ≤
      (Real.exp δ-1)*a*‖ξ‖ := by
    apply resolventSqrt_local_error R hR hRpos ξ
      (modularCutThreshold (r+δ)) t hhi hlo ht hε
    intro s hs hu
    exact (modularCutThreshold_relative_width hδ hs hu.le).1
  have hcomp : ‖tomitaGraphComplementRoot (M := M) J Ω ξ-(b : ℂ) • ξ‖ ≤
      (Real.exp δ-1)*b*‖ξ‖ := by
    apply resolventComplementSqrt_local_error R hR hRcomp ξ
      (modularCutThreshold (r+δ)) t hhi hlo ht1 hε
      (fun s => (graphResolvent_spectrum_bounds J Ω s.property).2)
    intro s hs hu
    exact (modularCutThreshold_relative_width hδ hs hu.le).2
  refine ⟨((a : ℂ)⁻¹) • tomitaGraphRoot (M := M) J Ω ξ,
    ((b : ℂ)⁻¹) • tomitaGraphComplementRoot (M := M) J Ω ξ,
    b/a, div_pos hb ha, ?_, norm_scaled_error ha _ ξ hroot, norm_scaled_error hb _ ξ hcomp⟩
  apply (modularPositiveOperator_graph_iff J Ω hsep hcyc _ _).mpr
  refine ⟨((a : ℂ)⁻¹) • ξ, ?_, ?_⟩
  · rw [map_smul]
  · rw [map_smul, smul_smul]
    congr 1
    rw [Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne', Complex.ofReal_ne_zero.mpr hb.ne']

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveGraphAlgebraicApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebraic approximation in the positive modular graph -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem positiveGraph_algebraic_approximate
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    {x y : H} (hxy : (x,y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : Algebra M, ‖a.val Ω-x‖ < ε ∧ ‖d.rightAction a Ω-y‖ < ε := by
  obtain ⟨z,hz,hz'⟩ := (modularPositiveOperator_graph_iff J Ω hsep hcyc x y).mp hxy
  have hg : (x,tomitaLinearPolarUnitary J Ω hsep hcyc y) ∈
      (tomitaClosedLinearOperator M J Ω 1).graph := by
    apply (tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc _ _).mpr
    exact ⟨z,hz,congrArg (tomitaLinearPolarUnitary J Ω hsep hcyc) hz'⟩
  obtain ⟨a,ha,hb⟩ := tomitaClosed_graph_approximate J Ω hsep hg hε
  refine ⟨a,ha,?_⟩
  have he : ‖d.rightAction a Ω-y‖ =
      ‖J (star a.val Ω)-tomitaLinearPolarUnitary J Ω hsep hcyc y‖ := by
    change ‖d.conjugation (star a.val (d.conjugation Ω))-y‖=_
    rw [d.fixes_vector,hd,tomitaLinearPolarUnitary_apply,← J.map_sub,J.norm_map]
    calc
      _ = ‖tomitaPolarConjugation J Ω hsep hcyc
          (star a.val Ω-tomitaPolarConjugation J Ω hsep hcyc y)‖ := by
        rw [map_sub,tomitaPolarConjugation_involutive]
      _ = _ := (tomitaPolarConjugation J Ω hsep hcyc).norm_map _
  rwa [he]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularLocalizedAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra elements approximating a short modular spectral vector -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem modular_localized_algebra_approximate_oai
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    (ξ : H) {r δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : modularUpperCut M J Ω r ξ=ξ)
    (hhi : modularUpperCut M J Ω (r+δ) ξ=0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : Algebra M) (q : ℝ), 0 < q ∧
      ‖a.val Ω-ξ‖ < (Real.exp δ-1)*‖ξ‖+ε ∧
      ‖((q : ℂ)⁻¹) • d.rightAction a Ω-ξ‖ < (Real.exp δ-1)*‖ξ‖+ε := by
  obtain ⟨x,y,q,hq,hgraph,hx,hy⟩ :=
    modular_localized_graph_pair J Ω hsep hcyc ξ hδ hlo hhi
  let tol := min ε (q*ε)
  have htol : 0 < tol := lt_min hε (mul_pos hq hε)
  obtain ⟨a,ha,hb⟩ := positiveGraph_algebraic_approximate J hsep hcyc d hd hgraph htol
  have hscaled : ‖((q : ℂ)⁻¹) • d.rightAction a Ω-y‖ < ε := by
    have hqne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    have he : ((q : ℂ)⁻¹) • d.rightAction a Ω-y =
        ((q : ℂ)⁻¹) • (d.rightAction a Ω-(q : ℂ) • y) := by
      rw [smul_sub,smul_smul,inv_mul_cancel₀ hqne,one_smul]
    rw [he,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]
    calc
      _ < q⁻¹*tol := mul_lt_mul_of_pos_left hb (inv_pos.mpr hq)
      _ ≤ q⁻¹*(q*ε) := mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_nonneg.mpr hq.le)
      _ = ε := by rw [← mul_assoc,inv_mul_cancel₀ hq.ne',one_mul]
  refine ⟨a,q,hq,?_,?_⟩
  · calc
      ‖a.val Ω-ξ‖ ≤ ‖a.val Ω-x‖+‖x-ξ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε+(Real.exp δ-1)*‖ξ‖ :=
        add_lt_add_of_lt_of_le (ha.trans_le (min_le_left _ _)) hx
      _ = _ := add_comm _ _
  · calc
      ‖((q : ℂ)⁻¹) • d.rightAction a Ω-ξ‖ ≤
          ‖((q : ℂ)⁻¹) • d.rightAction a Ω-y‖+‖y-ξ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε+(Real.exp δ-1)*‖ξ‖ := add_lt_add_of_lt_of_le hscaled hy
      _ = _ := add_comm _ _

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.modular_localized_algebra_approximate_oai.{u_1} := @OAI.KadisonKastler.modular_localized_algebra_approximate_oai.{u_1}
