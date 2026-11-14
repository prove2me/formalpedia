-- Prove2me | solution 1 for OAI.KadisonKastler.regularCore_fixed_corner_commute_translations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:14:36.919808+00:00
-- url     : https://prove2.me/submissions/dad80c4e-f9a7-4de8-81e0-22e112dcafe8

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Analysis.Normed.Operator.Mul
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
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
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
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K028

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCentralField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier fields of central elements in the actual regular core -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
  (P : VonNeumannAlgebra H)

omit [TopologicalSpace.SeparableSpace H] in
/-- Fixed operators have constant regular embeddings. -/
theorem regularCoreEmbedding_eq_constant_of_fixed (b : H →L[ℂ] H)
    (hfixed : ∀ s, unitaryConj (U s) b = b) :
    regularCoreEmbedding U hU b = regularConstantHom volume b := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreEmbedding_apply_ae U hU b f,
    regularConstantHom_apply_ae volume b f] with t h₁ h₂
  rw [h₁, h₂]
  have he : unitaryConj (star (U (Multiplicative.ofAdd t))) b = b := by
    rw [regularGroup_star_eq U t]
    exact hfixed _
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
    using congrArg (fun A : H →L[ℂ] H => A (f t)) he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreMonomials
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebraic generation by regular monomials

The core's algebraic generators reduce to finite linear combinations of
one original-algebra coefficient followed by one translation. This is
the dense algebra used to compute the frequency-window trace.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

theorem regularCore_generator_mem_monomials
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularCoreGenerators U hU M) :
    T ∈ regularCoreMonomials U hU M hM := by
  rcases hT with ⟨a, ha, rfl⟩ | ⟨s, rfl⟩
  · exact ⟨a, ha, 1, by simp [regularCoreMonomial]⟩
  · exact ⟨1, M.one_mem, s, by simp [regularCoreMonomial]⟩

theorem regularCore_generator_star_mem_monomials
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularCoreGenerators U hU M) :
    star T ∈ regularCoreMonomials U hU M hM := by
  apply regularCore_generator_mem_monomials U hU M hM
  rcases hT with ⟨a, ha, rfl⟩ | ⟨s, rfl⟩
  · exact Or.inl ⟨star a, M.star_mem' ha, (map_star (regularCoreEmbedding U hU) a)⟩
  · refine Or.inr ⟨s⁻¹, ?_⟩
    have he : regularRightTranslation (H := H) s⁻¹ = star (regularRightTranslation s) := by
      rw [map_inv, Unitary.star_eq_inv]
    exact congrArg Subtype.val he

theorem regularCore_adjoin_eq_span_monomials
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M) :
    (StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M)).toSubalgebra.toSubmodule =
      Submodule.span ℂ (regularCoreMonomials U hU M hM :
        Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) := by
  apply le_antisymm
  · rw [StarAlgebra.adjoin_eq_span]
    apply Submodule.span_mono
    change Submonoid.closure (regularCoreGenerators U hU M ∪
      star (regularCoreGenerators U hU M)) ≤ regularCoreMonomials U hU M hM
    apply Submonoid.closure_le.mpr
    intro T hT
    rcases hT with hT | hT
    · exact regularCore_generator_mem_monomials U hU M hM hT
    · have h := regularCore_generator_star_mem_monomials U hU M hM (Set.mem_star.mp hT)
      rcases h with ⟨a, ha, s, he⟩
      refine ⟨a, ha, s, ?_⟩
      simpa only [star_star] using he
  · apply Submodule.span_le.mpr
    rintro T ⟨a, ha, s, rfl⟩
    exact (StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M)).mul_mem
      (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, ha, rfl⟩))
      (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨s, rfl⟩))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreCornerCommutation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Translations commute with core corners on which the action is trivial -/

namespace KadisonKastler

open MeasureTheory Filter Generator.Tracial
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCore_compressed_commute_of_monomials
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H) (hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (p S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hm : ∀ a ∈ M, ∀ s, Commute (p * regularCoreMonomial U hU a s * p) S)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M) : Commute (p * T * p) S := by
  classical
  let A := StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M)
  have hsub : A.toSubalgebra.toSubmodule ≤ compressedCommutant p S := by
    rw [show A = StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M) from rfl,
      regularCore_adjoin_eq_span_monomials U hU M hn]
    apply Submodule.span_le.mpr
    rintro x ⟨a, ha, s, rfl⟩
    exact hm a ha s
  have ht : T ∈ Set.centralizer (Set.centralizer (A :
      Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))) := by
    change T ∈ (generatedVonNeumannAlgebra A :
      Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net A T ht
  apply ContinuousLinearMap.ext
  intro x
  have hl : Tendsto (fun i : Finset (RegularCoreHilbert H) × ℕ =>
      p ((a i).val (p (S x)))) atTop (𝓝 (p (T (p (S x))))) :=
    p.continuous.continuousAt.tendsto.comp (ha (p (S x)))
  have hr : Tendsto (fun i : Finset (RegularCoreHilbert H) × ℕ =>
      S (p ((a i).val (p x)))) atTop (𝓝 (S (p (T (p x))))) :=
    S.continuous.continuousAt.tendsto.comp
    (p.continuous.continuousAt.tendsto.comp (ha (p x)))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  exact Filter.Eventually.of_forall (fun i =>
    (congrArg (fun B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => B x)
      (hsub (a i).property).eq).symm)

theorem regularCore_fixed_corner_commute_translations_oai
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H) (hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (p : AlgebraProjection M)
    (hfix : ∀ t a, a ∈ M → unitaryConj (U t) (p.val.val * a * p.val.val) =
      p.val.val * a * p.val.val)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M) (s : Multiplicative ℝ) :
    Commute (regularCoreEmbedding U hU p.val.val * T * regularCoreEmbedding U hU p.val.val)
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hp : ∀ t, unitaryConj (U t) p.val.val = p.val.val := by
    intro t
    have h := hfix t 1 M.one_mem
    simpa only [mul_one, show p.val.val * p.val.val = p.val.val from
      congrArg Subtype.val p.property.isIdempotentElem.eq] using h
  have hpconst := regularCoreEmbedding_eq_constant_of_fixed U hU p.val.val hp
  apply regularCore_compressed_commute_of_monomials U hU M hn _ _ ?_ T hT
  intro a ha t
  have hpt : Commute (regularCoreEmbedding U hU p.val.val)
      (regularRightTranslation (H := H) t :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    rw [hpconst]
    exact regularConstant_commute_translation _ _
  have he : regularCoreEmbedding U hU p.val.val * regularCoreMonomial U hU a t *
      regularCoreEmbedding U hU p.val.val =
      regularConstantHom volume (p.val.val * a * p.val.val) *
        (regularRightTranslation (H := H) t :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    unfold regularCoreMonomial
    calc
      _ = (regularCoreEmbedding U hU p.val.val * regularCoreEmbedding U hU a *
          regularCoreEmbedding U hU p.val.val) *
          (regularRightTranslation (H := H) t :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
        simp only [mul_assoc]
        rw [hpt.symm.eq]
      _ = _ := by
        rw [← map_mul, ← map_mul, regularCoreEmbedding_eq_constant_of_fixed U hU _
          (fun t => hfix t a ha)]
  rw [he]
  apply (regularConstant_commute_translation _ s).mul_left
  change (regularRightTranslation (H := H) t :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
    (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      (regularRightTranslation (H := H) t :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  exact congrArg Subtype.val (show regularRightTranslation (H := H) t *
    regularRightTranslation s = regularRightTranslation s * regularRightTranslation t by
      rw [← map_mul, ← map_mul, mul_comm])

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.regularCore_fixed_corner_commute_translations_oai.{u_1} := @OAI.KadisonKastler.regularCore_fixed_corner_commute_translations_oai.{u_1}
