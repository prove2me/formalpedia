-- Prove2me | solution 1 for OAI.KadisonKastler.matrixTraceRetraction_eq_expectation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:01:09.782331+00:00
-- url     : https://prove2.me/submissions/828d7f87-90ca-4189-a6f7-15789e230dbd

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
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
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
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
import Definitions.Def_Q260K068

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalCyclicExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Explicit retractions through a minimal cyclic space

The compression proof of type-I injectivity gives a specific contractive
retraction. Its coefficients on the minimal cyclic space agree with the
original ambient operator. These identities allow the trace-preserving
finite-stage construction to retain the original vector state.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (N : VonNeumannAlgebra H) (hN : ScalarCenter N)
  (p : AlgebraProjection N) (hp : IsMinimalProjectionIn N p)
  (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)

/-- Compression preserves every coefficient with both vectors in the cyclic space. -/
theorem minimalCyclicRetraction_coefficient (T : H →L[ℂ] H)
    (x y : typeICyclicSpace N ξ) :
    inner ℂ y.val ((minimalCyclicRetraction N hN p hp ξ hξ hpξ T).val x.val) =
      inner ℂ y.val (T x.val) := by
  have h := congrArg (fun A : typeICyclicSpace N ξ →L[ℂ] typeICyclicSpace N ξ =>
    inner ℂ y (A x)) (minimalCyclicRetraction_compression N hN p hp ξ hξ hpξ T)
  change inner ℂ y.val ((minimalCyclicRetraction N hN p hp ξ hξ hpξ T).val x.val) =
    inner ℂ y (cornerCompression (typeICyclicSpace N ξ) T x) at h
  simpa only [cornerCompression_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using h

/-- The compression retraction respects left multiplication from its range. -/
theorem minimalCyclicRetraction_mul_left (a : Algebra N) (T : H →L[ℂ] H) :
    minimalCyclicRetraction N hN p hp ξ hξ hpξ (a.val * T) =
      a * minimalCyclicRetraction N hN p hp ξ hξ hpξ T := by
  apply (typeICyclicEquiv hN p hp ξ hξ hpξ).injective
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y.val
    ((minimalCyclicRetraction N hN p hp ξ hξ hpξ (a.val * T)).val x.val) =
      inner ℂ y.val (a.val ((minimalCyclicRetraction N hN p hp ξ hξ hpξ T).val x.val))
  rw [minimalCyclicRetraction_coefficient]
  let y' : typeICyclicSpace N ξ :=
    ⟨(star a).val y.val, vectorOrbitClosure_invariant _ _ (star a) y.property⟩
  have h := minimalCyclicRetraction_coefficient N hN p hp ξ hξ hpξ T x y'
  change inner ℂ (star a.val y.val)
    ((minimalCyclicRetraction N hN p hp ξ hξ hpξ T).val x.val) =
      inner ℂ (star a.val y.val) (T x.val) at h
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, mul_apply_eq_comp] using h.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixTraceRetraction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Trace-preserving ambient retractions onto finite matrix algebras

The minimal cyclic space is based at a diagonal matrix unit applied to the
original trace vector. The matrix columns then recover the original trace.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (τ : TracialRepresentation M) (E : MatrixUnitSystem ι (Algebra M)) (o : ι)

omit [Nontrivial H] [Nonempty ι] in
/-- A matrix-column resolution of the faithful vector trace. -/
theorem matrixColumn_trace (T : Algebra M) :
    (∑ i, inner ℂ ((E.entry i o).val τ.vector)
      (T.val ((E.entry i o).val τ.vector))) = τ.trace T := by
  have hterm (i : ι) :
      inner ℂ ((E.entry i o).val τ.vector) (T.val ((E.entry i o).val τ.vector)) =
        τ.trace (T * E.entry i i) := by
    change inner ℂ (baseVector τ (E.entry i o))
      (baseVector τ (T * E.entry i o)) = _
    rw [baseVector_inner_trace, τ.trace_mul_comm, mul_assoc, E.star_entry,
      E.mul_entry, ite_eq_left rfl]
  simp_rw [hterm]
  change (∑ i, coordinateTraceLinear τ (T * E.entry i i)) = _
  rw [← map_sum, ← Finset.mul_sum, E.total, mul_one]
  rfl

omit [Nontrivial H] [Nonempty ι] in
/-- Every matrix column belongs to this minimal cyclic space. -/
theorem matrixColumn_mem (i : ι) :
    (E.entry i o).val τ.vector ∈
      typeICyclicSpace (matrixUnitConcreteAlgebra E) ((E.entry o o).val τ.vector) := by
  have h := vectorOrbitClosure_invariant (matrixUnitConcreteAlgebra E).toStarSubalgebra
    ((E.entry o o).val τ.vector) ((concreteMatrixUnits E).entry i o)
    (mem_vectorOrbitClosure _ _)
  have he : (E.entry i o).val ((E.entry o o).val τ.vector) =
      (E.entry i o).val τ.vector := by
    have hm := congrArg (fun a : Algebra M => a.val τ.vector) (E.mul_entry i o o o)
    simpa only [ite_true, if_true, MulMemClass.coe_mul, mul_apply_eq_comp] using hm
  change (E.entry i o).val ((E.entry o o).val τ.vector) ∈ _ at h
  rwa [he] at h

/-- Compression preserves the original trace on the ambient finite algebra. -/
theorem matrixTraceRetraction_trace (T : Algebra M) :
    τ.trace (coordinateInclusion E.concreteAlgebra_le (matrixTraceRetraction τ E o T.val)) =
      τ.trace T := by
  rw [← matrixColumn_trace τ E o]
  rw [← matrixColumn_trace τ E o T]
  apply Finset.sum_congr rfl
  intro i _
  exact minimalCyclicRetraction_coefficient _ _ _ _ _ _ _ T.val
    ⟨(E.entry i o).val τ.vector, matrixColumn_mem τ E o i⟩
    ⟨(E.entry i o).val τ.vector, matrixColumn_mem τ E o i⟩

/-- The finite-stage retraction is a left module map over the matrix algebra. -/
theorem matrixTraceRetraction_mul_left
    (a : Algebra (matrixUnitConcreteAlgebra E)) (T : H →L[ℂ] H) :
    matrixTraceRetraction τ E o (a.val * T) = a * matrixTraceRetraction τ E o T :=
  minimalCyclicRetraction_mul_left _ _ _ _ _ _ _ a T

/-- On the finite ambient algebra this is the trace conditional expectation. -/
theorem matrixTraceRetraction_eq_expectation_oai (T : Algebra M) :
    conditionalExpectation τ (matrixUnitConcreteAlgebra_le E) T =
      coordinateInclusion E.concreteAlgebra_le (matrixTraceRetraction τ E o T.val) := by
  apply conditionalExpectation_eq_of_orthogonal
  · exact (matrixTraceRetraction τ E o T.val).property
  · intro b
    let bN : Algebra (matrixUnitConcreteAlgebra E) := ⟨b.val.val, b.property⟩
    have hb : coordinateInclusion E.concreteAlgebra_le bN = b.val := rfl
    have h := matrixTraceRetraction_trace τ E o (b.val * T)
    change τ.trace (coordinateInclusion E.concreteAlgebra_le
      (matrixTraceRetraction τ E o (bN.val * T.val))) = τ.trace (b.val * T) at h
    rw [matrixTraceRetraction_mul_left, map_mul, hb] at h
    change τ.trace (b.val * (T - coordinateInclusion E.concreteAlgebra_le
      (matrixTraceRetraction τ E o T.val))) = 0
    rw [mul_sub, trace_sub, h, sub_self]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.matrixTraceRetraction_eq_expectation_oai.{u_1, u_2} := @OAI.KadisonKastler.matrixTraceRetraction_eq_expectation_oai.{u_1, u_2}
