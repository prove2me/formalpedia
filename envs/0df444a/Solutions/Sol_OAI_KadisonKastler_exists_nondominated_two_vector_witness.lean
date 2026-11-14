-- Prove2me | solution 1 for OAI.KadisonKastler.exists_nondominated_two_vector_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:56.181643+00:00
-- url     : https://prove2.me/submissions/ea0e29c8-999b-4bb6-995a-aa42ae620af8

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K029
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_exists_projection_large_vector_ratio
import Theorems.Thm_OAI_KadisonKastler_projection_equivalent_one_of_not_finite

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Matrices of orthogonal projections

The preservation-cut estimate uses an operator matrix whose nonzero
entries are projections, orthogonal within each row and each column.
Such a rectangular matrix is a contraction.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inner_eq_zero_of_selfAdjoint_mul_eq_zero
    (P Q : H →L[ℂ] H) (hP : IsSelfAdjoint P) (hPQ : P * Q = 0) (x y : H) :
    inner ℂ (P x) (Q y) = 0 := by
  have hstar : P.adjoint = P := hP.star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right, hstar]
  have hz : P (Q y) = 0 := by
    change (P * Q) y = 0
    rw [hPQ]
    rfl
  rw [hz, inner_zero_right]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorSupportProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The support projection of a represented vector state

The support is the projection onto the closed commutant orbit. The orbit
construction proves its minimality and faithfulness on the supported corner.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An operator killing the vector kills its supported corner. -/
theorem mul_vectorSupport_eq_zero (M : VonNeumannAlgebra H) (ξ : H)
    (a : Algebra M) (ha : a.val ξ = 0) :
    a.val * (vectorSupportProjection M ξ).val.val = 0 := by
  have hker : vectorOrbitClosure M.commutant.toStarSubalgebra ξ ≤ a.val.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro y ⟨b,rfl⟩
      change a.val (b.val ξ) = 0
      have hc := congrArg (fun T : H →L[ℂ] H => T ξ)
        (VonNeumannAlgebra.mem_commutant_iff.mp b.property a.val a.property)
      change a.val (b.val ξ) = b.val (a.val ξ) at hc
      rw [hc,ha,map_zero]
    · exact a.val.isClosed_ker
  ext η
  exact hker (Submodule.starProjection_apply_mem _ η)

theorem vectorSupport_faithful_corner (M : VonNeumannAlgebra H) (ξ : H)
    (a : Algebra M) (ha : a.val * (vectorSupportProjection M ξ).val.val = a.val)
    (hξ : a.val ξ = 0) : a = 0 := by
  apply Subtype.ext
  exact ha.symm.trans (mul_vectorSupport_eq_zero M ξ a hξ)

/-- A projection fixing the vector dominates its support. -/
theorem vectorSupport_minimal (M : VonNeumannAlgebra H) (ξ : H)
    (p : AlgebraProjection M) (hp : p.val.val ξ = ξ) :
    (vectorSupportProjection M ξ).val.val * p.val.val =
      (vectorSupportProjection M ξ).val.val := by
  have h := mul_vectorSupport_eq_zero M ξ (1 - p.val) (by
    change ξ - p.val.val ξ = 0
    rw [hp,sub_self])
  change (1 - p.val.val) * (vectorSupportProjection M ξ).val.val = 0 at h
  rw [sub_mul,one_mul,sub_eq_zero] at h
  have hs := congrArg star h
  have hpstar : star p.val.val = p.val.val :=
    congrArg (fun a : Algebra M => a.val) p.property.isSelfAdjoint.star_eq
  have hqstar : star (vectorSupportProjection M ξ).val.val =
      (vectorSupportProjection M ξ).val.val :=
    congrArg (fun a : Algebra M => a.val)
      (vectorSupportProjection M ξ).property.isSelfAdjoint.star_eq
  simpa only [star_mul, hpstar, hqstar] using hs.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerStateWeights
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalized corner states of faithful vector states

The weights of a proper nonzero projection lie strictly between zero and
one. The two normalized compressions have norm at most one and reconstruct
a state centralizing the projection with exactly those scalar weights.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vectorFunctional_projection (p : AlgebraProjection M) (ξ : H) :
    vectorFunctional ξ p.val = (projectionVectorWeight p ξ : ℂ) := by
  have hp := congrArg (fun a : Algebra M => a.val ξ) p.property.isIdempotentElem.eq
  change p.val.val (p.val.val ξ) = p.val.val ξ at hp
  have hs : p.val.val.adjoint = p.val.val :=
    (p.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
  change inner ℂ ξ (p.val.val ξ) = (‖p.val.val ξ‖^2 : ℝ)
  calc
    _ = inner ℂ ξ (p.val.val (p.val.val ξ)) := by rw [hp]
    _ = inner ℂ (p.val.val ξ) (p.val.val ξ) := by
      simpa only [hs] using p.val.val.adjoint_inner_right ξ (p.val.val ξ)
    _ = _ := by
      rw [inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow]
      rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIPrescribedRank
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prescribed finite matrix ranks for type III projections

Every nonzero projection splits into any positive finite number of
nonzero pieces. Consequently a nontrivial projection can occupy either
chosen positive block size in a unital full matrix algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_proper_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧ q.val ≠ p.val := by
  have hn : ¬ FiniteProjectionIn M p.val := fun h => hp (hM.purelyInfinite p.val p.property h)
  simp only [FiniteProjectionIn] at hn
  push Not at hn
  obtain ⟨v,hv,hpv,hproper⟩ := hn
  let w : PartialIsometry M := ⟨p,v,hv⟩
  refine ⟨w.target,?_,?_,hproper⟩
  · change p.val * (v * star v) = v * star v
    rw [← mul_assoc,hpv]
  · intro hz
    have hv0 : v = 0 := by
      have he := w.target_mul
      change (v * star v) * v = v at he
      rw [show v * star v = 0 from hz,zero_mul] at he
      exact he.symm
    apply hp
    rw [← hv,hv0,star_zero,zero_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SmallVectorSubprojection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Small positive vector-state cuts in type III algebras

Restricting to the vector support makes every nonzero subprojection have
positive weight. Repeated proper splitting then makes that weight small.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vector_projection_sub_weight (p q : AlgebraProjection M) (hqp : q ≤ p) (η : H) :
    ‖q.val.val η‖^2+‖(p.val-q.val).val η‖^2=‖p.val.val η‖^2 := by
  have hzero : q.val*(p.val-q.val)=0 := by
    rw [mul_sub,projection_mul_of_le hqp,q.property.isIdempotentElem.eq,sub_self]
  have horth : inner ℂ (q.val.val η) ((p.val-q.val).val η)=0 :=
    inner_eq_zero_of_selfAdjoint_mul_eq_zero _ _
      (q.property.map M.toStarSubalgebra.subtype).isSelfAdjoint
      (congrArg Subtype.val hzero) η η
  have he := norm_add_sq (𝕜 := ℂ) (q.val.val η) ((p.val-q.val).val η)
  have hv : q.val.val η+(p.val-q.val).val η=p.val.val η := by
    change q.val.val η+(p.val.val η-q.val.val η)=p.val.val η
    abel
  rw [horth,map_zero,mul_zero,add_zero,hv] at he
  exact he.symm

theorem TypeIIIFactor.exists_half_vector_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (η : H) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧ ‖q.val.val η‖^2 ≤ ‖p.val.val η‖^2/2 := by
  obtain ⟨q,hqp,hq0,hqne⟩ := hM.exists_proper_subprojection p hp
  by_cases hh : ‖q.val.val η‖^2 ≤ ‖p.val.val η‖^2/2
  · exact ⟨q,hqp,hq0,hh⟩
  · let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hqp⟩
    have hrp : r ≤ p := by
      change p.val*(p.val-q.val)=p.val-q.val
      rw [mul_sub,p.property.isIdempotentElem.eq,hqp]
    refine ⟨r,hrp,?_,?_⟩
    · exact sub_ne_zero.mpr (Ne.symm hqne)
    · have he := vector_projection_sub_weight p q hqp η
      change ‖(p.val-q.val).val η‖^2 ≤ _
      linarith

theorem TypeIIIFactor.exists_geometric_vector_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (η : H) (n : ℕ) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧
      ‖q.val.val η‖^2 ≤ (1/2 : ℝ)^n*‖p.val.val η‖^2 := by
  induction n with
  | zero => exact ⟨p,le_rfl,hp,by simp⟩
  | succ n ih =>
    obtain ⟨q,hqp,hq0,hqw⟩ := ih
    obtain ⟨r,hrq,hr0,hrw⟩ := hM.exists_half_vector_subprojection q hq0 η
    refine ⟨r,hrq.trans hqp,hr0,?_⟩
    calc
      _ ≤ ‖q.val.val η‖^2/2 := hrw
      _ ≤ ((1/2 : ℝ)^n*‖p.val.val η‖^2)/2 := div_le_div_of_nonneg_right hqw (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem TypeIIIFactor.exists_small_positive_vector_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (η : H) (hp : 0 < ‖p.val.val η‖^2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ 0 < ‖q.val.val η‖^2 ∧ ‖q.val.val η‖^2 < ε := by
  let ζ := p.val.val η
  let e := vectorSupportProjection M ζ
  have hep : e ≤ p := by
    have he := vectorSupport_minimal M ζ p (by
      change p.val.val (p.val.val η)=p.val.val η
      exact congrArg (fun a : Algebra M => a.val η) p.property.isIdempotentElem.eq)
    have hs := congrArg star he
    have hes := (e.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
    have hps := (p.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
    change star e.val.val=e.val.val at hes
    change star p.val.val=p.val.val at hps
    apply Subtype.ext
    change p.val.val*e.val.val=e.val.val
    change star (e.val.val*p.val.val)=star e.val.val at hs
    rw [star_mul,hps,hes] at hs
    exact hs
  have he0 : e.val ≠ 0 := by
    intro hz
    have he := vectorSupportProjection_apply M ζ
    change e.val.val ζ=ζ at he
    rw [hz] at he
    have hζ : ζ=0 := by simpa using he.symm
    change 0 < ‖ζ‖^2 at hp
    simp [hζ] at hp
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n*‖e.val.val η‖^2) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).mul_const (‖e.val.val η‖^2)
  obtain ⟨n,hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  obtain ⟨q,hqe,hq0,hqw⟩ := hM.exists_geometric_vector_subprojection e he0 η n
  have hqp := hqe.trans hep
  refine ⟨q,hqp,?_,hqw.trans_lt hn⟩
  apply sq_pos_of_ne_zero
  intro hz
  have hqη : q.val.val η=0 := norm_eq_zero.mp hz
  apply hq0
  apply vectorSupport_faithful_corner M ζ q.val
  · exact congrArg Subtype.val (projection_mul_of_le hqe)
  · change q.val.val (p.val.val η)=0
    have he := congrArg (fun a : Algebra M => a.val η) (projection_mul_of_le hqp)
    exact he.trans hqη

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartialIsometryVectorEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vector energy of a partial isometry and its central defect -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem partialIsometry_vector_norm_sq (v : PartialIsometry M) (ξ : H) :
    ‖v.val.val ξ‖^2=‖v.support.val.val ξ‖^2 := by
  have he := congrArg Complex.re (vectorFunctional_projection v.support ξ)
  rw [← v.initial] at he
  change (inner ℂ ξ (v.val.val.adjoint (v.val.val ξ))).re=‖v.support.val.val ξ‖^2 at he
  rw [ContinuousLinearMap.adjoint_inner_right] at he
  change RCLike.re (inner ℂ (v.val.val ξ) (v.val.val ξ))=_ at he
  rwa [inner_self_eq_norm_sq] at he

theorem partialIsometry_right_vector_norm_sq (J : H ≃ₗᵢ⋆[ℂ] H)
    (v : PartialIsometry M) (ξ : H) (hξ : J ξ=ξ) :
    ‖conjugationOperator J (star v.val.val) ξ‖^2=‖v.target.val.val ξ‖^2 := by
  rw [conjugationOperator_apply,hξ,J.norm_map]
  exact partialIsometry_vector_norm_sq v.adjoint ξ

theorem partialIsometry_central_defect_upper (J : H ≃ₗᵢ⋆[ℂ] H)
    (v : PartialIsometry M) (ξ : H) (hξ : J ξ=ξ) :
    ‖centralVectorDefect J ξ v.val.val‖^2 ≤
      2*(‖v.support.val.val ξ‖^2+‖v.target.val.val ξ‖^2) := by
  have hn := norm_sub_le (v.val.val ξ) (conjugationOperator J (star v.val.val) ξ)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  have hp := partialIsometry_vector_norm_sq v ξ
  have hq := partialIsometry_right_vector_norm_sq J v ξ hξ
  change ‖centralVectorDefect J ξ v.val.val‖ ≤ _ at hn
  change ‖centralVectorDefect J ξ v.val.val‖^2 ≤ _ at hs
  nlinarith [sq_nonneg (‖v.val.val ξ‖-‖conjugationOperator J (star v.val.val) ξ‖)]

theorem partialIsometry_central_defect_lower (J : H ≃ₗᵢ⋆[ℂ] H)
    (v : PartialIsometry M) (p q : AlgebraProjection M)
    (hsupport : v.support.val=p.val-q.val) (htarget : v.target=q)
    (hqp : q ≤ p) (η : H) (hη : J η=η)
    (hsmall : ‖q.val.val η‖^2 < ‖p.val.val η‖^2/16) :
    ‖p.val.val η‖^2/4 < ‖centralVectorDefect J η v.val.val‖^2 := by
  let A := ‖v.val.val η‖
  let B := ‖conjugationOperator J (star v.val.val) η‖
  let D := ‖centralVectorDefect J η v.val.val‖
  have ha : A^2=‖(p.val-q.val).val η‖^2 := by
    exact (partialIsometry_vector_norm_sq v η).trans (congrArg (fun a : Algebra M => ‖a.val η‖^2) hsupport)
  have hb : B^2=‖q.val.val η‖^2 := by
    exact (partialIsometry_right_vector_norm_sq J v η hη).trans (congrArg (fun r : AlgebraProjection M => ‖r.val.val η‖^2) htarget)
  have htotal : A^2+B^2=‖p.val.val η‖^2 := by
    rw [ha,hb,add_comm]
    exact vector_projection_sub_weight p q hqp η
  have hn : A ≤ D+B := by
    calc
      _ = ‖(v.val.val η-conjugationOperator J (star v.val.val) η)+
          conjugationOperator J (star v.val.val) η‖ := by
        dsimp only [A]
        congr 1
        abel
      _ ≤ _ := norm_add_le _ _
  have hs := (sq_le_sq₀ (show 0 ≤ A from norm_nonneg _) (show 0 ≤ D+B by positivity)).mpr hn
  change ‖p.val.val η‖^2/4 < D^2
  nlinarith [sq_nonneg (D-B),sq_nonneg ‖p.val.val η‖]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NondominatedVectorWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Two-vector witnesses when the test state is not dominated

A small positive cut of a projection of large relative state weight is
equivalent to its complement in the type III factor. The resulting partial
isometry has large test displacement and small reference displacement.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem exists_nondominated_two_vector_witness_oai (hM : TypeIIIFactor M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (hξ : J ξ=ξ) (hη : J η=η)
    (hnot : ¬ ∃ C : ℝ, ∀ a : Algebra M, ‖a.val η‖ ≤ C*‖a.val ξ‖)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ a : Algebra M, ‖a.val ξ‖+‖a.val η‖ < 12*‖centralVectorDefect J η a.val‖ ∧
      ‖centralVectorDefect J ξ a.val‖ < γ*‖centralVectorDefect J η a.val‖ := by
  let R := 16/γ^2+1
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hR₁ : 1 ≤ R := by
    dsimp [R]
    have he : 0 ≤ 16/γ^2 := by positivity
    linarith
  obtain ⟨p,hp⟩ := exists_projection_large_vector_ratio ξ η hnot R hR.le
  have hpη : 0 < ‖p.val.val η‖^2 := lt_of_le_of_lt
    (mul_nonneg hR.le (sq_nonneg _)) hp
  obtain ⟨q,hqp,hqη,hqsmall⟩ := hM.exists_small_positive_vector_subprojection p η hpη
    (show 0 < ‖p.val.val η‖^2/16 by positivity)
  let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hqp⟩
  have hweights (ζ : H) : ‖q.val.val ζ‖^2+‖r.val.val ζ‖^2=‖p.val.val ζ‖^2 :=
    vector_projection_sub_weight p q hqp ζ
  have hq0 : q.val ≠ 0 := by
    intro hz
    have hzv : q.val.val=0 := congrArg Subtype.val hz
    have he : (0 : ℝ) < 0 := by
      simpa only [hzv,zero_apply,norm_zero,pow_two,mul_zero] using hqη
    exact (lt_irrefl 0) he
  have hr0 : r.val ≠ 0 := by
    intro hz
    have hzv : r.val.val=0 := congrArg Subtype.val hz
    have hh := hweights η
    simp only [hzv,zero_apply,norm_zero,pow_two,mul_zero,add_zero] at hh
    nlinarith only [hpη,hqsmall,hh]
  have hr1 : r.Equivalent (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    projection_equivalent_one_of_not_finite hM.factor r
      (fun hf => hr0 (hM.purelyInfinite r.val r.property hf))
  have hq1 : q.Equivalent (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    projection_equivalent_one_of_not_finite hM.factor q
      (fun hf => hq0 (hM.purelyInfinite q.val q.property hf))
  obtain ⟨v,hvs,hvt⟩ := AlgebraProjection.equivalent_trans hr1
    (AlgebraProjection.equivalent_symm hq1)
  have hvnorm (ζ : H) : ‖v.val.val ζ‖^2=‖r.val.val ζ‖^2 := by
    rw [partialIsometry_vector_norm_sq,hvs]
  have hgap : ‖p.val.val η‖^2/4 < ‖centralVectorDefect J η v.val.val‖^2 :=
    partialIsometry_central_defect_lower J v p q (congrArg Subtype.val hvs) hvt hqp η hη hqsmall
  have hcent : ‖centralVectorDefect J ξ v.val.val‖^2 ≤ 2*‖p.val.val ξ‖^2 := by
    have he := partialIsometry_central_defect_upper J v ξ hξ
    rw [hvs,hvt] at he
    have hw := hweights ξ
    nlinarith only [he,hw]
  have hpξ : ‖p.val.val ξ‖^2 < ‖p.val.val η‖^2 := by
    exact (le_mul_of_one_le_left (sq_nonneg _) hR₁).trans_lt hp
  have hsum : (‖v.val.val ξ‖+‖v.val.val η‖)^2 <
      16*‖centralVectorDefect J η v.val.val‖^2 := by
    have hξw := hweights ξ
    have hηw := hweights η
    have hvξ := hvnorm ξ
    have hvη := hvnorm η
    nlinarith only [hξw,hηw,hvξ,hvη,hpξ,hgap,
      sq_nonneg (‖v.val.val ξ‖-‖v.val.val η‖),sq_nonneg ‖q.val.val ξ‖,
      sq_nonneg ‖q.val.val η‖]
  have hD : 0 < ‖centralVectorDefect J η v.val.val‖ := by
    nlinarith only [hgap,hpη,norm_nonneg (centralVectorDefect J η v.val.val)]
  have hsum' : ‖v.val.val ξ‖+‖v.val.val η‖ <
      4*‖centralVectorDefect J η v.val.val‖ := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [hsum]
  have hRval : γ^2*R=16+γ^2 := by
    dsimp [R]
    field_simp
  have hratio : 16*‖p.val.val ξ‖^2 < γ^2*‖p.val.val η‖^2 := by
    have he := mul_lt_mul_of_pos_left hp (sq_pos_of_pos hγ)
    rw [← mul_assoc,hRval] at he
    nlinarith only [he,mul_nonneg (sq_nonneg γ) (sq_nonneg ‖p.val.val ξ‖)]
  have hgapγ := mul_lt_mul_of_pos_left hgap (sq_pos_of_pos hγ)
  refine ⟨v.val,by linarith,?_⟩
  apply (sq_lt_sq₀ (norm_nonneg _) (mul_nonneg hγ.le hD.le)).mp
  rw [mul_pow]
  nlinarith only [hcent,hratio,hgapγ]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_nondominated_two_vector_witness_oai.{u_1} := @OAI.KadisonKastler.exists_nondominated_two_vector_witness_oai.{u_1}
