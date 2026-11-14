-- Prove2me | solution 1 for OAI.KadisonKastler.infDist_poisson_sandwich_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:08:33.418627+00:00
-- url     : https://prove2.me/submissions/82c7c9a2-3085-46cf-9d5a-cbe8963e62bc

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
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
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
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
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.RingTheory.Congruence.Basic
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
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K065
import Definitions.Def_Q260K032
import Theorems.Thm_OAI_KadisonKastler_probabilityOperatorIntegral_complete_commutant_bound

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Two-by-two C⋆-matrix norm formulas

The diagonal embedding is a faithful star representation, so its norm is
the supremum norm. Multiplying by the flip unitary gives the corresponding
off-diagonal formula.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Every individual entry is bounded by the operator norm, at any size. -/
theorem matrix_entry_norm_le {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) (i : m) (j : n) : ‖M i j‖ ≤ ‖M‖ :=
  CStarMatrix.norm_entry_le_norm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Complete bounds for the off-diagonal commutator construction

Reordering the two finite matrix indices turns an amplification of
`b ↦ [0,-b;b,0]` into the same off-diagonal matrix over a matrix algebra.
Its norm is therefore exactly the norm of the original amplification.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem norm_matrixBlockSwap (n : Type*) [Fintype n] [DecidableEq n]
    (X : CStarMatrix n n (CStarMatrix (Fin 2) (Fin 2) B)) :
    ‖matrixBlockSwap n X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (matrixBlockSwap n) (matrixBlockSwap n).injective X

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SquareCompleteBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rectangular complete bounds from square levels of size at least two -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Reindexing transports a bound at a finite ordinal to any finite square
matrix of the same size. -/
theorem norm_map_square_of_fin (F : A →ₗ[ℂ] B) {c : ℝ}
    (hsquare : ∀ n : ℕ, 2 ≤ n → ∀ X : CStarMatrix (Fin n) (Fin n) A,
      ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι)
    (X : CStarMatrix ι ι A) : ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖ := by
  let e := Fintype.equivFin ι
  let eA := CStarMatrix.reindexₐ ℂ A e
  let eB := CStarMatrix.reindexₐ ℂ B e
  have h := hsquare (Fintype.card ι) hι (eA X)
  have heq : CStarMatrix.mapₗ F (eA X) = eB (CStarMatrix.mapₗ F X) := rfl
  have hnA : ‖eA X‖ = ‖X‖ :=
    NonUnitalStarAlgHom.norm_map eA.toStarAlgHom eA.injective X
  have hnB : ‖eB (CStarMatrix.mapₗ F X)‖ = ‖CStarMatrix.mapₗ F X‖ :=
    NonUnitalStarAlgHom.norm_map eB.toStarAlgHom eB.injective (CStarMatrix.mapₗ F X)
  rw [heq, hnA, hnB] at h
  exact h

/-- Positive rectangular sizes embed isometrically into a square of size
at least two; zero rectangular sizes contribute only the zero matrix. -/
theorem completelyBoundedBy_of_large_square (F : A →ₗ[ℂ] B) {c : ℝ}
    (hsquare : ∀ n : ℕ, 2 ≤ n → ∀ X : CStarMatrix (Fin n) (Fin n) A,
      ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖) : CompletelyBoundedBy F c := by
  classical
  intro p q X
  by_cases hp : p = 0
  · subst p
    have hX : X = 0 := by ext i; exact Fin.elim0 i
    simp only [hX, map_zero, norm_zero, mul_zero, le_refl]
  by_cases hq : q = 0
  · subst q
    have hX : X = 0 := by ext i j; exact Fin.elim0 j
    simp only [hX, map_zero, norm_zero, mul_zero, le_refl]
  have hcard : 2 ≤ Fintype.card (Fin p ⊕ Fin q) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have h := norm_map_square_of_fin F hsquare hcard (rectangularCorner X)
  rw [← rectangularCorner_map, norm_rectangularCorner, norm_rectangularCorner] at h
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommutantDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap_apply _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutant distance in the presence of countable full matrix units

Finite matrix averaging and Cuntz amplification reduce the estimate to
the commutant-distance formula.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.matrixDistanceOperatorStarOrder
attribute [local instance] OAI.KadisonKastler.matrixDistanceSourceStarOrder
private theorem blockDiagonal_commutator (h a : H →L[ℂ] H) :
    innerDerivation (blockDiagonal h h) (blockDiagonal a a) =
      blockDiagonal (h * a - a * h) (h * a - a * h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [innerDerivation_apply, CStarMatrix.mul_apply,
      blockDiagonal, diagonalStarAlgHom_apply]

attribute [local instance] OAI.KadisonKastler.matrixDistanceOperatorOrder
attribute [local instance] OAI.KadisonKastler.matrixDistanceSourceOrder
theorem exists_commutant_approximation_of_complete_bound
    (M : VonNeumannAlgebra H)
    (hPublished : PublishedBlockCommutantApproximation (Algebra M) H)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : CompletelyBoundedBy
      ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) δ)
    (r : ℝ) (hr : δ / 2 < r) :
    ∃ k : H →L[ℂ] H, k ∈ M.commutant ∧ ‖h - k‖ < r := by
  let ρ := M.toStarSubalgebra.subtype
  let π := pairedRepresentation ρ ρ
  let T := blockDiagonal h h
  have hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) δ := by
    apply completelyBoundedBy_of_large_square
    intro n _ X
    have he : matrixBlockSwap (Fin n)
        (CStarMatrix.mapₗ ((innerDerivation T).comp π.toAlgHom.toLinearMap) X) =
        blockDiagonal
          (CStarMatrix.mapₗ ((innerDerivation h).comp ρ.toLinearMap) X)
          (CStarMatrix.mapₗ ((innerDerivation h).comp ρ.toLinearMap) X) := by
      have he' (x : Algebra M) : innerDerivation T (π x) =
          blockDiagonal (h * ρ x - ρ x * h) (h * ρ x - ρ x * h) := by
        rw [pairedRepresentation_apply]
        exact blockDiagonal_commutator h (ρ x)
      apply CStarMatrix.ext
      intro i j
      apply CStarMatrix.ext
      intro v w
      change innerDerivation T (π (X v w)) i j = _
      rw [he']
      fin_cases i <;> fin_cases j <;> rfl
    rw [← norm_matrixBlockSwap (Fin n), he, norm_blockDiagonal, max_self]
    exact hb n n X
  obtain ⟨D, hcomm, hnorm⟩ := hPublished π T δ hδ hcb r hr
  refine ⟨D 0 0, VonNeumannAlgebra.mem_commutant_iff.mpr ?_, ?_⟩
  · intro a ha
    have he := congrArg (fun X : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) => X 0 0)
      (hcomm ⟨a, ha⟩)
    simp only [π, pairedRepresentation_apply, CStarMatrix.mul_apply, Fin.sum_univ_two,
      blockDiagonal, diagonalStarAlgHom_apply] at he
    simpa [ρ] using he.symm
  · have he := matrix_entry_norm_le (D - T) 0 0
    change ‖D 0 0 - h‖ ≤ ‖D - T‖ at he
    rw [norm_sub_rev]
    exact he.trans_lt hnorm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProbabilityMatrixDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Distance to an algebra after vector integration

Diagonal amplification commutes with the actual vector integral. Applying
the published complete commutant-distance bound to the commutant gives
an algebra approximation without choosing measurable nearest points.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.matrixIntegralOrder
attribute [local instance] OAI.KadisonKastler.matrixIntegralStarOrder
attribute [local instance] OAI.KadisonKastler.integralSourceOrder
attribute [local instance] OAI.KadisonKastler.integralSourceStarOrder
/-- The published complete commutant-distance theorem supplies the needed
algebra distance after integration, without any measurable selection. -/
theorem exists_algebra_approximation_probabilityOperatorIntegral
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C)
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s ∂μ, ∃ b : H →L[ℂ] H, b ∈ M ∧ ‖F s - b‖ ≤ δ)
    (r : ℝ) (hr : δ < r) :
    ∃ b : H →L[ℂ] H, b ∈ M ∧
      ‖probabilityOperatorIntegral μ F hF C hC - b‖ < r := by
  obtain ⟨b, hb, hclose⟩ := exists_commutant_approximation_of_complete_bound M.commutant
    hDistance (probabilityOperatorIntegral μ F hF C hC) (mul_nonneg (by norm_num) hδ)
    (probabilityOperatorIntegral_complete_commutant_bound μ F hF C hC M hδ hnear)
    r (by linarith)
  exact ⟨b, by simpa only [VonNeumannAlgebra.commutant_commutant] using hb, hclose⟩

/-- Algebra distance is not increased by the vectorwise probability integral. -/
theorem infDist_probabilityOperatorIntegral_le
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C)
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s ∂μ, Metric.infDist (F s) (M : Set (H →L[ℂ] H)) ≤ δ) :
    Metric.infDist (probabilityOperatorIntegral μ F hF C hC)
      (M : Set (H →L[ℂ] H)) ≤ δ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hn : ∀ᵐ s ∂μ, ∃ b : H →L[ℂ] H, b ∈ M ∧ ‖F s - b‖ ≤ δ + ε / 2 := by
    filter_upwards [hnear] with s hs
    obtain ⟨b, hb, hFb⟩ := (Metric.infDist_lt_iff ⟨0, M.zero_mem⟩).mp
      (hs.trans_lt (show δ < δ + ε / 2 by linarith))
    exact ⟨b, hb, by simpa only [dist_eq_norm] using hFb.le⟩
  obtain ⟨b, hb, hFb⟩ := exists_algebra_approximation_probabilityOperatorIntegral
    μ F hF C hC M hDistance (by positivity : 0 ≤ δ + ε / 2) hn
    (δ + ε) (by linarith)
  exact (Metric.infDist_le_dist_of_mem hb).trans
    (by simpa only [dist_eq_norm] using hFb.le)

/-- The positive Poisson kernel retains an essential algebra-distance bound
at every point above the real axis. -/
theorem infDist_measurablePoissonAverage_le
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s, Metric.infDist (F s) (M : Set (H →L[ℂ] H)) ≤ δ)
    (t r : ℝ) (hr : 0 < r) :
    Metric.infDist (measurablePoissonAverage F hF C hC t r hr)
      (M : Set (H →L[ℂ] H)) ≤ δ :=
  infDist_probabilityOperatorIntegral_le _ F _ C _ M hDistance hδ
    ((cauchyMeasure_absolutelyContinuous t hr).ae_le hnear)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AnalyticAlgebraBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra errors of the demodulated analytic products

The Hardy product identity follows from evaluation and preservation of
the frequency nest. The resulting norm estimates pass from boundary
algebra distance to positive-height distance.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.analyticAlgebraStarOrder
omit [CompleteSpace H] in
/-- Perturbing both factors gives the boundary sandwich error. -/
theorem norm_sandwich_sub_of_contractions
    (a b u v x : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (ha : ‖a - u‖ ≤ δ) (hb : ‖b - v‖ ≤ δ) :
    ‖a * x * b - u * x * v‖ ≤ (2 * δ + δ ^ 2) * ‖x‖ := by
  have han : ‖a‖ ≤ 1 + δ := by
    have h := norm_sub_le_norm_sub_add_norm_sub a u (0 : H →L[ℂ] H)
    simp only [sub_zero] at h
    linarith
  have he : a * x * b - u * x * v = a * x * (b - v) + (a - u) * x * v := by
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖a * x * (b - v)‖ + ‖(a - u) * x * v‖ := norm_add_le _ _
    _ ≤ (‖a‖ * ‖x‖) * ‖b - v‖ + (‖a - u‖ * ‖x‖) * ‖v‖ := add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ ≤ ((1 + δ) * ‖x‖) * δ + (δ * ‖x‖) * 1 := add_le_add
      (mul_le_mul (mul_le_mul_of_nonneg_right han (norm_nonneg _)) hb
        (norm_nonneg _) (by positivity))
      (mul_le_mul (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hv
        (norm_nonneg _) (by positivity))
    _ = _ := by ring

attribute [local instance] OAI.KadisonKastler.analyticAlgebraOrder
/-- The actual Poisson average of a product inherits its boundary algebra
error. This is the step for which no measurable nearest points are chosen. -/
theorem infDist_poisson_sandwich_le_oai
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun s => B s ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun s => S s ξ) volume)
    {CB CS : ℝ} (hCB : 0 ≤ CB)
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    {δ e : ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (x : H →L[ℂ] H)
    (hnear : ∀ᵐ s, Metric.infDist (U s * x * V s) (M : Set (H →L[ℂ] H)) ≤ e * ‖x‖)
    (t r : ℝ) (hr : 0 < r) :
    Metric.infDist
      (measurablePoissonAverage (fun s => B s * x * S s)
        (sandwich_vector_measurable B S hB hS x) (CB * ‖x‖ * CS)
        (ae_norm_sandwich_le B S hCB hb hs x) t r hr)
      (M : Set (H →L[ℂ] H)) ≤ (e + 2 * δ + δ ^ 2) * ‖x‖ := by
  apply infDist_measurablePoissonAverage_le _ _ _ _ M hDistance (by positivity)
  filter_upwards [hnear, hu, hv, hBU, hSV] with s hn hu hv hBU hSV
  have h := Metric.infDist_le_infDist_add_dist
    (x := B s * x * S s) (y := U s * x * V s) (s := (M : Set (H →L[ℂ] H)))
  rw [dist_eq_norm] at h
  exact (h.trans (add_le_add hn
    (norm_sandwich_sub_of_contractions _ _ _ _ x hδ hu hv hBU hSV))).trans_eq (by ring)

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.infDist_poisson_sandwich_le_oai.{u} := @OAI.KadisonKastler.infDist_poisson_sandwich_le_oai.{u}
