-- Prove2me | solution 1 for OAI.KadisonKastler.FullMatrixCorner.exists_commutant_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:11:35.247983+00:00
-- url     : https://prove2.me/submissions/c05761a7-89a4-4a7c-b70a-c5704f4953b0

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
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
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K065

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
-- module Solutions.OAIQ075_KS.KadisonKastler_CuntzMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix amplification using common isometries

A finite Cuntz family gives an actual star equivalence between the ambient
operator algebra and its matrix amplification. If its isometries belong to
two concrete algebras, the same equivalence identifies both matrix unit
balls with their original unit balls.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H n : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype n] [DecidableEq n]

namespace CuntzFamily

attribute [local instance] OAI.KadisonKastler.CuntzFamily.instStarOrderedRingContinuousLinearMapComplexId
variable (S : CuntzFamily n H)

theorem assemble_mem (M : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ M)
    (X : CStarMatrix n n (H →L[ℂ] H)) (hX : ∀ i j, X i j ∈ M) : S.assemble X ∈ M := by
  exact M.sum_mem fun i _ => M.sum_mem fun j _ =>
    M.mul_mem (M.mul_mem (hS i) (hX i j)) (M.toStarSubalgebra.star_mem' (hS j))

end CuntzFamily

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerCuntzFamily
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common isometries from countable matrix units

Regrouping the countably many matrix summands gives the finite Cuntz
families used to identify matrix unit balls with ordinary unit balls.
The isometries belong to every von Neumann algebra containing the matrix
units, by their explicit strong-sum formula.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

variable {n : Type*} (e : n × ℕ ≃ ℕ)

variable [DecidableEq n]

variable [Fintype n]

omit [Fintype n] [DecidableEq n] in
theorem regroupingOperator_mem (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i : n) : F.regroupingOperator e i ∈ M := by
  let a (s : Finset ℕ) : Algebra M :=
    ⟨∑ k ∈ s, F.entry (e (i, k)) k, M.sum_mem fun k _ => hM _ _⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) M a
  intro x y
  have he (s : Finset ℕ) :
      (a s : H →L[ℂ] H) x = F.regroupingOperator e i (F.partialDiagonal s x) := by
    simp only [a, partialDiagonal, sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [F.diagonal_apply, F.regroupingOperator_column]
    change F.entry (e (i, k)) k x =
      (F.entry (e (i, k)) 0 * E.starProjection * F.entry 0 k) x
    rw [← F.zero_zero, F.mul_entry, ite_eq_left rfl, F.mul_entry, ite_eq_left rfl]
  exact (tendsto_const_nhds.inner (𝕜 := ℂ)
    ((F.regroupingOperator e i).continuous.continuousAt.tendsto.comp
      (F.partialDiagonal_tendsto x))).congr
    (fun s => congrArg (inner ℂ y) (he s).symm)

theorem cuntzFamily_mem (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i : n) : (F.cuntzFamily e).entry i ∈ M :=
  F.regroupingOperator_mem e M hM i

theorem finiteCuntz_mem (n : ℕ) [NeZero n] (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i : Fin n) : (F.finiteCuntz n).entry i ∈ M :=
  F.cuntzFamily_mem _ M hM i

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite averages of unitary conjugations -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {G : Type*} [Fintype G] [Nonempty G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [Nonempty G] in
theorem finiteAverage_sub (f g : G → V) :
    finiteAverage (fun a => f a - g a) = finiteAverage f - finiteAverage g := by
  simp [finiteAverage, Finset.sum_sub_distrib, smul_sub]

theorem norm_finiteAverage_le (f : G → V) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) :
    ‖finiteAverage f‖ ≤ C := by
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ = (Fintype.card G : ℝ)⁻¹ * ‖∑ g, f g‖ := by
      simp [finiteAverage, norm_smul, norm_inv]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖f g‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _ : G, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun g _ => hf g)) (inv_nonneg.mpr hn.le)
    _ = C := by simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Nonempty G] in
theorem finiteUnitaryAverage_star (π : G → unitary (H →L[ℂ] H)) (h : H →L[ℂ] H) :
    star (finiteUnitaryAverage π h) = finiteUnitaryAverage π (star h) := by
  simp [finiteUnitaryAverage, finiteAverage, unitaryConj, star_mul, mul_assoc]

omit [Nonempty G] in
theorem finiteUnitaryAverage_selfAdjoint (π : G → unitary (H →L[ℂ] H))
    {h : H →L[ℂ] H} (hh : IsSelfAdjoint h) : IsSelfAdjoint (finiteUnitaryAverage π h) := by
  change star (finiteUnitaryAverage π h) = finiteUnitaryAverage π h
  rw [finiteUnitaryAverage_star, hh.star_eq]

variable [Group G]

omit [Nonempty G] in
theorem finiteUnitaryAverage_invariant (π : G →* unitary (H →L[ℂ] H))
    (h : H →L[ℂ] H) (g : G) :
    unitaryConj (π g) (finiteUnitaryAverage π h) = finiteUnitaryAverage π h := by
  have he : (∑ k : G, unitaryConj (π (g * k)) h) = ∑ k : G, unitaryConj (π k) h :=
    Equiv.sum_comp (Equiv.mulLeft g) (fun k => unitaryConj (π k) h)
  simp only [map_mul, unitaryConj_mul] at he
  unfold finiteUnitaryAverage finiteAverage
  simp only [unitaryConj, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1

omit [Nonempty G] in
theorem finiteUnitaryAverage_commutes (π : G →* unitary (H →L[ℂ] H))
    (h : H →L[ℂ] H) (g : G) :
    Commute (π g : H →L[ℂ] H) (finiteUnitaryAverage π h) := by
  have hh := congrArg (fun a : H →L[ℂ] H => a * (π g : H →L[ℂ] H))
    (finiteUnitaryAverage_invariant π h g)
  have hs := Unitary.star_mul_self_of_mem (π g).property
  change (π g : H →L[ℂ] H) * finiteUnitaryAverage π h =
    finiteUnitaryAverage π h * (π g : H →L[ℂ] H)
  simpa only [unitaryConj, mul_assoc, hs, mul_one] using hh


omit [Group G] in
theorem norm_sub_finiteUnitaryAverage_le (π : G → unitary (H →L[ℂ] H))
    (h : H →L[ℂ] H) {δ : ℝ}
    (hb : ∀ g, ‖h * (π g : H →L[ℂ] H) - (π g : H →L[ℂ] H) * h‖ ≤ δ) :
    ‖h - finiteUnitaryAverage π h‖ ≤ δ := by
  have he : finiteAverage (fun g => h - unitaryConj (π g) h) =
      h - finiteUnitaryAverage π h := by
    rw [finiteAverage_sub, finiteAverage_const]
    rfl
  rw [← he]
  apply norm_finiteAverage_le
  intro g
  have he : h - unitaryConj (π g) h =
      (h * (π g : H →L[ℂ] H) - (π g : H →L[ℂ] H) * h) * star (π g : H →L[ℂ] H) := by
    have hu := Unitary.mul_star_self_of_mem (π g).property
    simp only [sub_mul, mul_assoc, hu, mul_one, unitaryConj]
  rw [he, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
  exact hb g

/-- Conjugating a commutator conjugates its argument in the opposite direction. -/
theorem commutator_unitaryConj (u : unitary (H →L[ℂ] H)) (h a : H →L[ℂ] H) :
    unitaryConj u h * a - a * unitaryConj u h =
      unitaryConj u (h * unitaryConj (star u) a - unitaryConj (star u) a * h) := by
  have hu := Unitary.mul_star_self_of_mem u.property
  simp only [unitaryConj, Unitary.coe_star, star_star, mul_sub, sub_mul, mul_assoc, hu, mul_one]
  rw [← mul_assoc (u : H →L[ℂ] H) (star (u : H →L[ℂ] H)), hu, one_mul]

omit [Group G] in
theorem finiteUnitaryAverage_derivation_le
    (M : VonNeumannAlgebra H) (π : G → unitary (H →L[ℂ] H))
    (hπ : ∀ g, (π g : H →L[ℂ] H) ∈ M) (h : H →L[ℂ] H) {δ : ℝ}
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    ∀ a ∈ M, ‖finiteUnitaryAverage π h * a - a * finiteUnitaryAverage π h‖ ≤ δ * ‖a‖ := by
  intro a ha
  have he : finiteUnitaryAverage π h * a - a * finiteUnitaryAverage π h =
      finiteAverage (fun g => unitaryConj (π g) h * a - a * unitaryConj (π g) h) := by
    simp [finiteUnitaryAverage, finiteAverage,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, smul_sub]
  rw [he]
  apply norm_finiteAverage_le
  intro g
  rw [commutator_unitaryConj, norm_unitaryConj]
  have hm : unitaryConj (star (π g)) a ∈ M := by
    simp only [unitaryConj, Unitary.coe_star, star_star]
    exact M.mul_mem (M.mul_mem ((show star (π g : H →L[ℂ] H) ∈ M from
      M.toStarSubalgebra.star_mem' (hπ g))) ha) (hπ g)
  simpa only [norm_unitaryConj] using hb _ hm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging over a concrete finite matrix algebra

Signed permutation matrices give a finite unitary group whose commutant
is exactly the commutant of the matrix-unit system. Its uniform average
preserves the original scalar derivation bound.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A]
  [StarRing A]
  [_root_.Algebra ℂ A]
  [StarModule ℂ A]

omit [Fintype ι] in
/-- Changing one diagonal sign isolates the corresponding diagonal matrix unit. -/
theorem signDiagonal_reflection (i : ι) :
    signDiagonal (Function.update (1 : ι → ℤˣ) i (-1)) =
      1 - (2 : ℂ) • Matrix.single i i 1 := by
  ext j k
  by_cases hjk : j = k
  · subst k
    by_cases hji : j = i
    · subst j
      norm_num [signDiagonal, Matrix.diagonal, Matrix.single]
    · simp [signDiagonal, Matrix.diagonal, Matrix.single, hji, Ne.symm hji]
  · have hn : ¬ (i = j ∧ i = k) := fun h => hjk (h.1.symm.trans h.2)
    simp [signDiagonal, Matrix.diagonal, Matrix.single, hjk, hn]

theorem matrixUnit_diagonal_sandwich (E : Generator.MatrixUnitSystem ι A)
    (a : Matrix ι ι ℂ) (i j : ι) :
    E.entry i i * E.hom a * E.entry j j = a i j • E.entry i j := by
  simp only [Generator.MatrixUnitSystem.hom_apply, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, E.mul_entry]
  simp [E.mul_entry, smul_ite]

/-- Commuting with the finite signed-permutation group is enough to commute
with the entire full matrix algebra. -/
theorem commute_matrixUnits_of_signed (E : Generator.MatrixUnitSystem ι A) (x : A)
    (hx : ∀ g, Commute (matrixUnitSignedRepresentation E g : A) x) :
    ∀ i j, Commute (E.entry i j) x := by
  have hd (i : ι) : Commute (E.entry i i) x := by
    have hi := hx (SemidirectProduct.inl (Function.update (1 : ι → ℤˣ) i (-1)))
    rw [matrixUnitSignedRepresentation_inl, signDiagonal_reflection, map_sub, map_one,
      map_smul, E.hom_single, one_smul] at hi
    change (1 - (2 : ℂ) • E.entry i i) * x = x * (1 - (2 : ℂ) • E.entry i i) at hi
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm] at hi
    exact (smul_right_injective A (by norm_num : (2 : ℂ) ≠ 0)) (sub_right_inj.mp hi)
  have hp (σ : Equiv.Perm ι) : Commute (E.hom (Matrix.permMatrixHom (R := ℂ) σ)) x := by
    simpa only [matrixUnitSignedRepresentation_inr] using hx (SemidirectProduct.inr σ)
  intro i j
  have h := ((hd i).mul_left (hp (Equiv.swap i j))).mul_left (hd j)
  simpa only [matrixUnit_diagonal_sandwich, permutationMatrix_apply,
    Equiv.swap_apply_right, ↓reduceIte, one_smul] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem matrixUnitAverage_commutes (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H))
    (h : H →L[ℂ] H) : ∀ a ∈ E.algebra, Commute a (matrixUnitAverage E h) := by
  apply (E.commute_algebra_iff _).mpr
  exact commute_matrixUnits_of_signed E _ (finiteUnitaryAverage_commutes _ h)

/-- Finite-dimensional averaging improves the commutant without enlarging
either the displacement or the derivation bound. -/
theorem exists_matrixUnitAverage (M : VonNeumannAlgebra H)
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (hE : E.algebra ≤ M.toStarSubalgebra)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    ∃ h0 : H →L[ℂ] H,
      (∀ a ∈ E.algebra, Commute a h0) ∧ ‖h - h0‖ ≤ δ ∧
      (∀ a ∈ M, ‖h0 * a - a * h0‖ ≤ δ * ‖a‖) ∧
      (IsSelfAdjoint h → IsSelfAdjoint h0) := by
  have hm (g : SignedPermutation ι) : (matrixUnitSignedRepresentation E g : H →L[ℂ] H) ∈ M :=
    hE (matrixUnitSignedRepresentation_mem E g)
  refine ⟨matrixUnitAverage E h, matrixUnitAverage_commutes E h, ?_, ?_, ?_⟩
  · apply norm_sub_finiteUnitaryAverage_le
    intro g
    refine (hb _ (hm g)).trans ?_
    have hn : ‖(matrixUnitSignedRepresentation E g : H →L[ℂ] H)‖ ≤ 1 := by
      calc
        _ = ‖(matrixUnitSignedRepresentation E g : H →L[ℂ] H) * 1‖ := by rw [mul_one]
        _ = ‖(1 : H →L[ℂ] H)‖ := CStarRing.norm_coe_unitary_mul _ _
        _ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hδ
  · exact finiteUnitaryAverage_derivation_le M _ hm h hb
  · exact finiteUnitaryAverage_selfAdjoint _

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
-- module Solutions.OAIQ075_KS.KadisonKastler_CuntzCommutator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar commutator bounds amplify along commuting Cuntz families -/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.KadisonKastler.cuntzCommutatorOperatorStarOrder
attribute [local instance] OAI.KadisonKastler.cuntzCommutatorSourceStarOrder
theorem CuntzFamily.assemble_commutator (S : CuntzFamily ι H)
    (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (hcomm : ∀ i, Commute h (S.entry i))
    (X : CStarMatrix ι ι (H →L[ℂ] H)) :
    S.assemble (CStarMatrix.mapₗ (innerDerivation h) X) =
      h * S.assemble X - S.assemble X * h := by
  have hstar (i : ι) : h * star (S.entry i) = star (S.entry i) * h := by
    have he := congrArg star (hcomm i).eq
    simpa only [star_mul, hh.star_eq] using he.symm
  have hterm (i j : ι) :
      S.entry i * (h * X i j - X i j * h) * star (S.entry j) =
        h * (S.entry i * X i j * star (S.entry j)) -
          (S.entry i * X i j * star (S.entry j)) * h := by
    calc
      _ = (S.entry i * h) * X i j * star (S.entry j) -
          S.entry i * X i j * (h * star (S.entry j)) := by noncomm_ring
      _ = (h * S.entry i) * X i j * star (S.entry j) -
          S.entry i * X i j * (star (S.entry j) * h) := by rw [← (hcomm i).eq, hstar]
      _ = _ := by noncomm_ring
  calc
    _ = ∑ i, ∑ j, (h * (S.entry i * X i j * star (S.entry j)) -
        (S.entry i * X i j * star (S.entry j)) * h) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hterm i j
    _ = _ := by
      simp only [CuntzFamily.assemble, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]

attribute [local instance] OAI.KadisonKastler.cuntzCommutatorOperatorOrder
attribute [local instance] OAI.KadisonKastler.cuntzCommutatorSourceOrder
theorem CuntzFamily.matrix_commutator_le (S : CuntzFamily ι H)
    (M : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ M)
    (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (hcomm : ∀ i, Commute h (S.entry i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (X : CStarMatrix ι ι (Algebra M)) :
    ‖CStarMatrix.mapₗ ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) X‖ ≤
      δ * ‖X‖ := by
  let Y := X.map M.toStarSubalgebra.subtype
  have hY : ‖Y‖ ≤ ‖X‖ :=
    NonUnitalStarAlgHom.norm_apply_le (coefficientMatrixMap M.toStarSubalgebra.subtype) X
  have hentry : ∀ i j, Y i j ∈ M := fun i j => (X i j).property
  have hid : CStarMatrix.mapₗ ((innerDerivation h).comp
      M.toStarSubalgebra.subtype.toLinearMap) X =
      CStarMatrix.mapₗ (innerDerivation h) Y := rfl
  rw [hid, ← S.norm_assemble, S.assemble_commutator h hh hcomm]
  exact (hb _ (S.assemble_mem M hS Y hentry)).trans
    (by rw [S.norm_assemble]; exact mul_le_mul_of_nonneg_left hY hδ)

theorem completelyBounded_commutator_of_commuting_cuntz
    (M : VonNeumannAlgebra H) (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (hfamilies : ∀ n : ℕ, 2 ≤ n → ∃ S : CuntzFamily (Fin n) H,
      (∀ i, S.entry i ∈ M) ∧ (∀ i, Commute h (S.entry i)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    CompletelyBoundedBy ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) δ := by
  apply completelyBoundedBy_of_large_square
  intro n hn X
  obtain ⟨S, hSM, hSh⟩ := hfamilies n hn
  exact S.matrix_commutator_le M hSM h hh hSh hδ hb X

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PeriodicMatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite full matrix algebras from countable matrix units

The finite algebras need not be increasing. Their matrix units agree with
the countable matrix units on any fixed finite collection of columns once
the matrix size is large enough.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FullMatrixCorner

variable {E : Submodule ℂ H} [CompleteSpace E] (F : FullMatrixCorner E)

theorem periodicMatrixUnits_mem (n : ℕ) [NeZero n] (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i j : Fin n) :
    (F.periodicMatrixUnits n).entry i j ∈ M :=
  M.mul_mem (F.finiteCuntz_mem n M hM i)
    (star_mem (s := M.toStarSubalgebra) (F.finiteCuntz_mem n M hM j))

theorem finiteCuntz_column (n : ℕ) [NeZero n] (i : Fin n) (k : ℕ) (x : E) :
    (F.finiteCuntz n).entry i (F.column k x) = F.column (k * n + i) x :=
  F.regroupingOperator_column _ i k x

theorem finiteCuntz_adjoint_column (n : ℕ) [NeZero n] (i j : Fin n) (k : ℕ) (x : E) :
    star ((F.finiteCuntz n).entry i) (F.column (k * n + j) x) =
      if i = j then F.column k x else 0 :=
  F.adjoint_regrouping_column _ i j k x

theorem periodicMatrixUnits_column (n : ℕ) [NeZero n] (i j k : Fin n) (x : E) :
    (F.periodicMatrixUnits n).entry i j (F.column k x) =
      if j = k then F.column i x else 0 := by
  change (F.finiteCuntz n).entry i
    (star ((F.finiteCuntz n).entry j) (F.column k x)) = _
  have he := F.finiteCuntz_adjoint_column n j k 0 x
  simp only [Nat.zero_mul, Nat.zero_add] at he
  rw [he]
  split_ifs <;> simp only [map_zero, F.finiteCuntz_column, Nat.zero_mul, Nat.zero_add]

theorem periodicMatrixUnits_agree_on_column (n : ℕ) [NeZero n]
    (i j k : ℕ) (hi : i < n) (hj : j < n) (hk : k < n) (x : E) :
    (F.periodicMatrixUnits n).entry ⟨i, hi⟩ ⟨j, hj⟩ (F.column k x) =
      F.entry i j (F.column k x) := by
  rw [F.entry_column]
  simpa only [Fin.mk.injEq] using
    F.periodicMatrixUnits_column n ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ x

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity and norm bounds in pointwise weak operator limits

These lemmas retain the complete positivity of the maps obtained from
finite Hilbert-space tests. No normality of the limiting map is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [CompleteSpace H] in
/-- A uniform operator norm bound survives a weak coefficient limit. -/
theorem norm_le_of_weak_limit {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (T : ι → H →L[ℂ] K) (S : H →L[ℂ] K)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (S x)))) :
    ‖S‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  change (inner ℂ (S x) y).re ≤ C
  have hb (i : ι) : (inner ℂ y (T i x)).re ≤ C := by
    calc
      _ ≤ ‖inner ℂ y (T i x)‖ := Complex.re_le_norm _
      _ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * ‖x‖) := mul_le_mul_of_nonneg_left
        ((T i).le_of_opNorm_le (hT i) x) (norm_nonneg y)
      _ = C := by rw [hx, hy]; ring
  have hr := (Complex.continuous_re.tendsto _).comp (ht x y)
  rw [show (inner ℂ (S x) y).re = (inner ℂ y (S x)).re from
    inner_re_symm (𝕜 := ℂ) (S x) y]
  exact le_of_tendsto hr (Eventually.of_forall hb)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PeriodicMatrixAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging over the countable matrix factor

Weak limits of finite signed-permutation averages commute with the
countable matrix units, preserving both the displacement and the scalar
commutator estimate.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isSelfAdjoint_of_weak_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → H →L[ℂ] H) (T : H →L[ℂ] H) (ha : ∀ i, IsSelfAdjoint (a i))
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (a i x)) l (𝓝 (inner ℂ y (T x)))) :
    IsSelfAdjoint T := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (T x) y = inner ℂ x (T y)
  have he (i : ι) : star (inner ℂ y (a i x)) = inner ℂ x (a i y) := by
    change (starRingEnd ℂ) (inner ℂ y (a i x)) = _
    rw [inner_conj_symm]
    exact (ha i).isSymmetric x y
  have hlim := (ht x y).star.congr he
  have hid := tendsto_nhds_unique hlim (ht y x)
  change (starRingEnd ℂ) (inner ℂ y (T x)) = inner ℂ x (T y) at hid
  simpa only [inner_conj_symm] using hid

namespace FullMatrixCorner

variable {E : Submodule ℂ H} [CompleteSpace E] (F : FullMatrixCorner E)

theorem weak_limit_commutes_matrixUnits {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (a : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (ha : ∀ n i j, Commute ((F.periodicMatrixUnits (n + 1)).entry i j) (a n))
    (ht : ∀ x y, Tendsto (fun n => inner ℂ y (a n x)) l (𝓝 (inner ℂ y (T x)))) :
    ∀ i j, Commute (F.entry i j) T := by
  intro i j
  apply Commute.symm
  apply F.ext_on_columns
  intro k x
  apply F.eq_of_inner_columns
  intro m y
  change inner ℂ (F.column m y) (T (F.entry i j (F.column k x))) =
    inner ℂ (F.column m y) (F.entry i j (T (F.column k x)))
  have he : ∀ᶠ n in l,
      inner ℂ (F.column m y) (a n (F.entry i j (F.column k x))) =
        inner ℂ (star (F.entry i j) (F.column m y)) (a n (F.column k x)) := by
    filter_upwards [(eventually_ge_atTop (max (max i j) (max k m))).filter_mono hl] with n hn
    have hi : i < n + 1 := by omega
    have hj : j < n + 1 := by omega
    have hk : k < n + 1 := by omega
    have hm : m < n + 1 := by omega
    let P := (F.periodicMatrixUnits (n + 1)).entry ⟨i, hi⟩ ⟨j, hj⟩
    have hright : P (F.column k x) = F.entry i j (F.column k x) :=
      F.periodicMatrixUnits_agree_on_column _ i j k hi hj hk x
    have hleft : star P (F.column m y) = star (F.entry i j) (F.column m y) := by
      rw [F.star_entry]
      change (star ((F.periodicMatrixUnits (n + 1)).entry ⟨i, hi⟩ ⟨j, hj⟩)) _ = _
      rw [(F.periodicMatrixUnits (n + 1)).star_entry]
      exact F.periodicMatrixUnits_agree_on_column _ j i m hj hi hm y
    calc
      _ = inner ℂ (F.column m y) (a n (P (F.column k x))) := by rw [hright]
      _ = inner ℂ (F.column m y) (P (a n (F.column k x))) :=
        congrArg (fun S : H →L[ℂ] H => inner ℂ (F.column m y) (S (F.column k x)))
          (ha n ⟨i, hi⟩ ⟨j, hj⟩).eq.symm
      _ = inner ℂ (star P (F.column m y)) (a n (F.column k x)) := by
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      _ = _ := by rw [hleft]
  have hlim := (ht (F.entry i j (F.column k x)) (F.column m y)).congr' he
  have heq := tendsto_nhds_unique hlim (ht (F.column k x)
    (star (F.entry i j) (F.column m y)))
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left] using heq

theorem exists_matrixUnit_commuting_average (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    ∃ h0 : H →L[ℂ] H, IsSelfAdjoint h0 ∧ (∀ i j, Commute (F.entry i j) h0) ∧
      ‖h - h0‖ ≤ δ ∧ (∀ a ∈ M, ‖h0 * a - a * h0‖ ≤ δ * ‖a‖) := by
  classical
  have hfinite (n : ℕ) := exists_matrixUnitAverage M (F.periodicMatrixUnits (n + 1))
    ((F.periodicMatrixUnits (n + 1)).algebra_le_iff M.toStarSubalgebra |>.mpr
      (F.periodicMatrixUnits_mem (n + 1) M hM)) h hδ hb
  choose a hac had hab has using hfinite
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have han (n : ℕ) : ‖a n‖ ≤ ‖h‖ + δ := by
    calc
      ‖a n‖ ≤ ‖h‖ + ‖a n - h‖ := by
        simpa only [add_sub_cancel] using norm_add_le h (a n - h)
      _ ≤ ‖h‖ + δ := by rw [norm_sub_rev]; exact add_le_add le_rfl (had n)
  obtain ⟨h0, _, ht⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω a
    (‖h‖ + δ) (add_nonneg (norm_nonneg h) hδ) han
  refine ⟨h0, isSelfAdjoint_of_weak_limit a h0 (fun n => has n hh) ht,
    F.weak_limit_commutes_matrixUnits hω a h0 (fun n i j =>
      hac n _ ((F.periodicMatrixUnits (n + 1)).entry_mem i j)) ht, ?_, ?_⟩
  · apply norm_le_of_weak_limit (l := (ω : Filter ℕ)) (fun n => h - a n) (h - h0) hδ had
    intro x y
    simpa only [sub_apply, inner_sub_right] using tendsto_const_nhds.sub (ht x y)
  · intro b hbM
    apply norm_le_of_weak_limit (l := (ω : Filter ℕ))
      (fun n => a n * b - b * a n) (h0 * b - b * h0)
      (mul_nonneg hδ (norm_nonneg b)) (fun n => hab n b hbM)
    intro x y
    have hlim := (ht (b x) y).sub (ht x (star b y))
    simpa only [mul_apply_eq_comp, sub_apply, inner_sub_right,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] using hlim

theorem commute_finiteCuntz_of_commute_matrixUnits (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hc : ∀ i j, Commute (F.entry i j) T)
    (n : ℕ) [NeZero n] (i : Fin n) : Commute T ((F.finiteCuntz n).entry i) := by
  let C : VonNeumannAlgebra H :=
    { toStarSubalgebra := StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
      centralizer_centralizer' := Set.centralizer_centralizer_centralizer _ }
  have hmem (j k : ℕ) : F.entry j k ∈ C := by
    change F.entry j k ∈ StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
    rw [StarSubalgebra.mem_centralizer_iff]
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact ⟨(hc j k).symm.eq, by rw [hT.star_eq]; exact (hc j k).symm.eq⟩
  have hS := F.finiteCuntz_mem n C hmem i
  change (F.finiteCuntz n).entry i ∈
    StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) at hS
  rw [StarSubalgebra.mem_centralizer_iff] at hS
  exact (hS T (Set.mem_singleton T)).1

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommutantDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap_apply _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

namespace FullMatrixCorner

attribute [local instance] OAI.KadisonKastler.matrixDistanceOperatorStarOrder
attribute [local instance] OAI.KadisonKastler.matrixDistanceSourceStarOrder
variable {E : Submodule ℂ H} [CompleteSpace E] (F : FullMatrixCorner E)

attribute [local instance] OAI.KadisonKastler.matrixDistanceOperatorOrder
attribute [local instance] OAI.KadisonKastler.matrixDistanceSourceOrder
theorem exists_commutant_approximation_oai (M : VonNeumannAlgebra H)
    (hPublished : PublishedBlockCommutantApproximation (Algebra M) H)
    (hM : ∀ i j, F.entry i j ∈ M)
    (h : H →L[ℂ] H) (hh : IsSelfAdjoint h) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (r : ℝ) (hr : δ / 2 < r) :
    ∃ k : H →L[ℂ] H, k ∈ M.commutant ∧ ‖h - k‖ < δ + r := by
  obtain ⟨h0, hh0, hc, hdist, hb0⟩ := F.exists_matrixUnit_commuting_average M hM h hh hδ hb
  have hcb := completelyBounded_commutator_of_commuting_cuntz M h0 hh0
    (fun n hn => by
      have : NeZero n := ⟨by omega⟩
      exact ⟨F.finiteCuntz n, F.finiteCuntz_mem n M hM,
        F.commute_finiteCuntz_of_commute_matrixUnits h0 hh0 hc n⟩) hδ hb0
  obtain ⟨k, hk, hclose⟩ := exists_commutant_approximation_of_complete_bound M
    hPublished h0 hδ hcb r hr
  refine ⟨k, hk, ?_⟩
  calc
    ‖h - k‖ ≤ ‖h - h0‖ + ‖h0 - k‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ + r := add_lt_add_of_le_of_lt hdist hclose

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.FullMatrixCorner.exists_commutant_approximation_oai.{u_1} := @OAI.KadisonKastler.FullMatrixCorner.exists_commutant_approximation_oai.{u_1}
