-- Prove2me | solution 1 for OAI.KadisonKastler.probabilityOperatorIntegral_complete_commutant_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:13:05.783579+00:00
-- url     : https://prove2.me/submissions/720a0b8d-61fb-44fe-a41b-b07b6e9bdb4f

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
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
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
import Definitions.Def_Q260K065

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixVonNeumann
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete von Neumann algebra of finite matrices

The commutant of the diagonal copy of `M'` consists exactly of the
operators all of whose matrix entries lie in `M`. This identifies it with
the usual C⋆-matrix algebra, including the represented normalized trace.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.KadisonKastler.matrixVNOperatorOrder
attribute [local instance] OAI.KadisonKastler.matrixVNOperatorStarOrder
attribute [local instance] OAI.KadisonKastler.matrixVNAlgebraOrder
attribute [local instance] OAI.KadisonKastler.matrixVNAlgebraStarOrder
theorem norm_matrixOperatorHom (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) : ‖matrixOperatorHom M x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map (matrixOperatorHom M) (matrixOperatorHom_injective M) x

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
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The uniform completely bounded derivation estimate for II₁ factors -/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance completeAmplificationSourceOrder_rc83c62_1 : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance completeAmplificationSourceStarOrder_rc83c62_1 : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance completeAmplificationOperatorOrder_rc83c62_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance completeAmplificationOperatorStarOrder_rc83c62_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- The entrywise derivation acts as commutation with the diagonal operator. -/
theorem hilbertMatrix_map_innerDerivation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : H →L[ℂ] H) (X : CStarMatrix ι ι (Algebra M)) :
    hilbertMatrix (CStarMatrix.mapₗ
      ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) X) =
      hilbertMatrix (diagonalAmplification h) * matrixOperatorHom M X -
        matrixOperatorHom M X * hilbertMatrix (diagonalAmplification h) := by
  rw [matrixOperatorHom_apply, ← hilbertMatrix_mul, ← hilbertMatrix_mul]
  have hsub := map_sub (hilbertMatrixHom (H := H) (n := ι))
    (diagonalAmplification h * X.map M.toStarSubalgebra.subtype)
    (X.map M.toStarSubalgebra.subtype * diagonalAmplification h)
  change hilbertMatrix (diagonalAmplification h * X.map M.toStarSubalgebra.subtype -
      X.map M.toStarSubalgebra.subtype * diagonalAmplification h) =
    hilbertMatrix (diagonalAmplification h * X.map M.toStarSubalgebra.subtype) -
      hilbertMatrix (X.map M.toStarSubalgebra.subtype * diagonalAmplification h) at hsub
  rw [← hsub]
  congr 1
  apply CStarMatrix.ext
  intro i j
  change h * (X i j).val - (X i j).val * h =
    (Matrix.diagonal (fun _ : ι => h) *
      CStarMatrix.ofMatrix.symm (X.map M.toStarSubalgebra.subtype)) i j -
      (CStarMatrix.ofMatrix.symm (X.map M.toStarSubalgebra.subtype) *
        Matrix.diagonal (fun _ : ι => h)) i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProbabilityOperatorRelations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Linear relations and commutator bounds under vector integration

The operator fields are only assumed measurable on each vector. Fixed
left and right multiplication commute with their probability integral;
essential operator-norm commutator bounds therefore pass to the integral.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A uniform almost-everywhere commutator bound survives vector integration. -/
theorem norm_probabilityOperatorIntegral_commutator_le
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (A : H →L[ℂ] H)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomm : ∀ᵐ s ∂μ, ‖F s * A - A * F s‖ ≤ ε) :
    ‖probabilityOperatorIntegral μ F hF C hC * A -
      A * probabilityOperatorIntegral μ F hF C hC‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  have hi := integrable_bounded_operator_vector μ F hF hC x
  have hiA := integrable_bounded_operator_vector μ F hF hC (A x)
  have hAi : Integrable (fun s => A (F s x)) μ := A.integrable_comp hi
  change ‖(∫ s, F s (A x) ∂μ) - A (∫ s, F s x ∂μ)‖ ≤ ε * ‖x‖
  rw [← A.integral_comp_comm hi, ← integral_sub hiA hAi]
  have hb : ∀ᵐ s ∂μ, ‖F s (A x) - A (F s x)‖ ≤ ε * ‖x‖ := by
    filter_upwards [hcomm] with s hs
    exact ((F s * A - A * F s).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  have hn := norm_integral_le_of_norm_le_const (μ := μ) hb
  simpa only [probReal_univ, mul_one] using hn

omit [CompleteSpace H] in
/-- An algebra approximation bounds every commutator with its commutant. -/
theorem norm_commutator_of_near_commuting
    (T b A : H →L[ℂ] H) {δ : ℝ} (hTb : ‖T - b‖ ≤ δ)
    (hbA : b * A = A * b) : ‖T * A - A * T‖ ≤ 2 * δ * ‖A‖ := by
  have he : T * A - A * T = (T - b) * A - A * (T - b) := by
    rw [sub_mul, mul_sub, hbA]
    abel
  rw [he]
  calc
    _ ≤ ‖(T - b) * A‖ + ‖A * (T - b)‖ := norm_sub_le _ _
    _ ≤ ‖T - b‖ * ‖A‖ + ‖A‖ * ‖T - b‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ δ * ‖A‖ + ‖A‖ * δ := add_le_add
      (mul_le_mul_of_nonneg_right hTb (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hTb (norm_nonneg _))
    _ = _ := by ring

/-- This estimate requires no measurable choice of nearby algebra elements. -/
theorem norm_probabilityOperatorIntegral_commutator_of_near
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (A : H →L[ℂ] H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s ∂μ, ∃ b : H →L[ℂ] H, b * A = A * b ∧ ‖F s - b‖ ≤ δ) :
    ‖probabilityOperatorIntegral μ F hF C hC * A -
      A * probabilityOperatorIntegral μ F hF C hC‖ ≤ 2 * δ * ‖A‖ := by
  apply norm_probabilityOperatorIntegral_commutator_le μ F hF C hC A (by positivity)
  filter_upwards [hnear] with s hs
  obtain ⟨b, hbA, hFb⟩ := hs
  exact norm_commutator_of_near_commuting _ b A hFb hbA

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProbabilityMatrixDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

attribute [local instance] OAI.KadisonKastler.matrixIntegralStarOrder
theorem probabilityOperatorIntegral_diagonal
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (n : ℕ) :
    probabilityOperatorIntegral μ (fun s => Generator.diagonalOperator (ι := Fin n) (F s))
      (diagonalOperator_vector_measurable μ F hF n) C
      (hC.mono fun s hs => (norm_diagonalOperator_le (F s) n).trans hs) =
      Generator.diagonalOperator (probabilityOperatorIntegral μ F hF C hC) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  change (∫ s, Generator.diagonalOperator (ι := Fin n) (F s) x ∂μ) i = ∫ s, F s (x i) ∂μ
  have hi := integrable_bounded_operator_vector μ
    (fun s => Generator.diagonalOperator (ι := Fin n) (F s))
    (diagonalOperator_vector_measurable μ F hF n)
    (hC.mono fun s hs => (norm_diagonalOperator_le (F s) n).trans hs) x
  let p : Generator.FiniteHilbert (Fin n) H →L[ℂ] H := PiLp.proj 2 (fun _ : Fin n => H) i
  exact (p.integral_comp_comm hi).symm

/-- A matrix over the commutant commutes with each diagonal element of the algebra. -/
theorem diagonal_commutes_commutant_matrix (M : VonNeumannAlgebra H)
    (b : H →L[ℂ] H) (hb : b ∈ M) (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (Algebra M.commutant)) :
    Generator.diagonalOperator b * matrixOperatorHom M.commutant X =
      matrixOperatorHom M.commutant X * Generator.diagonalOperator b := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  simp only [mul_apply_eq_comp, Generator.diagonalOperator_apply,
    matrixOperatorHom_apply, hilbertMatrix_apply, CStarMatrix.map_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun T : H →L[ℂ] H => T (x j))
    ((VonNeumannAlgebra.mem_commutant_iff.mp (X i j).property) b hb)

attribute [local instance] OAI.KadisonKastler.matrixIntegralOrder
attribute [local instance] OAI.KadisonKastler.integralSourceOrder
attribute [local instance] OAI.KadisonKastler.integralSourceStarOrder
/-- Pointwise algebra distance bounds pass to a complete commutator bound
for the integral against the algebra's commutant. -/
theorem probabilityOperatorIntegral_complete_commutant_bound_oai
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C)
    (M : VonNeumannAlgebra H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s ∂μ, ∃ b : H →L[ℂ] H, b ∈ M ∧ ‖F s - b‖ ≤ δ) :
    CompletelyBoundedBy
      ((innerDerivation (probabilityOperatorIntegral μ F hF C hC)).comp
        M.commutant.toStarSubalgebra.subtype.toLinearMap) (2 * δ) := by
  apply completelyBoundedBy_of_large_square
  intro n _ X
  have hd := norm_probabilityOperatorIntegral_commutator_of_near μ
    (fun s => Generator.diagonalOperator (ι := Fin n) (F s))
    (diagonalOperator_vector_measurable μ F hF n) C
    (hC.mono fun s hs => (norm_diagonalOperator_le (F s) n).trans hs)
    (matrixOperatorHom M.commutant X) hδ ?_
  · rw [probabilityOperatorIntegral_diagonal, norm_matrixOperatorHom] at hd
    rw [← norm_hilbertMatrix, hilbertMatrix_map_innerDerivation,
      hilbertMatrix_diagonalAmplification_eq]
    exact hd
  · filter_upwards [hnear] with s hs
    obtain ⟨b, hb, hFb⟩ := hs
    refine ⟨Generator.diagonalOperator (ι := Fin n) b,
      diagonal_commutes_commutant_matrix M b hb n X, ?_⟩
    have he : Generator.diagonalOperator (ι := Fin n) (F s) -
        Generator.diagonalOperator b = Generator.diagonalOperator (F s - b) := by
      apply ContinuousLinearMap.ext
      intro x
      apply PiLp.ext
      intro i
      rfl
    rw [he]
    exact (norm_diagonalOperator_le (F s - b) n).trans hFb

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.probabilityOperatorIntegral_complete_commutant_bound_oai.{u_1, u_2} := @OAI.KadisonKastler.probabilityOperatorIntegral_complete_commutant_bound_oai.{u_1, u_2}
