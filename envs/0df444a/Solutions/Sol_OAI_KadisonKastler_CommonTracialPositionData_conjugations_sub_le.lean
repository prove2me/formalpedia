-- Prove2me | solution 1 for OAI.KadisonKastler.CommonTracialPositionData.conjugations_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:51:50.135674+00:00
-- url     : https://prove2.me/submissions/8e2f9c9f-ff01-4a77-9a4e-fdd5c277f3fb

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
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
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K032
import Theorems.Thm_OAI_KadisonKastler_exists_finite_bimodular_covariance_families
import Theorems.Thm_OAI_KadisonKastler_opNorm_le_of_finite_covariance_families

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kkDistance_nonneg (M N : VonNeumannAlgebra H) : 0 ≤ kkDistance M N :=
  Metric.hausdorffDist_nonneg

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteBimodularBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded-ball tests for bimodular operators

Relative scalar averaging supplies the finite covariance families. The
left and right unitary actions then preserve their pairings, so the
proved sign-randomization and clipping estimate applies with constant 384.
-/

namespace KadisonKastler

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}

/-- Unit-ball tests control a bounded bimodular operator on the trace
Hilbert realization, with the manuscript's constant 384. -/
theorem opNorm_le_of_irreducible_bimodular_tests
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hJdense : DenseRange J)
    (hτ : FiniteVectorTrace τ) (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (V : E →L[ℂ] E) (L Q : unitary R → unitary (E →L[ℂ] E))
    (hL : ∀ (u : unitary R) (x : Algebra M), J (φ u * x) = (L u : E →L[ℂ] E) (J x))
    (hQ : ∀ (u : unitary R) (x : Algebra M), J (x * φ u) = (Q u : E →L[ℂ] E) (J x))
    (hVL : ∀ u, Commute V (L u : E →L[ℂ] E))
    (hVQ : ∀ u, Commute V (Q u : E →L[ℂ] E)) {K : ℝ}
    (hK : ∀ x y : Algebra M, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖inner ℂ (V (J x)) (J y)‖ ≤ K) : ‖V‖ ≤ 384 * K := by
  let : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder (Algebra M)
  let : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing (Algebra M)
  apply opNorm_le_of_finite_covariance_families τ J hJ hJdense V hK
  intro a b ha hb
  exact exists_finite_bimodular_covariance_families τ J hJ hτ φ hirr
    V L Q hL hQ hVL hVQ a b ha hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialConjugationBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Comparing tracial conjugations in common position

The two conjugations are supplied as actual conjugate-linear isometries.
Common right-action commutation remains an explicit structural premise;
the distance estimate itself follows from unit-ball approximation and
the proved finite bimodular test.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Composing by an involutive isometry identifies the two operator norms. -/
theorem norm_tracialConjugationDefect (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) :
    ‖tracialConjugationDefect J₁ J₂‖ =
      ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ := by
  let D : H →L⋆[ℂ] H := (J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)
  have he (ξ : H) : ‖tracialConjugationDefect J₁ J₂ ξ‖ = ‖D (J₁ ξ)‖ := by
    change ‖J₂ (J₁ ξ) - ξ‖ = ‖J₁ (J₁ ξ) - J₂ (J₁ ξ)‖
    rw [hJ₁ ξ, norm_sub_rev]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro ξ
    rw [he]
    exact (D.le_opNorm (J₁ ξ)).trans_eq (by rw [J₁.norm_map])
  · change ‖D‖ ≤ ‖tracialConjugationDefect J₁ J₂‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro ξ
    calc
      ‖D ξ‖ = ‖tracialConjugationDefect J₁ J₂ (J₁ ξ)‖ := by
        rw [he, hJ₁ ξ]
      _ ≤ ‖tracialConjugationDefect J₁ J₂‖ * ‖J₁ ξ‖ :=
        (tracialConjugationDefect J₁ J₂).le_opNorm _
      _ = _ := by rw [J₁.norm_map]

/-- Close unit balls bound the comparison operator on every bounded
algebra vector by twice the Kadison--Kastler tolerance. -/
theorem tracialConjugationDefect_unitBall_bound
    {M N : VonNeumannAlgebra H} (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ y : Algebra N, J₂ (y.val Ω) = (star y).val Ω)
    {b : ℝ} (hb : kkDistance M N < b) (x : Algebra M) (hx : ‖x‖ ≤ 1) :
    ‖tracialConjugationDefect J₁ J₂ (x.val Ω)‖ ≤ 2 * b := by
  obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx (M := M) (N := N)
    (x := x.val) ⟨x.property, hx⟩ hb
  let z : Algebra N := ⟨y, hy.1⟩
  have hz : J₂ ((star z).val Ω) = z.val Ω := by
    simpa only [star_star] using hN (star z)
  rw [tracialConjugationDefect_apply, hM]
  calc
    _ ≤ ‖J₂ ((star x).val Ω) - J₂ ((star z).val Ω)‖ +
        ‖J₂ ((star z).val Ω) - x.val Ω‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖(star x).val Ω - (star z).val Ω‖ + ‖z.val Ω - x.val Ω‖ := by
      rw [← map_sub, J₂.norm_map, hz]
    _ ≤ ‖(star x).val - (star z).val‖ * ‖Ω‖ + ‖z.val - x.val‖ * ‖Ω‖ := by
      exact add_le_add (( (star x).val - (star z).val).le_opNorm Ω)
        ((z.val - x.val).le_opNorm Ω)
    _ = 2 * ‖x.val - y‖ := by
      change ‖star x.val - star y‖ * ‖Ω‖ + ‖y - x.val‖ * ‖Ω‖ = _
      rw [← star_sub, norm_star, norm_sub_rev y, hΩ]
      ring
    _ ≤ 2 * b := by linarith

/-- The norm-768 tracial-conjugation estimate under common module actions
commuting with the comparison operator. -/
theorem norm_tracialConjugations_sub_le
    {M N : VonNeumannAlgebra H} {R : Type*} [CStarAlgebra R]
    (τ : FaithfulTracialState (Algebra M)) (ι : Algebra M →ₗ[ℂ] H)
    (hι : ∀ x, ‖ι x‖ = traceTwoNorm τ x) (hιdense : DenseRange ι)
    (hτ : FiniteVectorTrace τ) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hιΩ : ∀ x : Algebra M, ι x = x.val Ω)
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (hJ₁ : Function.Involutive J₁)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ y : Algebra N, J₂ (y.val Ω) = (star y).val Ω)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ a : Algebra M, (∀ r : R, φ r * a = a * φ r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (L Q : unitary R → unitary (H →L[ℂ] H))
    (hL : ∀ (u : unitary R) (x : Algebra M), ι (φ u * x) = (L u : H →L[ℂ] H) (ι x))
    (hQ : ∀ (u : unitary R) (x : Algebra M), ι (x * φ u) = (Q u : H →L[ℂ] H) (ι x))
    (hTL : ∀ u, Commute (tracialConjugationDefect J₁ J₂) (L u : H →L[ℂ] H))
    (hTQ : ∀ u, Commute (tracialConjugationDefect J₁ J₂) (Q u : H →L[ℂ] H))
    {b : ℝ} (hb : kkDistance M N < b) :
    ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ ≤ 768 * b := by
  have hb0 : 0 ≤ b := (kkDistance_nonneg M N).trans hb.le
  have htest (x y : Algebra M) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
      ‖inner ℂ (tracialConjugationDefect J₁ J₂ (ι x)) (ι y)‖ ≤ 2 * b := by
    have hTx : ‖tracialConjugationDefect J₁ J₂ (ι x)‖ ≤ 2 * b := by
      rw [hιΩ]
      exact tracialConjugationDefect_unitBall_bound J₁ J₂ Ω hΩ hM hN hb x hx
    have hiy : ‖ι y‖ ≤ 1 := by
      calc
        ‖ι y‖ = ‖y.val Ω‖ := by rw [hιΩ]
        _ ≤ ‖y.val‖ * ‖Ω‖ := y.val.le_opNorm Ω
        _ = ‖y‖ := by rw [hΩ, mul_one]; rfl
        _ ≤ 1 := hy
    calc
      _ ≤ ‖tracialConjugationDefect J₁ J₂ (ι x)‖ * ‖ι y‖ := norm_inner_le_norm _ _
      _ ≤ (2 * b) * 1 := mul_le_mul hTx hiy (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hnorm := opNorm_le_of_irreducible_bimodular_tests τ ι hι hιdense hτ φ hirr
    (tracialConjugationDefect J₁ J₂) L Q hL hQ hTL hTQ htest
  rw [norm_tracialConjugationDefect J₁ J₂ hJ₁] at hnorm
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common right actions in a cyclic representation

Two operators in the same commutant are equal if they agree on the cyclic
vector. Equality of the right actions obtained this way makes the product
of the two tracial conjugations commute with both module actions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Equality of the right conjugates intertwines the product of the two
conjugations with the original operator. -/
theorem conjugations_comp_apply_commute
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (a : H →L[ℂ] H)
    (ha : conjugationOperator J₁ a = conjugationOperator J₂ a) (ξ : H) :
    J₂ (J₁ (a ξ)) = a (J₂ (J₁ ξ)) := by
  have h := congrArg (fun b : H →L[ℂ] H => J₂ (b (J₁ ξ))) ha
  change J₂ (J₁ (a (J₁ (J₁ ξ)))) = J₂ (J₂ (a (J₂ (J₁ ξ)))) at h
  rw [hJ₁ ξ, hJ₂ (a (J₂ (J₁ ξ)))] at h
  exact h

/-- Subtracting the identity retains this commutation relation. -/
theorem tracialConjugationDefect_commute_of_common_right
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (a : H →L[ℂ] H)
    (ha : conjugationOperator J₁ a = conjugationOperator J₂ a) :
    Commute (tracialConjugationDefect J₁ J₂) a := by
  change tracialConjugationDefect J₁ J₂ * a = a * tracialConjugationDefect J₁ J₂
  ext ξ
  change J₂ (J₁ (a ξ)) - a ξ = a (J₂ (J₁ ξ) - ξ)
  rw [map_sub, conjugations_comp_apply_commute J₁ J₂ hJ₁ hJ₂ a ha]

/-- The same comparison commutes with the common right operator too. -/
theorem tracialConjugationDefect_commute_both
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (a : H →L[ℂ] H)
    (ha : conjugationOperator J₁ a = conjugationOperator J₂ a) :
    Commute (tracialConjugationDefect J₁ J₂) a ∧
      Commute (tracialConjugationDefect J₁ J₂) (conjugationOperator J₁ a) := by
  refine ⟨tracialConjugationDefect_commute_of_common_right J₁ J₂ hJ₁ hJ₂ a ha, ?_⟩
  apply tracialConjugationDefect_commute_of_common_right J₁ J₂ hJ₁ hJ₂
  calc
    conjugationOperator J₁ (conjugationOperator J₁ a) = a :=
      conjugationOperator_twice J₁ hJ₁ a
    _ = conjugationOperator J₂ (conjugationOperator J₁ a) := by
      rw [ha, conjugationOperator_twice J₂ hJ₂]

variable [CompleteSpace H]

/-- A common left multiplier has the same right-action value on the
common standard vector, before equality of the right operators is known. -/
theorem conjugationOperator_common_vector
    (M N : VonNeumannAlgebra H) (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ x : Algebra N, J₂ (x.val Ω) = (star x).val Ω)
    (a : H →L[ℂ] H) (haM : a ∈ M) (haN : a ∈ N) :
    conjugationOperator J₁ a Ω = conjugationOperator J₂ a Ω := by
  have h₁ : J₁ Ω = Ω := by
    simpa only [star_one, OneMemClass.coe_one, one_apply_eq_self] using hM 1
  have h₂ : J₂ Ω = Ω := by
    simpa only [star_one, OneMemClass.coe_one, one_apply_eq_self] using hN 1
  change J₁ (a (J₁ Ω)) = J₂ (a (J₂ Ω))
  rw [h₁, h₂]
  exact (hM ⟨a, haM⟩).trans (hN ⟨a, haN⟩).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Right actions and the common subalgebra projection

The right action of a common unitary reduces the closed subspace generated
by the common algebra and the standard vector. Thus equality of the two
basic constructions gives the cross-commutant membership required for the
common right-action argument, without identifying the whole commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conjugationOperator_star_unitary (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (u : unitary (H →L[ℂ] H)) :
    star (conjugationOperator J u) = conjugationOperator J (star (u : H →L[ℂ] H)) := by
  let q := conjugationUnitary J hJ u
  have hi : conjugationOperator J (star (u : H →L[ℂ] H)) * (q : H →L[ℂ] H) = 1 := by
    ext ξ
    change J (star (u : H →L[ℂ] H) (J (J ((u : H →L[ℂ] H) (J ξ))))) = ξ
    rw [hJ ((u : H →L[ℂ] H) (J ξ))]
    change J ((star (u : H →L[ℂ] H) * (u : H →L[ℂ] H)) (J ξ)) = ξ
    rw [Unitary.star_mul_self_of_mem u.property, one_apply_eq_self, hJ ξ]
  change star (q : H →L[ℂ] H) = _
  calc
    star (q : H →L[ℂ] H) =
        (conjugationOperator J (star (u : H →L[ℂ] H)) * (q : H →L[ℂ] H)) *
          star (q : H →L[ℂ] H) := by rw [hi, one_mul]
    _ = conjugationOperator J (star (u : H →L[ℂ] H)) := by
      rw [mul_assoc, Unitary.mul_star_self_of_mem q.property, mul_one]

/-- A bounded operator preserving the algebra orbit also preserves its
closed linear span. -/
theorem vectorOrbitClosure_invariant_of_orbit
    (R : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (T : H →L[ℂ] H)
    (hT : ∀ x : R, ∃ y : R, T (x.val Ω) = y.val Ω)
    {ξ : H} (hξ : ξ ∈ Generator.vectorOrbitClosure R Ω) :
    T ξ ∈ Generator.vectorOrbitClosure R Ω := by
  have h : (Generator.vectorOrbitMap R Ω).range.topologicalClosure ≤
      (Generator.vectorOrbitClosure R Ω).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hT x
      exact Submodule.le_topologicalClosure _ ⟨y, hy.symm⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact h hξ

/-- Right multiplication by a common unitary commutes with the orthogonal
projection onto the common algebra's cyclic subspace. -/
theorem conjugationOperator_commute_orbitProjection
    (N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJinv : Function.Involutive J) (Ω : H)
    (hJ : ∀ x : Algebra N, J (x.val Ω) = (star x).val Ω)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ R) :
    (Generator.vectorOrbitClosure R Ω).starProjection * conjugationOperator J u =
      conjugationOperator J u * (Generator.vectorOrbitClosure R Ω).starProjection := by
  apply Generator.starProjection_commutes_of_invariant
  · apply vectorOrbitClosure_invariant_of_orbit
    intro x
    let a : Algebra N := ⟨u, hRN hu⟩
    let b : Algebra N := ⟨x, hRN x.property⟩
    refine ⟨x * star (⟨u, hu⟩ : R), ?_⟩
    exact conjugationOperator_algebraVector N J Ω hJ a b
  · rw [conjugationOperator_star_unitary J hJinv u]
    apply vectorOrbitClosure_invariant_of_orbit
    intro x
    let a : Algebra N := ⟨star (u : H →L[ℂ] H), hRN (R.star_mem' hu)⟩
    let b : Algebra N := ⟨x, hRN x.property⟩
    refine ⟨x * (⟨u, hu⟩ : R), ?_⟩
    change conjugationOperator J (star (u : H →L[ℂ] H)) (x.val Ω) =
      (x.val * (u : H →L[ℂ] H)) Ω
    have h := conjugationOperator_algebraVector N J Ω hJ a b
    change conjugationOperator J (star (u : H →L[ℂ] H)) (x.val Ω) =
      (x.val * star (star (u : H →L[ℂ] H))) Ω at h
    simpa only [star_star] using h

/-- Equality of the two basic constructions transports a commutant member
which also commutes with their common projection. -/
theorem mem_commutant_of_equal_basicConstruction
    (M N : VonNeumannAlgebra H) (e q : H →L[ℂ] H)
    (hbasic : Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪ {e})) =
      Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪ {e})))
    (hq : q ∈ N.commutant) (he : e * q = q * e) : q ∈ M.commutant := by
  have hqN : q ∈ Set.centralizer ((N : Set (H →L[ℂ] H)) ∪ {e}) := by
    intro x hx
    rcases hx with hx | hx
    · exact VonNeumannAlgebra.mem_commutant_iff.mp hq x hx
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact he
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  have hxM : x ∈ Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪ {e})) := by
    intro b hb
    exact (hb x (Or.inl hx)).symm
  rw [hbasic] at hxM
  exact (hxM q hqN).symm

/-- The basic-construction equality gives the common right action for
every unitary of the common algebra, with no description of either full
commutant required. -/
theorem common_rightAction_of_equal_basicConstruction
    (M N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRM : R ≤ M.toStarSubalgebra) (hRN : R ≤ N.toStarSubalgebra)
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (hJ₂ : Function.Involutive J₂) (Ω : H)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ x : Algebra N, J₂ (x.val Ω) = (star x).val Ω)
    (hcyclic : DenseRange (fun x : Algebra M => x.val Ω))
    (hcyclicN : DenseRange (fun x : Algebra N => x.val Ω))
    (hbasic :
      Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
        {(Generator.vectorOrbitClosure R Ω).starProjection})) =
      Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
        {(Generator.vectorOrbitClosure R Ω).starProjection})))
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ R) :
    conjugationOperator J₁ u = conjugationOperator J₂ u := by
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector M Ω hcyclic
  · exact conjugationOperator_mem_commutant M J₁ Ω hM hcyclic ⟨u, hRM hu⟩
  · apply mem_commutant_of_equal_basicConstruction M N
      (Generator.vectorOrbitClosure R Ω).starProjection _ hbasic
    · exact conjugationOperator_mem_commutant N J₂ Ω hN hcyclicN ⟨u, hRN hu⟩
    · exact conjugationOperator_commute_orbitProjection N R hRN J₂ hJ₂ Ω hN u hu
  · exact conjugationOperator_common_vector M N J₁ J₂ Ω hM hN u (hRM hu) (hRN hu)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonPositionConjugationBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The tracial-conjugation bound in common position

The equality of basic constructions supplies the common right actions.
All left and right unitary actions used in the norm-768 estimate are
constructed here from the actual common subalgebra.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N R : VonNeumannAlgebra H}

/-- The norm-768 comparison with the common-action premises discharged by
the basic-construction equality. -/
theorem norm_tracialConjugations_sub_le_of_commonPosition
    (hRM : R ≤ M) (hRN : R ≤ N)
    (τ : FaithfulTracialState (Algebra M)) (hτ : FiniteVectorTrace τ)
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (htrace : ∀ x : Algebra M, ‖x.val Ω‖ = traceTwoNorm τ x)
    (hcyclicM : DenseRange (fun x : Algebra M => x.val Ω))
    (hcyclicN : DenseRange (fun x : Algebra N => x.val Ω))
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ x : Algebra N, J₂ (x.val Ω) = (star x).val Ω)
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (hbasic :
      Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
        {(Generator.vectorOrbitClosure R.toStarSubalgebra Ω).starProjection})) =
      Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
        {(Generator.vectorOrbitClosure R.toStarSubalgebra Ω).starProjection})))
    {b : ℝ} (hb : kkDistance M N < b) :
    ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ ≤ 768 * b := by
  let ι : Algebra M →ₗ[ℂ] H := Generator.vectorOrbitMap M.toStarSubalgebra Ω
  let φ : Algebra R →⋆ₐ[ℂ] Algebra M := coordinateInclusion hRM
  let L : unitary (Algebra R) → unitary (H →L[ℂ] H) :=
    fun u => Unitary.map (StarMonoidHom.ofClass R.toStarSubalgebra.subtype) u
  let Q : unitary (Algebra R) → unitary (H →L[ℂ] H) :=
    fun u => conjugationUnitary J₁ hJ₁ (star (L u))
  have hL (u : unitary (Algebra R)) (x : Algebra M) :
      ι (φ u * x) = (L u : H →L[ℂ] H) (ι x) := rfl
  have hQ (u : unitary (Algebra R)) (x : Algebra M) :
      ι (x * φ u) = (Q u : H →L[ℂ] H) (ι x) := by
    have hr := conjugationOperator_algebraVector M J₁ Ω hM (star (φ u)) x
    rw [star_star] at hr
    exact hr.symm
  have hright (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ R) :
      conjugationOperator J₁ u = conjugationOperator J₂ u :=
    common_rightAction_of_equal_basicConstruction M N R.toStarSubalgebra hRM hRN
      J₁ J₂ hJ₂ Ω hM hN hcyclicM hcyclicN hbasic u hu
  have hTL (u : unitary (Algebra R)) :
      Commute (tracialConjugationDefect J₁ J₂) (L u : H →L[ℂ] H) := by
    exact (tracialConjugationDefect_commute_both J₁ J₂ hJ₁ hJ₂ (L u)
      (hright (L u) (u : Algebra R).property)).1
  have hTQ (u : unitary (Algebra R)) :
      Commute (tracialConjugationDefect J₁ J₂) (Q u : H →L[ℂ] H) := by
    have hu : (star (L u) : H →L[ℂ] H) ∈ R :=
      R.toStarSubalgebra.star_mem' (u : Algebra R).property
    exact (tracialConjugationDefect_commute_both J₁ J₂ hJ₁ hJ₂ (star (L u))
      (hright (star (L u)) hu)).2
  exact norm_tracialConjugations_sub_le τ ι htrace hcyclicM hτ Ω hΩ
    (fun _ => rfl) J₁ J₂ hJ₁ hM hN φ hirr L Q hL hQ hTL hTQ hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearInclusionDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalizing strict near-inclusion approximants -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- An algebra approximant can be normalized into its unit ball with at
most twice the original error. -/
theorem exists_unitBall_approx_of_algebra_approx
    {x y : H →L[ℂ] H} (hx : ‖x‖ ≤ 1) (hy : y ∈ N) :
    ∃ z ∈ unitBall N, ‖x - z‖ ≤ 2 * ‖x - y‖ := by
  by_cases hy1 : ‖y‖ ≤ 1
  · exact ⟨y, ⟨hy, hy1⟩, by nlinarith [norm_nonneg (x - y)]⟩
  have hypos : 0 < ‖y‖ := by linarith
  let z : H →L[ℂ] H := (‖y‖⁻¹ : ℂ) • y
  have hznorm : ‖z‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hypos)
  have hyz : ‖y - z‖ = ‖y‖ - 1 := by
    have hi : 0 ≤ 1 - ‖y‖⁻¹ := by
      have ht : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hypos).mpr (lt_of_not_ge hy1).le
      linarith
    have he : y - z = ((1 - ‖y‖⁻¹ : ℝ) : ℂ) • y := by
      simp only [z, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
        sub_smul, one_smul]
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hypos.ne']
  have hnorm : ‖y‖ - 1 ≤ ‖x - y‖ := by
    have ht := norm_add_le (y - x) x
    rw [sub_add_cancel, norm_sub_rev] at ht
    linarith
  refine ⟨z, ⟨N.toStarSubalgebra.smul_mem hy _, hznorm.le⟩, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub x y z).trans (by rw [hyz]; linarith)

/-- The published strict near-inclusion convention controls the closed
unit balls with the factor two from normalization. -/
theorem exists_unitBall_approx_of_nearInclusion {γ : ℝ}
    (h : NearInclusion M N γ) {x : H →L[ℂ] H} (hx : x ∈ unitBall M) :
    ∃ y ∈ unitBall N, ‖x - y‖ < 2 * γ := by
  obtain ⟨γ', hγ', happrox⟩ := h
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff ⟨0, zero_mem N⟩).mp
    ((happrox x hx).trans_lt hγ')
  obtain ⟨z, hz, hxz⟩ := exists_unitBall_approx_of_algebra_approx hx.2 hy
  have hxy' : ‖x - y‖ < γ := by simpa only [dist_eq_norm] using hxy
  exact ⟨z, hz, hxz.trans_lt (by linarith)⟩

theorem kkDistance_le_two_mul_of_nearInclusions {γ : ℝ} (hγ : 0 ≤ γ)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    kkDistance M N ≤ 2 * γ := by
  apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx_of_nearInclusion hMN hx
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy.le⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx_of_nearInclusion hNM hx
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy.le⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StandardTracialPosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete standard tracial position

A faithful vector trace and cyclicity suffice to construct the standard
tracial conjugation. Its isometry and involution are proved rather than
included in the common-position input.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StandardTracialPosition

variable {M : VonNeumannAlgebra H} (p : StandardTracialPosition M)

theorem finiteVectorTrace : FiniteVectorTrace p.trace := by
  refine ⟨1, fun _ => p.vector, fun _ => p.vector, ?_⟩
  intro a
  simpa only [Fin.sum_univ_one] using p.trace_eq a

end StandardTracialPosition

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedCommonPosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published common tracial position input

This is the application-specific part of Cameron--Christensen--Sinclair--
Smith--White--Wiggins, *Kadison--Kastler stable factors*, Duke Math. J. 163
(2014), Lemma 4.10(i)--(iv),(vii), printed pp. 20--21,
arXiv:1209.4116v3. The constant is `50948 * sqrt g` and the hypothesis is
`g < 1.74 * 10^(-13)`.

We specialize their amenable subalgebra hypothesis to a scalar relative
commutant, which is the only case used here. The output records algebraic
equivalences onto the represented images and their actual vector traces.
No isomorphism between the two nearby factors is assumed.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CommonTracialPositionData

variable {M N R : VonNeumannAlgebra H} {hRM : R ≤ M} {hRN : R ≤ N} {g : ℝ}
  {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (d : CommonTracialPositionData M N R hRM hRN g K)

/-- The original relative commutant transfers through the faithful
representations and the common restriction. -/
theorem irreducible_left
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (x : Algebra d.left)
    (hx : ∀ r : Algebra d.common,
      coordinateInclusion d.common_le_left r * x = x * coordinateInclusion d.common_le_left r) :
    ∃ c : ℂ, x = c • (1 : Algebra d.left) := by
  have hcomm (r : Algebra R) :
      coordinateInclusion hRM r * d.leftEquiv.symm x =
        d.leftEquiv.symm x * coordinateInclusion hRM r := by
    apply d.leftEquiv.injective
    rw [map_mul, map_mul]
    change d.leftEquiv (coordinateInclusion hRM r) * d.leftEquiv (d.leftEquiv.symm x) =
      d.leftEquiv (d.leftEquiv.symm x) * d.leftEquiv (coordinateInclusion hRM r)
    rw [d.left_restrict, d.leftEquiv.apply_symm_apply]
    exact hx (d.commonEquiv r)
  obtain ⟨c, hc⟩ := hirr (d.leftEquiv.symm x) hcomm
  refine ⟨c, ?_⟩
  calc
    x = d.leftEquiv (d.leftEquiv.symm x) := (d.leftEquiv.apply_symm_apply x).symm
    _ = d.leftEquiv (c • (1 : Algebra M)) := congrArg d.leftEquiv hc
    _ = c • (1 : Algebra d.left) := by
      change d.leftEquiv.toAlgEquiv.toLinearMap (c • 1) = _
      rw [d.leftEquiv.toAlgEquiv.toLinearMap.map_smul]
      congr 1
      exact d.leftEquiv.map_one

theorem distance_le : kkDistance d.left d.right ≤ 2 * d.tolerance :=
  kkDistance_le_two_mul_of_nearInclusions d.tolerance_nonneg d.near_left d.near_right

/-- The common-position output supplies the full tracial-conjugation
estimate and its module structure. -/
theorem conjugations_sub_le_oai
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {b : ℝ} (hb : 2 * d.tolerance < b) :
    ‖(d.leftPosition.conjugation : K →L⋆[ℂ] K) -
      (d.rightPosition.conjugation : K →L⋆[ℂ] K)‖ ≤ 768 * b := by
  apply norm_tracialConjugations_sub_le_of_commonPosition
    d.common_le_left d.common_le_right d.leftPosition.trace d.leftPosition.finiteVectorTrace
    d.leftPosition.vector d.leftPosition.vector_norm d.leftPosition.vectorMap_norm
    d.leftPosition.cyclic
    (by
      change DenseRange (algebraVectorMap d.right d.leftPosition.vector)
      rw [d.same_vector]
      exact d.rightPosition.cyclic)
    d.leftPosition.conjugation d.rightPosition.conjugation
    d.leftPosition.conjugation_involutive d.rightPosition.conjugation_involutive
    d.leftPosition.conjugation_algebraVector
    (by simpa only [d.same_vector] using d.rightPosition.conjugation_algebraVector)
    (d.irreducible_left hirr) d.same_basicConstruction (d.distance_le.trans_lt hb)

end CommonTracialPositionData

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.CommonTracialPositionData.conjugations_sub_le_oai.{u} := @OAI.KadisonKastler.CommonTracialPositionData.conjugations_sub_le_oai.{u}
