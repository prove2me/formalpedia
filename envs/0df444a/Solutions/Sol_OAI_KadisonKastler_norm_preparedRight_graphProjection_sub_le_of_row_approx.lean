-- Prove2me | solution 1 for OAI.KadisonKastler.norm_preparedRight_graphProjection_sub_le_of_row_approx
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:16:33.259478+00:00
-- url     : https://prove2.me/submissions/ae648265-9613-48c5-a922-b171a4d8f0c7

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
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
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
import Definitions.Def_Q260K071
import Theorems.Thm_OAI_KadisonKastler_norm_graphProjectionDefect_le_of_row_approx_scale
import Theorems.Thm_OAI_KadisonKastler_relative_irreducibility_of_near_increasing_matrices

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedPairIrreducibility
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative irreducibility survives a nearby common matrix algebra

Finite signed-permutation averages over increasing matrix algebras have
bounded weak operator cluster points. Such a cluster point commutes with
every stage. Relative irreducibility in the first algebra makes it scalar;
the norm ball around a relative projection in the neighbor survives the
averages and their limit. No trace, invariant mean or averaging limit is
assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Commutation with all matrix stages extends to their generated von
Neumann algebra. -/
theorem commute_generated_of_commute_matrix_stages
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (T : H →L[ℂ] H)
    (hT : ∀ n a, a ∈ (E n).algebra → a * T = T * a) :
    ∀ a ∈ generatedVonNeumannAlgebra (⨆ n, (E n).algebra), a * T = T * a := by
  let C := StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
  have hEC : ∀ n, (E n).algebra ≤ C := by
    intro n a ha
    change a ∈ StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
    rw [StarSubalgebra.mem_centralizer_iff]
    intro t ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    refine ⟨(hT n a ha).symm, ?_⟩
    have he := congrArg star (hT n (star a) ((E n).algebra.star_mem' ha))
    simpa only [star_mul, star_star] using he
  let A : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n, (E n).algebra
  have hi : A ≤ C := iSup_le hEC
  have hc : T ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
    intro a ha
    have hh := hi ha
    change a ∈ StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) at hh
    rw [StarSubalgebra.mem_centralizer_iff] at hh
    exact (hh T (Set.mem_singleton T)).1.symm
  intro a ha
  change a ∈ (generatedVonNeumannAlgebra (⨆ n, (E n).algebra) :
    Set (H →L[ℂ] H)) at ha
  rw [generatedVonNeumannAlgebra_coe] at ha
  exact (ha T hc).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedPairState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common vector functional centralizes the shared algebra

Matching left and right vector actions, including their adjoints, gives
the centralizer identity directly by the Hilbert-space adjoint formula.
The source's common conjugation supplies these matches on unitaries;
the four-unitary span then gives every element of the common algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Matching a left operator and its adjoint on the vector with one
commutant operator proves the vector-functional centralizer identity. -/
theorem vector_functional_commutes_of_right_vector
    (N : VonNeumannAlgebra H) (Ω : H) (r s : H →L[ℂ] H)
    (hs : s ∈ N.commutant)
    (hvector : r Ω = s Ω) (hstar : (star r) Ω = (star s) Ω)
    (x : Algebra N) :
    inner ℂ Ω ((r * x.val) Ω) = inner ℂ Ω ((x.val * r) Ω) := by
  calc
    inner ℂ Ω ((r * x.val) Ω) = inner ℂ ((star r) Ω) (x.val Ω) := by
      simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ ((star s) Ω) (x.val Ω) := by rw [hstar]
    _ = inner ℂ Ω ((s * x.val) Ω) := by
      simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ Ω ((x.val * s) Ω) := by
      rw [← VonNeumannAlgebra.mem_commutant_iff.mp hs x.val x.property]
    _ = inner ℂ Ω ((x.val * r) Ω) := by
      simp only [mul_apply_eq_comp]
      rw [← hvector]

/-- It suffices to identify the right vector actions on unitaries of the
common algebra: these unitaries span every element. -/
theorem vector_functional_centralizes_of_right_unitaries
    (R N : VonNeumannAlgebra H) (hRN : R ≤ N) (Ω : H)
    (hright : ∀ u : unitary (Algebra R), ∃ s ∈ N.commutant,
      (u : Algebra R).val Ω = s Ω ∧
      (star (u : Algebra R)).val Ω = (star s) Ω)
    (r : Algebra R) (x : Algebra N) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  let ι : Algebra R →⋆ₐ[ℂ] Algebra N := StarSubalgebra.inclusion hRN
  let φ := Generator.Tracial.vectorFunctional (M := N) Ω
  let T : Algebra R →ₗ[ℂ] ℂ := φ.toLinearMap.comp
    ((LinearMap.mulRight ℂ x - LinearMap.mulLeft ℂ x).comp ι.toAlgHom.toLinearMap)
  have hT (u : unitary (Algebra R)) : ‖T (u : Algebra R)‖ ≤ 0 := by
    obtain ⟨s, hs, hv, hvs⟩ := hright u
    have he := vector_functional_commutes_of_right_vector N Ω
      (u : Algebra R).val s hs hv hvs x
    have hz : T (u : Algebra R) = 0 := by
      change inner ℂ Ω (((u : Algebra R).val * x.val - x.val * (u : Algebra R).val) Ω) = 0
      rw [sub_apply, inner_sub_right, he, sub_self]
    rw [hz, norm_zero]
  have hn := norm_le_twice_unitary_bound T hT r
  have hz : T r = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [mul_zero, zero_mul] using hn)
    (norm_nonneg _))
  change inner ℂ Ω ((r.val * x.val - x.val * r.val) Ω) = 0 at hz
  rw [sub_apply, inner_sub_right] at hz
  exact sub_eq_zero.mp hz

/-- The actual conjugate right algebra and central-vector relation in the
prepared-pair construction imply that the vector functional on `N`
centralizes `R`. -/
theorem vector_functional_centralizes_of_conjugate_right
    (R N : VonNeumannAlgebra H) (hRN : R ≤ N)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H)
    (hright : ∀ r : Algebra R, conjugationOperator J r.val ∈ N.commutant)
    (hcentral : ∀ r : Algebra R,
      r.val Ω = conjugationOperator J (star r).val Ω)
    (r : Algebra R) (x : Algebra N) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  apply vector_functional_centralizes_of_right_unitaries R N hRN Ω ?_ r x
  intro u
  let u₀ : unitary (H →L[ℂ] H) :=
    Unitary.map (StarMonoidHom.ofClass R.toStarSubalgebra.subtype) u
  refine ⟨conjugationOperator J (star (u : Algebra R)).val,
    hright (star (u : Algebra R)), hcentral (u : Algebra R), ?_⟩
  have hs : star (conjugationOperator J (star (u : Algebra R)).val) =
      conjugationOperator J (u : Algebra R).val := by
    change star (conjugationOperator J (star (u₀ : H →L[ℂ] H))) =
      conjugationOperator J (u₀ : H →L[ℂ] H)
    simpa only [Unitary.coe_star, star_star] using
      conjugationOperator_star_unitary J hJ (star u₀)
  rw [hs]
  simpa only [star_star] using hcentral (star (u : Algebra R))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledTomitaGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rescaled Tomita graphs in a fixed two-coordinate Hilbert space

A fixed conjugation identifies the conjugate copy of the Hilbert space
with the original one. In these coordinates the graph vector is
`(x Ω, c J (x* Ω))`. The same identification is used for both algebras.
No closability or modular spectral theorem is needed for the closed
linear graph subspace or the elementary projection comparison below.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem rescaledGraphProjection_vector (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) (x : Algebra P) :
    rescaledGraphProjection P J Ω c (rescaledGraphVector J Ω c x.val) =
      rescaledGraphVector J Ω c x.val :=
  (rescaledGraphSubspace P J Ω c).starProjection_eq_self_iff.mpr
    (rescaledGraphVector_mem P J Ω c x)

/-- A bound on the defining graph vectors extends to their actual closure. -/
theorem rescaledGraph_bound_on_closure
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (B : ℝ)
    (hB : ∀ x : Algebra P,
      ‖T (rescaledGraphVector J Ω c x.val)‖ ≤ B * ‖rescaledGraphVector J Ω c x.val‖)
    {ξ : TomitaGraphHilbert H} (hξ : ξ ∈ rescaledGraphSubspace P J Ω c) :
    ‖T ξ‖ ≤ B * ‖ξ‖ := by
  have hc : IsClosed {ξ : TomitaGraphHilbert H | ‖T ξ‖ ≤ B * ‖ξ‖} :=
    isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
  exact closure_minimal (by rintro _ ⟨x, rfl⟩; exact hB x) hc hξ

/-- A graph-vector estimate bounds the operator after graph projection. -/
theorem norm_comp_rescaledGraphProjection_le
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ x : Algebra P,
      ‖T (rescaledGraphVector J Ω c x.val)‖ ≤ B * ‖rescaledGraphVector J Ω c x.val‖) :
    ‖T * rescaledGraphProjection P J Ω c‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  change ‖T ((rescaledGraphSubspace P J Ω c).starProjection ξ)‖ ≤ B * ‖ξ‖
  exact (rescaledGraph_bound_on_closure P J Ω c T B hv
    ((rescaledGraphSubspace P J Ω c).starProjection_apply_mem ξ)).trans
    (mul_le_mul_of_nonneg_left
      ((rescaledGraphSubspace P J Ω c).norm_starProjection_apply_le ξ) hB)

private theorem norm_product_reverse_of_selfAdjoint {A : Type*}
    [NormedRing A] [StarRing A] [NormedStarGroup A]
    (x y : A) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : ‖x * y‖ = ‖y * x‖ := by
  calc
    _ = ‖star (x * y)‖ := (norm_star (x * y)).symm
    _ = _ := by rw [star_mul, hx.star_eq, hy.star_eq]

/-- Two directional graph-vector estimates give a uniform comparison
of the actual orthogonal graph projections. -/
theorem norm_rescaledGraphProjection_sub_le
    (P Q : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hPQ : ∀ x : Algebra P,
      ‖(1 - rescaledGraphProjection Q J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
        B * ‖rescaledGraphVector J Ω c x.val‖)
    (hQP : ∀ x : Algebra Q,
      ‖(1 - rescaledGraphProjection P J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
        B * ‖rescaledGraphVector J Ω c x.val‖) :
    ‖rescaledGraphProjection P J Ω c - rescaledGraphProjection Q J Ω c‖ ≤ 2 * B := by
  let EP : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H :=
    rescaledGraphProjection P J Ω c
  let EQ : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H :=
    rescaledGraphProjection Q J Ω c
  have h₁ : ‖(1 - EQ) * EP‖ ≤ B :=
    norm_comp_rescaledGraphProjection_le P J Ω c (1 - EQ) hB hPQ
  have h₂ : ‖(1 - EP) * EQ‖ ≤ B :=
    norm_comp_rescaledGraphProjection_le Q J Ω c (1 - EP) hB hQP
  have hEP : IsSelfAdjoint EP :=
    (isStarProjection_starProjection (U := rescaledGraphSubspace P J Ω c)).isSelfAdjoint
  have hEQ : IsSelfAdjoint EQ :=
    (isStarProjection_starProjection (U := rescaledGraphSubspace Q J Ω c)).isSelfAdjoint
  have hOne : IsSelfAdjoint (1 : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
    IsSelfAdjoint.one (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
  have hrev : ‖EQ * (1 - EP)‖ = ‖(1 - EP) * EQ‖ :=
    norm_product_reverse_of_selfAdjoint EQ (1 - EP) hEQ (hOne.sub hEP)
  calc
    ‖EP - EQ‖ = ‖(1 - EQ) * EP - EQ * (1 - EP)‖ := by
      congr 1
      simp only [mul_sub, sub_mul, mul_one, one_mul]
      abel
    _ ≤ ‖(1 - EQ) * EP‖ + ‖EQ * (1 - EP)‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add h₁ (hrev.le.trans h₂)
    _ = 2 * B := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphReciprocal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reciprocal rescaling of closed Tomita graphs

Conjugating and interchanging the two coordinates sends the graph at c
to the graph at 1/c. This norm-preserving real-linear map transfers the
directional estimates to small positive scales.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Exact reciprocal graph formula on the defining algebra vectors. -/
theorem graphReciprocalFlip_vector (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) {c : ℝ} (hc : c ≠ 0) (x : H →L[ℂ] H) :
    graphReciprocalFlip J (rescaledGraphVector J Ω c x) =
      c • rescaledGraphVector J Ω c⁻¹ (star x) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change J (c • J (star x Ω)) = c • (star x Ω)
    rw [conjugation_real_smul, hJ]
  · change J (x Ω) = c • (c⁻¹ • J (star (star x) Ω))
    rw [star_star, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The reciprocal symmetry maps the entire closed graph to the
reciprocal closed graph, by continuity. -/
theorem graphReciprocalFlip_mem (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) {ξ : TomitaGraphHilbert H}
    (hξ : ξ ∈ rescaledGraphSubspace P J Ω c) :
    graphReciprocalFlip J ξ ∈ rescaledGraphSubspace P J Ω c⁻¹ := by
  have hh : IsClosed {v : TomitaGraphHilbert H |
      graphReciprocalFlip J v ∈ rescaledGraphSubspace P J Ω c⁻¹} :=
    (Submodule.isClosed_topologicalClosure _).preimage (graphReciprocalFlip J).continuous
  apply closure_minimal (s := Set.range (rescaledGraphMap P J Ω c)) ?_ hh hξ
  rintro _ ⟨x, rfl⟩
  change graphReciprocalFlip J (rescaledGraphVector J Ω c x.val) ∈
    rescaledGraphSubspace P J Ω c⁻¹
  rw [graphReciprocalFlip_vector J hJ Ω hc]
  exact (rescaledGraphSubspace P J Ω c⁻¹).smul_mem c
    (rescaledGraphVector_mem P J Ω c⁻¹ (star x))

private theorem norm_sub_projection_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (S : Submodule ℂ K) [S.HasOrthogonalProjection] (ξ η : K) (hη : η ∈ S) :
    ‖ξ - S.starProjection ξ‖ ≤ ‖ξ - η‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨η, hη⟩ : S)

private theorem graph_distance_le (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) (ξ η : TomitaGraphHilbert H)
    (hη : η ∈ rescaledGraphSubspace P J Ω c) :
    ‖(1 - rescaledGraphProjection P J Ω c) ξ‖ ≤ ‖ξ - η‖ := by
  change ‖ξ - (rescaledGraphSubspace P J Ω c).starProjection ξ‖ ≤ _
  exact norm_sub_projection_le _ ξ η hη

/-- A directional vector bound at the reciprocal scale gives the same
bound at the original positive scale. -/
theorem graph_directional_reciprocal
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) {c : ℝ} (hc : 0 < c) {B : ℝ}
    (hbound : ∀ x : Algebra M,
      ‖(1 - rescaledGraphProjection N J Ω c⁻¹) (rescaledGraphVector J Ω c⁻¹ x.val)‖ ≤
        B * ‖rescaledGraphVector J Ω c⁻¹ x.val‖)
    (x : Algebra M) :
    ‖(1 - rescaledGraphProjection N J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
      B * ‖rescaledGraphVector J Ω c x.val‖ := by
  let ξ := rescaledGraphVector J Ω c⁻¹ (star x.val)
  let q := rescaledGraphProjection N J Ω c⁻¹ ξ
  have hq : q ∈ rescaledGraphSubspace N J Ω c⁻¹ :=
    (rescaledGraphSubspace N J Ω c⁻¹).starProjection_apply_mem ξ
  have hfq : graphReciprocalFlip J q ∈ rescaledGraphSubspace N J Ω c := by
    simpa only [inv_inv] using graphReciprocalFlip_mem N J hJ Ω (inv_ne_zero (ne_of_gt hc)) hq
  have hflip : c • graphReciprocalFlip J ξ = rescaledGraphVector J Ω c x.val := by
    dsimp [ξ]
    rw [graphReciprocalFlip_vector J hJ Ω (inv_ne_zero (ne_of_gt hc)), inv_inv,
      star_star, smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
  have hnorm : c * ‖ξ‖ = ‖rescaledGraphVector J Ω c x.val‖ := by
    rw [← hflip, norm_smul, Real.norm_eq_abs, abs_of_pos hc, graphReciprocalFlip_norm]
  have hd := graph_distance_le N J Ω c (rescaledGraphVector J Ω c x.val)
    (c • graphReciprocalFlip J q) ((rescaledGraphSubspace N J Ω c).smul_mem c hfq)
  have he : ‖rescaledGraphVector J Ω c x.val - c • graphReciprocalFlip J q‖ = c * ‖ξ - q‖ := by
    rw [← hflip, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      graphReciprocalFlip_norm]
  rw [he] at hd
  have hb := hbound (star x)
  change ‖ξ - q‖ ≤ B * ‖ξ‖ at hb
  calc
    _ ≤ c * ‖ξ - q‖ := hd
    _ ≤ c * (B * ‖ξ‖) := mul_le_mul_of_nonneg_left hb hc.le
    _ = B * ‖rescaledGraphVector J Ω c x.val‖ := by rw [← hnorm]; ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformGraphComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform comparison of the two rescaled graph projections

Directional bounds proved at scales at least one extend to every
positive scale by the reciprocal graph symmetry. The two directions
then bound the norm of the difference of orthogonal projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The norm of a directional projection product bounds all defining
graph vectors in that direction. -/
theorem graph_directional_vector_le_of_norm
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c B : ℝ)
    (hbound : ‖(1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c‖ ≤ B)
    (x : Algebra M) :
    ‖(1 - rescaledGraphProjection N J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
      B * ‖rescaledGraphVector J Ω c x.val‖ := by
  have he : ((1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c)
      (rescaledGraphVector J Ω c x.val) =
      (1 - rescaledGraphProjection N J Ω c) (rescaledGraphVector J Ω c x.val) := by
    rw [mul_apply_eq_comp, rescaledGraphProjection_vector M J Ω c x]
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))

/-- A large-scale directional bound controls every positive scale. -/
theorem graph_directional_all_positive
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (B : ℝ)
    (hlarge : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c‖ ≤ B)
    {c : ℝ} (hc : 0 < c) (x : Algebra M) :
    ‖(1 - rescaledGraphProjection N J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
      B * ‖rescaledGraphVector J Ω c x.val‖ := by
  by_cases hc1 : 1 ≤ c
  · exact graph_directional_vector_le_of_norm M N J Ω c B (hlarge c hc1) x
  · have hi : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr (le_of_not_ge hc1)
    exact graph_directional_reciprocal M N J hJ Ω hc
      (graph_directional_vector_le_of_norm M N J Ω c⁻¹ B (hlarge c⁻¹ hi)) x

/-- Two large-scale directional estimates give a uniform norm estimate
for the actual closed graph projections at every positive scale. -/
theorem uniform_rescaledGraphProjection_comparison
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) {B : ℝ} (hB : 0 ≤ B)
    (hMN : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c‖ ≤ B)
    (hNM : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection M J Ω c) * rescaledGraphProjection N J Ω c‖ ≤ B)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ 2 * B :=
  norm_rescaledGraphProjection_sub_le M N J Ω c hB
    (graph_directional_all_positive M N J hJ Ω B hMN hc)
    (graph_directional_all_positive N M J hJ Ω B hNM hc)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedGraphRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prepared graph comparison from individual row approximants

Only a separate nearby row is required for each finite row in either
algebra. No global linear map selecting those approximants is assumed.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedGraphRowsOrder_r308a11_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedGraphRowsStarOrder_r308a11_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.KadisonKastler.preparedGraphRowsOperatorStarOrder
/-- Common matrix actions and two-sided individual row approximation
imply the uniform comparison of every positively rescaled closed graph. -/
theorem norm_prepared_rescaledGraphProjection_sub_le_of_row_approx
    (M N : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hEN : ∀ n, (E n).algebra ≤ N.toStarSubalgebra)
    (hirrM : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hirrN : ∀ A ∈ N, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hcentralM : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (hcentralN : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ N,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hcommM : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hcommN : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ N.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hMN : GraphRowApproximation M N γ) (hNM : GraphRowApproximation N M γ)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤
      (32 * Real.sqrt 2 * 131072) * γ := by
  have hb : 0 ≤ (16 * Real.sqrt 2 * 131072) * γ := by positivity
  have hMN : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c‖ ≤
        (16 * Real.sqrt 2 * 131072) * γ := by
    intro c hc
    exact norm_graphProjectionDefect_le_of_row_approx_scale M N Ω hΩ d E hmono hEM
      hirrM hcentralM J hJ hcommM hcommN hEN hvector hc hγ
      hMN
  have hNM : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection M J Ω c) * rescaledGraphProjection N J Ω c‖ ≤
        (16 * Real.sqrt 2 * 131072) * γ := by
    intro c hc
    exact norm_graphProjectionDefect_le_of_row_approx_scale N M Ω hΩ d E hmono hEN
      hirrN hcentralN J hJ hcommN hcommM hEM hvector hc hγ
      hNM
  have h := uniform_rescaledGraphProjection_comparison M N J hJ Ω hb hMN hNM hc
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedRightGraphBridge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prepared graph comparison from common right actions

The vector and conjugation identities are imposed only on the
shared increasing matrix algebra. In particular, no tracial state on either
ambient algebra is needed. The relative right-action data imply the required
centralizer identities, and matrix averaging transfers relative irreducibility
to the nearby algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedRightGraphOrder_r308a11_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightGraphStarOrder_r308a11_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance preparedRightGraphOperatorOrder_r308a11_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightGraphOperatorStarOrder_r308a11_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- Right multiplication on the common algebra implies centralization of
the vector functional, without any trace hypothesis on the ambient algebra. -/
theorem vector_functional_centralizes_of_commonRight
    (R N : VonNeumannAlgebra H) (hRN : R ≤ N)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H)
    (hright : ∀ r ∈ R, conjugationOperator J r ∈ N.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    (r : Algebra R) (x : Algebra N) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  apply vector_functional_centralizes_of_conjugate_right R N hRN J hJ Ω
  · intro a
    exact hright a.val a.property
  · intro a
    exact (hvector a.val a.property).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedRightGraphRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prepared right actions with individual row approximants

The finite matrix and common right-action arguments do not require a
linear choice of nearby operators. These variants retain only the actual
finite-row approximations supplied by matrix unit-ball proximity.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedRightRowsOrder_r308a11_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightRowsStarOrder_r308a11_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance preparedRightRowsOperatorOrder_r308a11_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightRowsOperatorStarOrder_r308a11_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- Common right-action identities give all graph comparison hypotheses;
individual row approximants suffice for the remaining analytic step. -/
theorem norm_preparedRight_graphProjection_sub_le_of_row_approx_oai
    (M N R : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hirr : ∀ A ∈ M, (∀ a ∈ R, a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2)
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hrightN : ∀ r ∈ R, conjugationOperator J r ∈ N.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hMN : GraphRowApproximation M N γ) (hNM : GraphRowApproximation N M γ)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤
      (32 * Real.sqrt 2 * 131072) * γ := by
  have hER (n : ℕ) : (E n).algebra ≤ R.toStarSubalgebra := by
    intro a ha
    rw [hR]
    exact subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun n => (E n).algebra) n) ha)
  have hEM (n : ℕ) : (E n).algebra ≤ M.toStarSubalgebra :=
    fun _ ha => hRM (hER n ha)
  have hEN (n : ℕ) : (E n).algebra ≤ N.toStarSubalgebra :=
    fun _ ha => hRN (hER n ha)
  have hirrM : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H) := by
    intro A hAM hA
    apply hirr A hAM
    rw [hR]
    exact commute_generated_of_commute_matrix_stages d E A hA
  have hirrNg := relative_irreducibility_of_near_increasing_matrices M N d E hmono hEM
    (by simpa only [← hR] using hirr) hgap
  have hirrN : ∀ A ∈ N, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H) := by
    intro A hAN hA
    exact hirrNg A hAN (commute_generated_of_commute_matrix_stages d E A hA)
  have hcommM : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant := by
    intro j a ha
    exact hrightM (star a) (R.toStarSubalgebra.star_mem' (hER j ha))
  have hcommN : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ N.commutant := by
    intro j a ha
    exact hrightN (star a) (R.toStarSubalgebra.star_mem' (hER j ha))
  have hvectorE : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω := by
    intro j a ha
    exact hvector a (hER j ha)
  have hcentralM : ∀ j a, a ∈ (E j).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω) := by
    intro j a ha z hz
    exact vector_functional_centralizes_of_commonRight R M hRM J hJ Ω hrightM hvector
      ⟨a, hER j ha⟩ ⟨z, hz⟩
  have hcentralN : ∀ j a, a ∈ (E j).algebra → ∀ z ∈ N,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω) := by
    intro j a ha z hz
    exact vector_functional_centralizes_of_commonRight R N hRN J hJ Ω hrightN hvector
      ⟨a, hER j ha⟩ ⟨z, hz⟩
  exact norm_prepared_rescaledGraphProjection_sub_le_of_row_approx M N Ω hΩ d E hmono
    hEM hEN hirrM hirrN hcentralM hcentralN J hJ hcommM hcommN hvectorE
    hγ hMN hNM hc

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.norm_preparedRight_graphProjection_sub_le_of_row_approx_oai.{u_1} := @OAI.KadisonKastler.norm_preparedRight_graphProjection_sub_le_of_row_approx_oai.{u_1}
