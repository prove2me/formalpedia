-- Prove2me | solution 1 for OAI.KadisonKastler.exists_original_irreducible_matrix_algebra
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:41.797289+00:00
-- url     : https://prove2.me/submissions/131d3990-1aee-4803-b677-f9238ede380c

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
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
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
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
import Definitions.Def_OAIQ075A038
import Definitions.Def_Q260K029
import Definitions.Def_Q260K030
import Theorems.Thm_OAI_Generator_Tracial_traceFreeHilbertClosure_isII1Factor
import Theorems.Thm_OAI_KadisonKastler_FiniteVectorTrace_traceSeparable

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The canonical separable trace Hilbert realization

The trace completion provides the Hilbert-space norm estimates used
by boundary comparison.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Trace separability of the algebra makes any dense faithful trace
Hilbert realization separable. -/
theorem separableSpace_of_traceHilbert {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {τ : FaithfulTracialState (Algebra M)}
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hsep : TraceSeparable τ Set.univ) (hdense : DenseRange J) : SeparableSpace E := by
  obtain ⟨D, hDc, _, hD⟩ := hsep
  refine ⟨J '' D, hDc.image J, ?_⟩
  have hsub : Set.range J ⊆ closure (J '' D) := by
    rintro _ ⟨x, rfl⟩
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := hD x (Set.mem_univ x) ε hε
    refine ⟨J y, ⟨y, hy, rfl⟩, ?_⟩
    rw [dist_eq_norm, ← map_sub, hJ]
    exact hxy
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← hdense.closure_range]
  exact closure_minimal hsub isClosed_closure

/-- The trace Hilbert space of a separably acting II₁ factor is separable. -/
instance concreteTraceHilbert_separable [SeparableSpace H]
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    SeparableSpace (ConcreteTraceHilbert hM) :=
  separableSpace_of_traceHilbert (concreteTraceEmbedding hM) (concreteTraceEmbedding_norm hM)
    ((concreteFactorTrace_finiteVector hM).traceSeparable Set.univ)
    (concreteTraceEmbedding_denseRange hM)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IrreducibleMatrixSubfactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The irreducible matrix-generated subfactor

In a separable tracial representation, the existing matrix refinement
construction supplies the subfactor used in the finite stability argument.
No extra published existence hypothesis is introduced.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

/-- A concrete separable II₁ factor with its faithful vector trace contains
an irreducible II₁ subfactor generated by an increasing sequence of full
matrix algebras. -/
theorem exists_irreducible_matrix_subfactor
    (τ : UltrapowerBridge.TracialRepresentation M)
    (hM : IsII1Factor M.toStarSubalgebra) :
    ∃ (R : VonNeumannAlgebra H) (hRM : R ≤ M),
      IsII1Factor R.toStarSubalgebra ∧
      (∀ b : Algebra M,
        (∀ r : Algebra R, coordinateInclusion hRM r * b = b * coordinateInclusion hRM r) →
        ∃ c : ℂ, b = c • (1 : Algebra M)) ∧
      ∃ A : ℕ → FiniteMatrixStage M,
        R = FiniteMatrixStage.generatedVonNeumann A ∧
        Monotone (fun n => (A n).units.concreteAlgebra) ∧
        (∀ n, FiniteDimensional ℂ (A n).units.concreteAlgebra) := by
  have hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  have hirr : ∀ b : Algebra M,
      (∀ r : Algebra M, coordinateInclusion (le_refl M) r * b =
        b * coordinateInclusion (le_refl M) r) → ∃ c : ℂ, b = c • (1 : Algebra M) := by
    intro b hb
    exact traceHilbert_factor hM b hb
  obtain ⟨A, _, hmono, hfd, hII, _, hscalar⟩ :=
    FiniteMatrixStage.exists_irreducible_matrix_generated_II1 τ (le_refl M)
      (traceHilbert_factor hM) hM.diffuse hirr hsep
  refine ⟨FiniteMatrixStage.generatedVonNeumann A,
    FiniteMatrixStage.generatedVonNeumann_le A, hII, ?_, A, rfl, hmono, hfd⟩
  intro b hb
  refine ⟨τ.trace b, hscalar b ?_⟩
  intro r
  exact congrArg Subtype.val (hb r)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OriginalIrreducibleSubfactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pulling the increasing matrix construction to the original representation

The original representation need not possess a tracial vector. We construct
the matrix stages on the canonical separable trace Hilbert space, pull each
finite stage back algebraically, and take its actual original weak closure.
Commutation with that closure implies commutation with every pulled-back
stage and hence with the irreducible algebra in the trace representation.
Injectivity of the closure of the increasing matrix algebras is a hypothesis.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

section MatrixTransport

variable {A B : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A] [StarModule ℂ A]
  [Ring B] [StarRing B] [_root_.Algebra ℂ B] [StarModule ℂ B]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mapped_matrixUnits_hom (E : MatrixUnitSystem ι A) (f : A →⋆ₐ[ℂ] B)
    (a : Matrix ι ι ℂ) : (E.map f).hom a = f (E.hom a) := by
  simp only [MatrixUnitSystem.hom_apply, MatrixUnitSystem.map_entry,
    map_sum, map_smul]

theorem mem_inverse_mapped_matrixUnits (E : MatrixUnitSystem ι B)
    (e : A ≃⋆ₐ[ℂ] B) (x : A) :
    x ∈ (E.map e.symm.toStarAlgHom).algebra ↔ e x ∈ E.algebra := by
  constructor
  · rintro ⟨a, ha⟩
    change (E.map e.symm.toStarAlgHom).hom a = x at ha
    refine ⟨a, ?_⟩
    change E.hom a = e x
    rw [mapped_matrixUnits_hom] at ha
    change e.symm (E.hom a) = x at ha
    simpa only [e.apply_symm_apply] using congrArg e ha
  · rintro ⟨a, ha⟩
    change E.hom a = e x at ha
    refine ⟨a, ?_⟩
    change (E.map e.symm.toStarAlgHom).hom a = x
    rw [mapped_matrixUnits_hom]
    change e.symm (E.hom a) = x
    rw [ha, e.symm_apply_apply]

end MatrixTransport

section Commutation

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra K}

/-- Membership in the commutant of every increasing stage gives commutation
with the actual generated von Neumann algebra. -/
theorem commutes_generated_of_commutes_stages (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun j => (A j).units.concreteAlgebra)) (c : K →L[ℂ] K)
    (hc : ∀ j x, x ∈ (A j).units.concreteAlgebra → x * c = c * x)
    (x : Algebra (FiniteMatrixStage.generatedVonNeumann A)) :
    (x : K →L[ℂ] K) * c = c * (x : K →L[ℂ] K) := by
  have hc' : c ∈ Set.centralizer
      (FiniteMatrixStage.stageUnion A : Set (K →L[ℂ] K)) := by
    intro a ha
    rw [FiniteMatrixStage.stageUnion_coe A hA] at ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ha
    exact hc j a hj
  have hx : (x : K →L[ℂ] K) ∈ Set.centralizer (Set.centralizer
      (FiniteMatrixStage.stageUnion A : Set (K →L[ℂ] K))) := by
    rw [← bicommutantVonNeumann_coe]
    change (x : K →L[ℂ] K) ∈
      (bicommutantVonNeumann (FiniteMatrixStage.stageUnion A)).toStarSubalgebra
    rw [← wstar_starAlgebra_eq_bicommutant,
      ← FiniteMatrixStage.generated_eq_wstar_union A hA]
    exact x.property
  exact (hx c hc').symm

end Commutation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

/-- An irreducible, increasing matrix-generated subalgebra in the original
representation. No tracial vector in that representation is assumed. -/
theorem exists_original_irreducible_matrix_algebra_oai
    (hM : IsII1Factor M.toStarSubalgebra) :
    ∃ A : ℕ → FiniteMatrixStage M,
      Monotone (fun j => (A j).units.concreteAlgebra) ∧
      (∀ j, FiniteDimensional ℂ (A j).units.concreteAlgebra) ∧
      (∀ b : Algebra M,
        (∀ r : Algebra (FiniteMatrixStage.generatedVonNeumann A),
          coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) r * b =
            b * coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) r) →
        ∃ c : ℂ, b = c • (1 : Algebra M)) := by
  let K := ConcreteTraceHilbert hM
  let T : VonNeumannAlgebra K := traceFreeHilbertClosure (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  let e : Algebra M ≃⋆ₐ[ℂ] Algebra T := traceFreeHilbertEquiv (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  let τ : UltrapowerBridge.TracialRepresentation T :=
    traceFreeHilbertClosureTrace (traceHilbert_factor hM)
      hM.diffuse hM.finite (traceHilbert_nonzero hM)
  have hT : IsII1Factor T.toStarSubalgebra :=
    traceFreeHilbertClosure_isII1Factor (traceHilbert_factor hM)
      hM.diffuse hM.finite (traceHilbert_nonzero hM)
  obtain ⟨P, hPT, _, hirr, A, rfl, hA, _⟩ :=
    exists_irreducible_matrix_subfactor τ hT
  let B : ℕ → FiniteMatrixStage M := fun j => {
    size := (A j).size
    positive := (A j).positive
    units := (A j).units.map e.symm.toStarAlgHom }
  have hmem (j : ℕ) (x : Algebra M) :
      x.val ∈ (B j).units.concreteAlgebra ↔ (e x).val ∈ (A j).units.concreteAlgebra := by
    rw [(B j).units.mem_concreteAlgebra, (A j).units.mem_concreteAlgebra]
    exact mem_inverse_mapped_matrixUnits (A j).units e x
  have hB : Monotone (fun j => (B j).units.concreteAlgebra) := by
    intro i j hij x hx
    let xM : Algebra M := ⟨x, (B i).units.concreteAlgebra_le hx⟩
    exact (hmem j xM).mpr (hA hij ((hmem i xM).mp hx))
  refine ⟨B, hB, fun j => (B j).units.concrete_finiteDimensional, ?_⟩
  intro b hb
  have hstage (j : ℕ) (x : K →L[ℂ] K) (hx : x ∈ (A j).units.concreteAlgebra) :
      x * (e b).val = (e b).val * x := by
    let xT : Algebra T := ⟨x, (A j).units.concreteAlgebra_le hx⟩
    let xM : Algebra M := e.symm xT
    have hxM : xM.val ∈ (B j).units.concreteAlgebra := by
      apply (hmem j xM).mpr
      simpa only [xM, e.apply_symm_apply] using hx
    let xR : Algebra (FiniteMatrixStage.generatedVonNeumann B) :=
      ⟨xM.val, FiniteMatrixStage.stage_le_generated B j hxM⟩
    have hc : xM * b = b * xM := hb xR
    have he := congrArg e hc
    rw [map_mul, map_mul] at he
    have he' : e xM = xT := e.apply_symm_apply xT
    rw [he'] at he
    exact congrArg Subtype.val he
  obtain ⟨c, hc⟩ := hirr (e b) (fun r => Subtype.ext
    (commutes_generated_of_commutes_stages A hA (e b).val hstage r))
  refine ⟨c, e.injective ?_⟩
  calc
    e b = c • (1 : Algebra T) := hc
    _ = e (c • (1 : Algebra M)) := by
      have hs : e (c • (1 : Algebra M)) = c • e 1 :=
        e.toAlgEquiv.toLinearEquiv.map_smul c 1
      have h1 : e (1 : Algebra M) = 1 := e.map_one
      rw [hs, h1]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_original_irreducible_matrix_algebra_oai.{u_1} := @OAI.KadisonKastler.exists_original_irreducible_matrix_algebra_oai.{u_1}
