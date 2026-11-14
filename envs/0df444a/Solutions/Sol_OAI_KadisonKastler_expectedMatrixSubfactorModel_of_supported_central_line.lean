-- Prove2me | solution 1 for OAI.KadisonKastler.expectedMatrixSubfactorModel_of_supported_central_line
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:58:55.032198+00:00
-- url     : https://prove2.me/submissions/487a65db-3078-4de4-abb6-fc7b9beafe5a

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.End
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
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
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
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
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
import Mathlib.Topology.Instances.ENNReal.Lemmas
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
import Definitions.Def_Q260K041
import Theorems.Thm_OAI_KadisonKastler_exists_symmetric_support_isometries
import Theorems.Thm_OAI_KadisonKastler_expectedMatrixSubfactorModel_of_centralizing_stages
import Theorems.Thm_OAI_KadisonKastler_matrixCentralVectorSpace_centralizes
import Theorems.Thm_OAI_KadisonKastler_supportCompressedMatrixUnits_centralizes
import Theorems.Thm_OAI_KadisonKastler_supportCompressedStages_irreducible
import Theorems.Thm_OAI_KadisonKastler_supportCompressedStages_mono

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralVectorMatrixLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central vectors of an increasing matrix sequence

The decreasing central-vector projections have an actual strong limit.
When their common range is a separating line, the state and commutant
identities supply the exact expected-subfactor model.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrixCentralVectorSpace_le
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (n : ℕ) :
    matrixCentralVectorSpace A J ≤ centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J :=
  iInf_le _ n

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorSupportProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Central vectors have supports commuting with their left algebra. -/
theorem vectorSupport_commutes_of_right_vectors (M N : VonNeumannAlgebra H)
    (hNM : N ≤ M) (ξ : H)
    (hright : ∀ a : Algebra N, ∃ b : Algebra M.commutant, a.val ξ = b.val ξ)
    (a : Algebra N) :
    (vectorSupportProjection M ξ).val.val * a.val =
      a.val * (vectorSupportProjection M ξ).val.val := by
  have hinv (a : Algebra N) : ∀ y ∈ vectorOrbitClosure M.commutant.toStarSubalgebra ξ,
      a.val y ∈ vectorOrbitClosure M.commutant.toStarSubalgebra ξ := by
    apply vectorOrbitClosure_invariant_of_orbit
    intro c
    obtain ⟨b,hb⟩ := hright a
    refine ⟨c * b, ?_⟩
    have hc := congrArg (fun T : H →L[ℂ] H => T ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp c.property a.val (hNM a.property))
    change a.val (c.val ξ) = c.val (a.val ξ) at hc
    simpa only [MulMemClass.coe_mul, mul_apply_eq_comp, hb] using hc
  exact starProjection_commutes_of_invariant
    (vectorOrbitClosure M.commutant.toStarSubalgebra ξ) a.val (hinv a) (by
    simpa only [StarMemClass.coe_star] using hinv (star a))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralVectorSupport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The support of a central vector commutes with the matrix stages -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centralVector_support_commutes (M N : VonNeumannAlgebra H)
    (hNM : N ≤ M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra N, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ centralVectorSpace N J) (a : Algebra N) :
    (vectorSupportProjection M ξ).val.val * a.val =
      a.val * (vectorSupportProjection M ξ).val.val := by
  apply vectorSupport_commutes_of_right_vectors M N hNM ξ _ a
  intro b
  exact ⟨⟨conjugationOperator J (star b).val,hright (star b)⟩,hξ b⟩

theorem matrixCentralVector_support_commutes {M : VonNeumannAlgebra H}
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ matrixCentralVectorSpace A J) (n : ℕ) (i j : Fin (A n).size) :
    (vectorSupportProjection M ξ).val.val * ((A n).units.entry i j).val =
      ((A n).units.entry i j).val * (vectorSupportProjection M ξ).val.val := by
  exact centralVector_support_commutes M (matrixUnitConcreteAlgebra (A n).units)
    (matrixUnitConcreteAlgebra_le (A n).units) J
    (fun a => hright (coordinateInclusion (matrixUnitConcreteAlgebra_le (A n).units) a))
    ξ (matrixCentralVectorSpace_le A J n hξ) ((concreteMatrixUnits (A n).units).entry i j)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralizerTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix-unit tests for a vector-state centralizer -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixUnits_vector_centralizes (E : MatrixUnitSystem ι (Algebra M)) (ξ : H)
    (h : ∀ i j (x : Algebra M),
      inner ℂ ξ ((E.entry i j * x).val ξ) = inner ℂ ξ ((x * E.entry i j).val ξ))
    (a x : Algebra M) (ha : a ∈ E.algebra) :
    inner ℂ ξ ((a * x).val ξ) = inner ℂ ξ ((x * a).val ξ) := by
  obtain ⟨b,rfl⟩ := E.mem_algebra a |>.mp ha
  simp only [Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, AddSubmonoidClass.coe_finsetSum,
    SetLike.val_smul, sum_apply, smul_apply, inner_sum, inner_smul_right,h]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SupportVectorTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moving a supported vector back to the original representation

Isometries onto its left and right supports turn a vector into a separating
and cyclic vector on the original Hilbert space. Only the concrete support
identities enter the proof.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem support_transfer_separating (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hv : star v * v = 1)
    (hvp : v.val * star v.val = (vectorSupportProjection M ξ).val.val)
    (hwξ : (w.val * star w.val) ξ = ξ) :
    ∀ a : Algebra M, a.val (star (v.val * w.val) ξ) = 0 → a = 0 := by
  intro a ha
  have hwa : a.val * w.val = w.val * a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp w.property a.val a.property
  have hwv : star v.val * (w.val * star w.val) =
      (w.val * star w.val) * star v.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp
      (M.commutant.mul_mem w.property (M.commutant.star_mem' w.property))
      (star v.val) (M.star_mem' v.property)
  have he : v.val * w.val * a.val * star (v.val * w.val) =
      (v.val * a.val * star v.val) * (w.val * star w.val) := by
    rw [star_mul]
    calc
      v.val * w.val * a.val * (star w.val * star v.val) =
          v.val * a.val * ((w.val * star w.val) * star v.val) := by
        rw [mul_assoc v.val w.val a.val, ← hwa]
        simp only [mul_assoc]
      _ = (v.val * a.val * star v.val) * (w.val * star w.val) := by
        rw [← hwv]
        simp only [mul_assoc]
  have hbξ : (v.val * a.val * star v.val) ξ = 0 := by
    have hzero : (v.val * w.val * a.val * star (v.val * w.val)) ξ = 0 := by
      change v.val (w.val (a.val (star (v.val * w.val) ξ))) = 0
      rw [ha,map_zero,map_zero]
    rw [he,mul_apply_eq_comp,hwξ] at hzero
    exact hzero
  have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
  have hb : v * a * star v = 0 := by
    apply vectorSupport_faithful_corner M ξ (v * a * star v) _ hbξ
    change (v.val * a.val * star v.val) * (vectorSupportProjection M ξ).val.val = _
    rw [← hvp]
    calc
      (v.val * a.val * star v.val) * (v.val * star v.val) =
          v.val * a.val * (star v.val * v.val) * star v.val := by simp only [mul_assoc]
      _ = v.val * a.val * star v.val := by rw [hv',mul_one]
  have h := congrArg (fun b : Algebra M => star v * b * v) hb
  simpa only [mul_assoc, ← mul_assoc (star v) v, hv, one_mul,
    mul_one, mul_zero, zero_mul] using h

theorem support_transfer_cyclic (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hw : star w * w = 1)
    (hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val)
    (hvξ : (v.val * star v.val) ξ = ξ) :
    DenseRange (algebraVectorMap M (star (v.val * w.val) ξ)) := by
  have hswap : v.val * w.val = w.val * v.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp w.property v.val v.property
  let v' : Algebra M.commutant.commutant :=
    ⟨v.val, by simpa only [M.commutant_commutant] using v.property⟩
  have hs := support_transfer_separating M.commutant ξ w v' hw hwq hvξ
  rw [← hswap] at hs
  have hd := commutant_orbit_dense M.commutant (star (v.val * w.val) ξ) hs
  change Dense (Set.range (fun a : Algebra M.commutant.commutant =>
    a.val (star (v.val * w.val) ξ))) at hd
  rw [VonNeumannAlgebra.commutant_commutant] at hd
  change Dense (Set.range (fun a : Algebra M => a.val (star (v.val * w.val) ξ)))
  exact hd

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SymmetricSupportTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Support isometries for a symmetric vector in a type III factor -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem support_transfer_norm (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hv : star v * v = 1) (hw : star w * w = 1)
    (hvp : v.val * star v.val = (vectorSupportProjection M ξ).val.val)
    (hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val) :
    ‖star (v.val * w.val) ξ‖ = ‖ξ‖ := by
  have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
  have hw' : star w.val * w.val = 1 := congrArg Subtype.val hw
  have hU : star (v.val * w.val) * (v.val * w.val) = 1 := by
    rw [star_mul]
    calc
      star w.val * star v.val * (v.val * w.val) =
          star w.val * (star v.val * v.val) * w.val := by simp only [mul_assoc]
      _ = 1 := by rw [hv',mul_one,hw']
  have hqv : (vectorSupportProjection M.commutant ξ).val.val * star v.val =
      star v.val * (vectorSupportProjection M.commutant ξ).val.val :=
    (VonNeumannAlgebra.mem_commutant_iff.mp
      (vectorSupportProjection M.commutant ξ).val.property
      (star v.val) (M.star_mem' v.property)).symm
  have hfix : (v.val * w.val) (star (v.val * w.val) ξ) = ξ := by
    change ((v.val * w.val) * star (v.val * w.val)) ξ = ξ
    rw [star_mul]
    have he : (v.val * w.val) * (star w.val * star v.val) =
        (v.val * star v.val) * (w.val * star w.val) := by
      calc
        _ = v.val * ((w.val * star w.val) * star v.val) := by simp only [mul_assoc]
        _ = _ := by rw [hwq,hqv]; simp only [mul_assoc]
    rw [he,hvp,hwq,mul_apply_eq_comp,vectorSupportProjection_apply,vectorSupportProjection_apply]
  exact (norm_apply_of_operator_isometry (v.val * w.val) hU _).symm.trans
    (congrArg norm hfix)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedFromCentralLine
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The expected subfactor from a nonfaithful central line

The support corner and its conjugate support restore a cyclic separating
vector on the original representation. Thus the central line need not
itself consist of separating vectors before the corner transfer.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {M : VonNeumannAlgebra H}

theorem expectedMatrixSubfactorModel_of_supported_central_line_oai
    (hM : TypeIIIFactor M) (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hunit : ‖ξ‖ = 1) (hJξ : J ξ = ξ)
    (hξ : ξ ∈ matrixCentralVectorSpace A J)
    (hline : matrixCentralVectorSpace A J ≤ Submodule.span ℂ {ξ}) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  have hne : ξ ≠ 0 := by
    intro h
    have h01 : (0 : ℝ) = 1 := by simpa only [h,norm_zero] using hunit
    exact zero_ne_one h01
  obtain ⟨v,w,hv,hw,hvp,hwq⟩ :=
    exists_symmetric_support_isometries M hM J hJ hleft hright ξ hJξ hne
  have hvp' : v * star v = (vectorSupportProjection M ξ).val := Subtype.ext hvp
  have hc (n : ℕ) (i j : Fin (A n).size) :
      (v * star v) * (A n).units.entry i j = (A n).units.entry i j * (v * star v) := by
    apply Subtype.ext
    change (v.val * star v.val) * ((A n).units.entry i j).val =
      ((A n).units.entry i j).val * (v.val * star v.val)
    rw [hvp]
    exact matrixCentralVector_support_commutes A J hleft ξ hξ n i j
  let B := supportCompressedStages A v hv hc
  let Ω := star (v.val * w.val) ξ
  have hn : ‖Ω‖ = 1 := (support_transfer_norm M ξ v w hv hw hvp hwq).trans hunit
  have hcyc : DenseRange (algebraVectorMap M Ω) :=
    support_transfer_cyclic M ξ v w hw hwq (by rw [hvp,vectorSupportProjection_apply])
  have hsep : Function.Injective (algebraVectorMap M Ω) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply support_transfer_separating M ξ v w hv hvp
      (by rw [hwq,vectorSupportProjection_apply]) (a - b)
    change a.val Ω - b.val Ω = 0
    exact sub_eq_zero.mpr hab
  apply expectedMatrixSubfactorModel_of_centralizing_stages B
    (supportCompressedStages_mono A v hv hc hA) Ω hn hcyc hsep
  · intro n a ha x
    let a' : Algebra M := ⟨a,matrixUnitConcreteAlgebra_le (B n).units ha⟩
    have hcA (i j : Fin (A n).size) (y : Algebra M) :
        inner ℂ ξ (((A n).units.entry i j * y).val ξ) =
          inner ℂ ξ ((y * (A n).units.entry i j).val ξ) :=
      matrixCentralVectorSpace_centralizes A J hJ hleft ξ hξ n _
        (((A n).units.mem_concreteAlgebra _).mpr ((A n).units.entry_mem i j)) y
    have hcB (i j : Fin (B n).size) (y : Algebra M) :
        inner ℂ Ω (((B n).units.entry i j * y).val Ω) =
          inner ℂ Ω ((y * (B n).units.entry i j).val Ω) :=
      supportCompressedMatrixUnits_centralizes (A n).units ξ hcA v w hv (hc n) hwq i j y
    exact matrixUnits_vector_centralizes (B n).units Ω hcB a' x
      (((B n).units.mem_concreteAlgebra a').mp ha)
  · exact supportCompressedStages_irreducible A J hleft ξ hξ hline v hv hvp' hc

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.expectedMatrixSubfactorModel_of_supported_central_line_oai.{u_1} := @OAI.KadisonKastler.expectedMatrixSubfactorModel_of_supported_central_line_oai.{u_1}
