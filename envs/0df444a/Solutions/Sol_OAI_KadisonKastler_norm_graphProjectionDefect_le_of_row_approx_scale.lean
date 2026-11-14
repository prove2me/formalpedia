-- Prove2me | solution 1 for OAI.KadisonKastler.norm_graphProjectionDefect_le_of_row_approx_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:51:57.429391+00:00
-- url     : https://prove2.me/submissions/65044ae0-3aee-49f9-9b69-1e48bad0f001

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
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K071
import Definitions.Def_Q260K035
import Theorems.Thm_OAI_KadisonKastler_exists_bounded_graphRow_signal_scale
import Theorems.Thm_OAI_KadisonKastler_graphRowRMS_le_scale

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomizedRMS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Elementary norm bounds for finite random vectors -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {Ω H : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
/-- Pointwise norm domination passes through finite root mean squares. -/
theorem finiteRMS_mono (v w : Ω → H) (hv : ∀ i, ‖v i‖ ≤ ‖w i‖) :
    finiteRMS v ≤ finiteRMS w := by
  apply Real.sqrt_le_sqrt
  exact expect_le_expect (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledTomitaGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledGraphAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common unitary action on rescaled graphs

Left and right multiplication by common unitaries acts on graph vectors
through one unitary of the fixed two-coordinate Hilbert space. Thus each
closed graph reduces this unitary whenever the right action belongs to
the relevant commutant and has the prescribed value on the common vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem right_operator_on_algebra_vector
    (P : VonNeumannAlgebra H) (Ω : H) (a b : H →L[ℂ] H)
    (ha : a ∈ P.commutant) (x : Algebra P) (hΩ : a Ω = b Ω) :
    a (x.val Ω) = x.val (b Ω) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp ha x.val x.property
  calc
    a (x.val Ω) = x.val (a Ω) :=
      (congrArg (fun T : H →L[ℂ] H => T Ω) hc).symm
    _ = x.val (b Ω) := by rw [hΩ]

/-- Exact action on graph vectors, before any closure argument. -/
theorem rescaledGraphAction_vector
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (c : ℝ) (r s : unitary (H →L[ℂ] H))
    (hsright : conjugationOperator J (star (s : H →L[ℂ] H)) ∈ P.commutant)
    (hrright : conjugationOperator J (r : H →L[ℂ] H) ∈ P.commutant)
    (hsΩ : conjugationOperator J (star (s : H →L[ℂ] H)) Ω = (s : H →L[ℂ] H) Ω)
    (hrΩ : conjugationOperator J (r : H →L[ℂ] H) Ω = star (r : H →L[ℂ] H) Ω)
    (x : Algebra P) :
    (rescaledGraphAction J hJ r s :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c x.val) =
        rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (rescaledGraphAction J hJ r s :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) 0 =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) 0
    simp only [rescaledGraphAction, graphDiagonalUnitary_apply_zero,
      rescaledGraphVector_zero, Submonoid.coe_mul, mul_apply_eq_comp,
      conjugationUnitary_coe, Unitary.coe_star]
    rw [right_operator_on_algebra_vector P Ω _ _ hsright x hsΩ]
  · change (rescaledGraphAction J hJ r s :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) 1 =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) 1
    simp only [rescaledGraphAction, graphDiagonalUnitary_apply_one,
      rescaledGraphVector_one, conjugationUnitary_coe]
    rw [LinearMapClass.map_smul_of_tower]
    congr 1
    change J (star (s : H →L[ℂ] H)
      (conjugationOperator J (r : H →L[ℂ] H) (J (J (star x.val Ω))))) =
        J (star ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) Ω)
    rw [hJ]
    have hc := right_operator_on_algebra_vector P Ω _ _ hrright (star x) hrΩ
    change conjugationOperator J (r : H →L[ℂ] H) (star x.val Ω) =
      star x.val (star (r : H →L[ℂ] H) Ω) at hc
    rw [hc]
    simp only [star_mul, mul_apply_eq_comp]

/-- A bounded operator preserving defining graph vectors preserves the
closed graph subspace. -/
theorem rescaledGraphSubspace_invariant_of_vectors
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (hT : ∀ x : Algebra P, ∃ y : Algebra P,
      T (rescaledGraphVector J Ω c x.val) = rescaledGraphVector J Ω c y.val)
    {ξ : TomitaGraphHilbert H} (hξ : ξ ∈ rescaledGraphSubspace P J Ω c) :
    T ξ ∈ rescaledGraphSubspace P J Ω c := by
  have h : (rescaledGraphMap P J Ω c).range.topologicalClosure ≤
      (rescaledGraphSubspace P J Ω c).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hT x
      exact Submodule.le_topologicalClosure _ ⟨y, hy.symm⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact h hξ

/-- The common right-action identities make the graph reduce the
unitary implementing simultaneous left and right multiplication. -/
theorem rescaledGraphProjection_commutes
    (P : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRP : R ≤ P.toStarSubalgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (c : ℝ)
    (hcomm : ∀ a ∈ R, conjugationOperator J (star a) ∈ P.commutant)
    (hvector : ∀ a ∈ R, conjugationOperator J (star a) Ω = a Ω)
    (r s : unitary (H →L[ℂ] H))
    (hr : (r : H →L[ℂ] H) ∈ R) (hs : (s : H →L[ℂ] H) ∈ R) :
    rescaledGraphProjection P J Ω c *
        (rescaledGraphAction J hJ r s : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
      (rescaledGraphAction J hJ r s : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) *
        rescaledGraphProjection P J Ω c := by
  let U : unitary (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
    rescaledGraphAction J hJ r s
  have hformula (x : Algebra P) :
      (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) :=
    rescaledGraphAction_vector P J hJ Ω c r s (hcomm _ hs)
      (by simpa only [star_star] using hcomm _ (R.star_mem' hr)) (hvector _ hs)
      (by simpa only [star_star] using hvector _ (R.star_mem' hr)) x
  apply Generator.starProjection_commutes_of_invariant
  · apply rescaledGraphSubspace_invariant_of_vectors
    intro x
    exact ⟨⟨(r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H),
      P.mul_mem (P.mul_mem (hRP hr) x.property) (hRP hs)⟩, hformula x⟩
  · apply rescaledGraphSubspace_invariant_of_vectors
    intro x
    let y : Algebra P := ⟨star (r : H →L[ℂ] H) * x.val * star (s : H →L[ℂ] H),
      P.mul_mem (P.mul_mem (hRP (R.star_mem' hr)) x.property) (hRP (R.star_mem' hs))⟩
    have hm : (r : H →L[ℂ] H) * y.val * (s : H →L[ℂ] H) = x.val := by
      change (r : H →L[ℂ] H) *
        (star (r : H →L[ℂ] H) * x.val * star (s : H →L[ℂ] H)) *
          (s : H →L[ℂ] H) = x.val
      calc
        _ = ((r : H →L[ℂ] H) * star (r : H →L[ℂ] H)) * x.val *
            (star (s : H →L[ℂ] H) * (s : H →L[ℂ] H)) := by noncomm_ring
        _ = x.val := by rw [Unitary.mul_star_self_of_mem r.property,
          Unitary.star_mul_self_of_mem s.property, one_mul, mul_one]
    have hf := hformula y
    rw [hm] at hf
    have he := congrArg (fun ξ : TomitaGraphHilbert H =>
      star (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) ξ) hf
    change (star (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) *
      (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H))
        (rescaledGraphVector J Ω c y.val) =
          star (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
            (rescaledGraphVector J Ω c x.val) at he
    rw [Unitary.star_mul_self_of_mem U.property, one_apply_eq_self] at he
    exact ⟨y, he.symm⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphOrbitSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual orbit samples retaining the rescaled graph signal

The finite matrix moment estimate and the Hilbert sign selection are
combined here. The signal is the image of the graph vector under the
specified bounded operator; its invariance is derived from the common
unitary graph action.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- The defect between two graph projections commutes with every
common graph unitary that commutes with the two projections. -/
theorem graphProjectionDefect_commutes
    (P Q A : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (hP : P * A = A * P) (hQ : Q * A = A * Q) :
    ((1 - Q) * P) * A = A * ((1 - Q) * P) := by
  calc
    _ = (1 - Q) * (P * A) := mul_assoc _ _ _
    _ = (1 - Q) * (A * P) := by rw [hP]
    _ = (A - Q * A) * P := by noncomm_ring
    _ = (A - A * Q) * P := by rw [hQ]
    _ = _ := by simp only [mul_sub, sub_mul, one_mul, mul_assoc]

/-- In a common prepared position, the actual graph defect has the
required common matrix-orbit invariance. -/
theorem rescaledGraphProjectionDefect_commutes
    (M N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRM : R ≤ M.toStarSubalgebra) (hRN : R ≤ N.toStarSubalgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (c : ℝ)
    (hMcomm : ∀ a ∈ R, conjugationOperator J (star a) ∈ M.commutant)
    (hNcomm : ∀ a ∈ R, conjugationOperator J (star a) ∈ N.commutant)
    (hvector : ∀ a ∈ R, conjugationOperator J (star a) Ω = a Ω)
    (u v : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ R) (hv : (v : H →L[ℂ] H) ∈ R) :
    ((1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c) *
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
      (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) *
        ((1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c) :=
  graphProjectionDefect_commutes _ _ _
    (rescaledGraphProjection_commutes M R hRM J hJ Ω c hMcomm hvector u v hu hv)
    (rescaledGraphProjection_commutes N R hRN J hJ Ω c hNcomm hvector u v hu hv)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleDirection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.PointedMatrixSites.wordOperator_cons _root_.OAI.KadisonKastler.PointedMatrixSites.wordVector_cons _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugateOperatorMap_apply _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.graphCoordinateScale_one _root_.OAI.KadisonKastler.graphCoordinateScale_zero _root_.OAI.KadisonKastler.graphIsometry_one _root_.OAI.KadisonKastler.graphIsometry_zero _root_.OAI.KadisonKastler.graphReciprocalFlip_norm _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialMatrixAmplification_apply _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Directional graph bounds at all scales at least one

The integer row length is the ceiling of the squared scale. Both its
moment cost and its graph metric remain uniformly controlled.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]


theorem graphProjectionDefect_le_of_row_scale
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    {c : ℝ} {k : ℕ} (hk : 0 < k) (hck : c ^ 2 ≤ (k : ℝ)) {γ : ℝ} (hγ : 0 ≤ γ)
    (X Z : Fin k → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) (hZ : ∀ i, Z i ∈ N)
    (hXnorm : ‖operatorRow X‖ ≤ 131072)
    (happrox : ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖)
    (hsignal : ‖(1 - rescaledGraphProjection N J Ω (c)) *
        rescaledGraphProjection M J Ω (c)‖ / 16 ≤
      finiteRMS (fun i => ((1 - rescaledGraphProjection N J Ω (c)) *
        rescaledGraphProjection M J Ω (c))
          (rescaledGraphVector J Ω (c) (X i)))) :
    ‖(1 - rescaledGraphProjection N J Ω (c)) *
        rescaledGraphProjection M J Ω (c)‖ ≤
      (16 * Real.sqrt 2 * 131072) * γ := by
  let A := 1 - rescaledGraphProjection N J Ω (c)
  let T := A * rescaledGraphProjection M J Ω (c)
  have hAnorm : ‖A‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ (TomitaGraphHilbert H) -
      (rescaledGraphSubspace N J Ω (c)).starProjection‖ ≤ 1
    rw [← Submodule.starProjection_orthogonal]
    exact Submodule.starProjection_norm_le _
  have he (i : Fin k) :
      T (rescaledGraphVector J Ω (c) (X i)) =
        A (rescaledGraphVector J Ω (c) (X i - Z i)) := by
    have hp := rescaledGraphProjection_vector M J Ω (c) ⟨X i, hX i⟩
    have hq := rescaledGraphProjection_vector N J Ω (c) ⟨Z i, hZ i⟩
    have hs := (rescaledGraphOperatorMap J Ω (c)).map_sub (X i) (Z i)
    change rescaledGraphVector J Ω (c) (X i - Z i) =
      rescaledGraphVector J Ω (c) (X i) -
        rescaledGraphVector J Ω (c) (Z i) at hs
    dsimp [T]
    have hAz : A (rescaledGraphVector J Ω (c) (Z i)) = 0 := by
      dsimp [A]
      rw [sub_apply, one_apply_eq_self, hq, sub_self]
    rw [mul_apply_eq_comp, hp, hs, map_sub, hAz, sub_zero]
  have hrms : finiteRMS (fun i => T (rescaledGraphVector J Ω (c) (X i))) ≤
      finiteRMS (fun i => rescaledGraphVector J Ω (c) (X i - Z i)) := by
    apply finiteRMS_mono
    intro i
    rw [he]
    calc
      _ ≤ ‖A‖ * ‖rescaledGraphVector J Ω (c) (X i - Z i)‖ := A.le_opNorm _
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hAnorm
          (norm_nonneg (rescaledGraphVector J Ω (c) (X i - Z i)))
  have hrow : operatorRow (fun i => X i - Z i) = operatorRow X - operatorRow Z := by
    ext i j
    rfl
  have hmetric := graphRowRMS_le_scale hk J Ω hck (fun i => X i - Z i)
  rw [hrow, hΩ, mul_one] at hmetric
  have hdist : ‖operatorRow X - operatorRow Z‖ ≤ γ * 131072 :=
    happrox.trans (mul_le_mul_of_nonneg_left hXnorm hγ)
  have hfinal := hrms.trans (hmetric.trans
    (mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg 2)))
  change ‖T‖ / 16 ≤ _ at hsignal
  change ‖T‖ ≤ _
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]


theorem norm_graphProjectionDefect_le_of_row_approx_scale_oai
    (M N : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hcommM : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hcommN : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ N.commutant)
    (hEN : ∀ n, (E n).algebra ≤ N.toStarSubalgebra)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    {c : ℝ} (hc : 1 ≤ c) {γ : ℝ} (hγ : 0 ≤ γ)
    (happrox : ∀ k : ℕ, ∀ X : Fin k → H →L[ℂ] H, (∀ i, X i ∈ M) →
      ∃ Z : Fin k → H →L[ℂ] H, (∀ i, Z i ∈ N) ∧
        ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖) :
    ‖(1 - rescaledGraphProjection N J Ω (c)) *
        rescaledGraphProjection M J Ω (c)‖ ≤
      (16 * Real.sqrt 2 * 131072) * γ := by
  let k := Nat.ceil (c ^ 2)
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hck : c ^ 2 ≤ (k : ℝ) := Nat.le_ceil _
  have hk : 0 < k := by
    have hkR : 0 < (k : ℝ) := lt_of_lt_of_le (by linarith) hck
    exact_mod_cast hkR
  have hkc : (k : ℝ) ≤ 2 * c ^ 2 := by
    have hlt : (k : ℝ) < c ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg c)
    linarith
  let T := (1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c
  by_cases hT : T = 0
  · change ‖T‖ ≤ _
    rw [hT, norm_zero]
    positivity
  have hs : T * rescaledGraphProjection M J Ω c = T := by
    dsimp [T]
    have hid : rescaledGraphProjection M J Ω c * rescaledGraphProjection M J Ω c =
        rescaledGraphProjection M J Ω c :=
      (isStarProjection_starProjection (U := rescaledGraphSubspace M J Ω c)).isIdempotentElem.eq
    rw [mul_assoc, hid]
  obtain ⟨X, hX, hXnorm, hsignal⟩ := exists_bounded_graphRow_signal_scale M Ω hΩ d E hmono
    hEM hirr hcentral J hJ hc hk hck hkc T hT hs hcommM hvector (fun j u v hu hv =>
      rescaledGraphProjectionDefect_commutes M N (E j).algebra (hEM j) (hEN j)
        J hJ Ω c (hcommM j) (hcommN j) (hvector j) u v hu hv)
  obtain ⟨Z, hZ, hdist⟩ := happrox k X hX
  exact graphProjectionDefect_le_of_row_scale M N J Ω hΩ hk hck hγ X Z hX hZ hXnorm hdist hsignal


end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.norm_graphProjectionDefect_le_of_row_approx_scale_oai.{u_1} := @OAI.KadisonKastler.norm_graphProjectionDefect_le_of_row_approx_scale_oai.{u_1}
