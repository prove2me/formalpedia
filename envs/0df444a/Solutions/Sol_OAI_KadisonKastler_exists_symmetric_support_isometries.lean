-- Prove2me | solution 1 for OAI.KadisonKastler.exists_symmetric_support_isometries
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:02.52959+00:00
-- url     : https://prove2.me/submissions/b1bb466a-e4b9-4cb2-bca0-8203c102da1d

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
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
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
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K066
import Definitions.Def_Q260K032

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorSupportProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateVectorSupport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugate supports of a symmetric vector

For a conjugation interchanging an algebra and its commutant, the two
support projections of a fixed vector are conjugate. This is the support
identity used when passing the central-vector construction to a full corner.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conjugateAlgebraProjection_fixes (M N : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hMN : ∀ a : Algebra M, conjugationOperator J a.val ∈ N)
    (p : AlgebraProjection M) (ξ : H) (hξ : J ξ = ξ) (hp : p.val.val ξ = ξ) :
    (conjugateAlgebraProjection M N J hJ hMN p).val.val ξ = ξ := by
  change J (p.val.val (J ξ)) = ξ
  rw [hξ,hp,hξ]

theorem vectorSupportProjection_conjugate (M : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ) :
    (vectorSupportProjection M.commutant ξ).val.val =
      conjugationOperator J (vectorSupportProjection M ξ).val.val := by
  let p := vectorSupportProjection M ξ
  let q := vectorSupportProjection M.commutant ξ
  have hqp : q.val.val * conjugationOperator J p.val.val = q.val.val :=
    vectorSupport_minimal M.commutant ξ (conjugateAlgebraProjection M M.commutant J hJ hleft p)
      (conjugateAlgebraProjection_fixes M M.commutant J hJ hleft p ξ hξ
        (vectorSupportProjection_apply M ξ))
  have hpq : p.val.val * conjugationOperator J q.val.val = p.val.val :=
    vectorSupport_minimal M ξ (conjugateAlgebraProjection M.commutant M J hJ hright q)
      (conjugateAlgebraProjection_fixes M.commutant M J hJ hright q ξ hξ
        (vectorSupportProjection_apply M.commutant ξ))
  have hqp' := congrArg star hqp
  have hs : star q.val.val = q.val.val := congrArg Subtype.val q.property.isSelfAdjoint.star_eq
  have ht : star p.val.val = p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  rw [star_mul, ← conjugationOperator_star J hJ, ht, hs] at hqp'
  have hpq' := congrArg (conjugationOperator J) hpq
  rw [conjugationOperator_mul J hJ, conjugationOperator_twice J hJ] at hpq'
  exact hqp'.symm.trans hpq'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteFactorProperInfiniteness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # An infinite factor is properly infinite

A proper isometry supplies an infinite orthogonal sequence of equivalent
wandering projections.  A maximal orthogonal family of partial isometries
with sources under the first wandering projection covers the identity by
factoriality.  Separability makes this family countable, so its ranges can
be mapped into the even and odd wandering projections separately.

No trace, dimension function, or published projection comparison is used.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem projection_fixed_vectors_orthogonal (p q : AlgebraProjection M)
    (hpq : p.val * q.val = 0) (x y : H)
    (hx : (p.val : H →L[ℂ] H) x = x) (hy : (q.val : H →L[ℂ] H) y = y) :
    inner ℂ x y = 0 := by
  have hstar : star (p.val : H →L[ℂ] H) = (p.val : H →L[ℂ] H) :=
    congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  calc
    inner ℂ x y = inner ℂ ((p.val : H →L[ℂ] H) x)
        ((q.val : H →L[ℂ] H) y) := by rw [hx, hy]
    _ = inner ℂ x ((p.val : H →L[ℂ] H) ((q.val : H →L[ℂ] H) y)) := by
      conv_lhs => rw [← hstar]
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = 0 := by
      have hz := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) y) hpq
      change (p.val : H →L[ℂ] H) ((q.val : H →L[ℂ] H) y) = 0 at hz
      rw [hz, inner_zero_right]

/-- A nonzero projection has a unit vector in its range. -/
private theorem projection_unit_vector (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ x : H, ‖x‖ = 1 ∧ (p.val : H →L[ℂ] H) x = x := by
  have hn : (p.val : H →L[ℂ] H) ≠ 0 := fun h => hp (Subtype.ext h)
  obtain ⟨x, hx⟩ : ∃ x : H, (p.val : H →L[ℂ] H) x ≠ 0 := by
    by_contra h
    apply hn
    ext x
    simpa using (not_exists.mp h x)
  let y := (p.val : H →L[ℂ] H) x
  have hy : y ≠ 0 := hx
  have hnorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  refine ⟨((‖y‖ : ℂ)⁻¹) • y, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg y), inv_mul_cancel₀ hnorm]
  · rw [map_smul]
    congr 1
    change (p.val : H →L[ℂ] H) ((p.val : H →L[ℂ] H) x) =
      (p.val : H →L[ℂ] H) x
    exact congrArg (fun a : Algebra M => (a : H →L[ℂ] H) x)
      p.property.isIdempotentElem.eq

/-- Pairwise orthogonal nonzero projections in a separably acting algebra
form a countable family. -/
theorem countable_of_orthogonal_nonzero_projections [TopologicalSpace.SeparableSpace H]
    {ι : Type*} (p : ι → AlgebraProjection M)
    (hp : ∀ i, (p i).val ≠ 0)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) : Countable ι := by
  choose x hnorm hfix using fun i => projection_unit_vector (p i) (hp i)
  apply Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (x i) (1 / 2 : ℝ))
  · intro i j hij
    apply Metric.ball_disjoint_ball
    have hi := projection_fixed_vectors_orthogonal (p i) (p j) (ho hij)
      (x i) (x j) (hfix i) (hfix j)
    have he := @norm_sub_mul_self ℂ H _ _ _ (x i) (x j)
    simp only [hi, map_zero, hnorm] at he
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x i - x j)]
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨x i, Metric.mem_ball_self (by norm_num)⟩

private theorem exists_maximal_sourceFamily (p : AlgebraProjection M) :
    ∃ s : Set (PartialIsometry M), Maximal (sourceFamily p) s := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
  constructor
  · intro v hv
    obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
    exact (hc hs).1 v hvs
  · intro v hv w hw hvw
    obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
    obtain ⟨t, ht, hwt⟩ := Set.mem_sUnion.mp hw
    rcases hchain.total hs ht with hst | hts
    · exact (hc ht).2 (hst hvs) hwt hvw
    · exact (hc hs).2 hvs (hts hwt) hvw

private theorem target_ne_zero_of_support_ne_zero (v : PartialIsometry M)
    (hv : v.support.val ≠ 0) : v.target.val ≠ 0 := by
  intro hz
  have he := v.target_mul
  rw [hz, zero_mul] at he
  have hi := v.initial
  rw [← he, star_zero, zero_mul] at hi
  exact hv hi.symm

/-- Every nonzero projection in a countably decomposable factor supplies a
countable partition of the identity by ranges of partial isometries whose
initial projections lie under the supplied projection. -/
theorem exists_countable_source_partition_of_projection_countability
    (hFamilies : HasCountableProjectionFamilies M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support ≤ p) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) ∧
      (∀ q : AlgebraProjection M, (∀ n, (a n).target ≤ q) →
        (1 : Algebra M) = q.val) := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_sourceFamily p
  have hcount : Countable s := hFamilies s
    (fun v : s => v.val.target)
    (fun v => target_ne_zero_of_support_ne_zero v.val ((hs.1 v.val v.property).2))
    (fun v w hvw => hs.2 v.property w.property (fun he => hvw (Subtype.ext he)))
  let : Encodable s := @Encodable.ofCountable s hcount
  let a (n : ℕ) : PartialIsometry M :=
    (Encodable.decode₂ s n).elim PartialIsometry.zero (fun v => v.val)
  have ha (v : s) : a (Encodable.encode v) = v.val := by
    simp only [a, Encodable.decode₂_encode, Option.elim_some]
  have has (n : ℕ) : a n = PartialIsometry.zero ∨ a n ∈ s := by
    unfold a
    cases h : Encodable.decode₂ s n with
    | none => exact Or.inl rfl
    | some v => exact Or.inr v.property
  have hap (n : ℕ) : (a n).support ≤ p := by
    rcases has n with h | h
    · rw [h]
      change p.val * 0 = 0
      exact mul_zero _
    · exact (hs.1 _ h).1
  have hao : Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) := by
    intro i j hij
    unfold a
    cases hi : Encodable.decode₂ s i with
    | none => simp [PartialIsometry.zero, PartialIsometry.target]
    | some v =>
      cases hj : Encodable.decode₂ s j with
      | none => simp [PartialIsometry.zero, PartialIsometry.target]
      | some w =>
        apply hs.2 v.property w.property
        intro hvw
        have hvwe : v = w := Subtype.ext hvw
        have hvi := Encodable.decode₂_eq_some.mp hi
        have hwj := Encodable.decode₂_eq_some.mp hj
        exact hij (hvi.symm.trans (congrArg Encodable.encode hvwe |>.trans hwj))
  refine ⟨a, hap, hao, ?_⟩
  intro q hq
  by_contra hne
  let r := projectionComplement q
  have hr : r.val ≠ 0 := by
    change 1 - q.val ≠ 0
    exact sub_ne_zero.mpr hne
  obtain ⟨v, hvp, hvr, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections hfactor p r hp hr
  have hsq (w : PartialIsometry M) (hw : w ∈ s) : w.target ≤ q := by
    simpa only [ha ⟨w, hw⟩] using hq (Encodable.encode (⟨w, hw⟩ : s))
  have hov (w : PartialIsometry M) (hw : w ∈ s) :
      v.target.val * w.target.val = 0 := by
    have hrq : r.val * q.val = 0 := by
      change (1 - q.val) * q.val = 0
      rw [sub_mul, one_mul, q.property.isIdempotentElem.eq, sub_self]
    exact projection_orthogonal_of_le hrq hvr (hsq w hw)
  have hnew : sourceFamily p (insert v s) := by
    constructor
    · intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact ⟨hvp, hv0⟩
      · exact hs.1 w hw
    · intro w hw z hz hwz
      rcases Set.mem_insert_iff.mp hw with hw | hw
      · subst w
        rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          exact (hwz rfl).elim
        · exact hov z hz
      · rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          exact PartialIsometry.orthogonal_reverse _ _ (hov w hw)
        · exact hs.2 hw hz hwz
  have hvs : v ∈ s := hmax hnew (Set.subset_insert v s) (Set.mem_insert v s)
  have hz : v.target.val * v.target.val = 0 := hov v hvs
  rw [v.target.property.isIdempotentElem.eq] at hz
  exact target_ne_zero_of_support_ne_zero v hv0 hz

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionSchroederBernstein
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Schroeder--Bernstein for concrete projection equivalence

The proof constructs the unilateral shift on the iterated defect of a
partial isometry, then adds the identity on its orthogonal complement.
The construction uses the existing strong sums of partial isometries;
no finiteness or trace assumption occurs.
-/

namespace Generator.Tracial

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace PartialIsometry

private theorem defect_mul (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    (AlgebraProjection.remainder p v.support hp).val * v.val = 0 := by
  change (v.support.val - p.val) * v.val = 0
  rw [sub_mul, (v.target_le_iff_mul _).mp (ht.trans hp),
    (v.target_le_iff_mul _).mp ht, sub_self]

private theorem defect_mul_pow (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) {n : ℕ} (hn : 0 < n) :
    (AlgebraProjection.remainder p v.support hp).val * v.val ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', ← mul_assoc, defect_mul v p ht hp, zero_mul]

private theorem defectOrbit_target_le (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) (n : ℕ) :
    (defectOrbit v p ht hp n).target ≤ v.support := by
  apply ((defectOrbit v p ht hp n).target_le_iff_mul _).mpr
  change v.support.val * (v.val ^ n * (AlgebraProjection.remainder p v.support hp).val) =
    v.val ^ n * (AlgebraProjection.remainder p v.support hp).val
  cases n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact AlgebraProjection.remainder_le p v.support hp
  | succ n =>
    rw [pow_succ']
    calc
      _ = ((v.support.val * v.val) * v.val ^ n) *
          (AlgebraProjection.remainder p v.support hp).val := by simp only [mul_assoc]
      _ = _ := by rw [(v.target_le_iff_mul _).mp (ht.trans hp)]

private theorem defectOrbit_zero (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    (defectOrbit v p ht hp 0).target = AlgebraProjection.remainder p v.support hp := by
  apply Subtype.ext
  change (v.val ^ 0 * _) * star (v.val ^ 0 * _) = _
  simp only [pow_zero, one_mul,
    (AlgebraProjection.remainder p v.support hp).property.isSelfAdjoint.star_eq,
    (AlgebraProjection.remainder p v.support hp).property.isIdempotentElem.eq]

private theorem defectOrbit_cross (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) {i j : ℕ} (hij : i < j) :
    star (defectOrbit v p ht hp i).val * (defectOrbit v p ht hp j).val = 0 := by
  let d := AlgebraProjection.remainder p v.support hp
  have hd : d ≤ v.support := AlgebraProjection.remainder_le _ _ hp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  change star (v.val ^ i * d.val) * (v.val ^ (i + k) * d.val) = 0
  rw [star_mul, d.property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = (d.val * (star (v.val ^ i) * v.val ^ i)) * v.val ^ k * d.val := by
      simp only [mul_assoc]
    _ = d.val * v.val ^ k * d.val := by
      by_cases hi : i = 0
      · subst i
        simp only [pow_zero, star_one, mul_one]
      · rw [power_initial v (ht.trans hp) (Nat.pos_of_ne_zero hi),
          projection_mul_of_le hd]
    _ = 0 := by rw [defect_mul_pow v p ht hp hk, zero_mul]

private theorem defectOrbit_orthogonal (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    Pairwise (fun i j => (defectOrbit v p ht hp i).target.val *
      (defectOrbit v p ht hp j).target.val = 0) := by
  have hforward {i j : ℕ} (hij : i < j) :
      (defectOrbit v p ht hp i).target.val *
        (defectOrbit v p ht hp j).target.val = 0 := by
    change ((defectOrbit v p ht hp i).val * star (defectOrbit v p ht hp i).val) *
      ((defectOrbit v p ht hp j).val * star (defectOrbit v p ht hp j).val) = 0
    calc
      _ = (defectOrbit v p ht hp i).val *
          (star (defectOrbit v p ht hp i).val * (defectOrbit v p ht hp j).val) *
          star (defectOrbit v p ht hp j).val := by simp only [mul_assoc]
      _ = 0 := by rw [defectOrbit_cross v p ht hp hij, mul_zero, zero_mul]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hforward h
  · exact orthogonal_reverse _ _ (hforward h)

/-- A partial isometry whose range lies in its source has orthogonal copies
of its defect, all lying under the original source projection. -/
theorem defect_copies (v : PartialIsometry M) (h : v.target ≤ v.support) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support = AlgebraProjection.remainder v.target v.support h) ∧
      (∀ n, (a n).target ≤ v.support) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) :=
  ⟨defectOrbit v v.target le_rfl h, fun _ => rfl,
    defectOrbit_target_le v v.target le_rfl h, defectOrbit_orthogonal v v.target le_rfl h⟩

/-- A projection between the initial and final projections of a partial
isometry is equivalent to the initial projection. This is the shift form
of projection Schroeder--Bernstein. -/
theorem equivalent_intermediate (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) : v.support.Equivalent p := by
  let a := defectOrbit v p ht hp
  let d := AlgebraProjection.remainder p v.support hp
  have ho : Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) :=
    defectOrbit_orthogonal v p ht hp
  let b (i : ℕ) := rangeLink (a i) (a (i + 1)) rfl
  have hbs (i : ℕ) : (b i).support = (a i).target := rfl
  have hbt (i : ℕ) : (b i).target = (a (i + 1)).target := rangeLink_target _ _ _
  obtain ⟨s, _, hs, hs'⟩ := traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact ho hij)
    (by intro i j hij; rw [hbt, hbt]; exact ho (by omega))
  have hsle : s.support ≤ v.support := (hs _).mpr (fun i => by
    rw [hbs]
    exact defectOrbit_target_le v p ht hp i)
  have hst : s.target ≤ s.support := (hs' _).mpr (fun i => by
    rw [hbt, ← hbs (i + 1)]
    exact (hs s.support).mp le_rfl (i + 1))
  have hd0 : (a 0).target = d := defectOrbit_zero v p ht hp
  have hds : d ≤ s.support := by
    rw [← hd0, ← hbs 0]
    exact (hs s.support).mp le_rfl 0
  let c : AlgebraProjection M := ⟨1 - d.val, d.property.one_sub⟩
  have hsc : s.target ≤ c := (hs' c).mpr (fun i => by
    rw [hbt]
    change (1 - d.val) * (a (i + 1)).target.val = (a (i + 1)).target.val
    rw [sub_mul, one_mul, ← hd0, ho (by omega), sub_zero])
  have hdo : d.val * s.target.val = 0 := by
    change (1 - d.val) * s.target.val = s.target.val at hsc
    rw [sub_mul, one_mul] at hsc
    exact sub_eq_self.mp hsc
  have hsplit : s.support = orthogonalSum d s.target hdo := by
    apply le_antisymm
    · apply (hs _).mpr
      intro i
      rw [hbs]
      cases i with
      | zero => rw [hd0]; exact le_orthogonalSum_left _ _ hdo
      | succ i =>
        rw [← hbt i]
        exact ((hs' s.target).mp le_rfl i).trans
          (le_orthogonalSum_right _ _ hdo)
    · exact orthogonalSum_le hdo hds hst
  let e := AlgebraProjection.remainder s.support v.support hsle
  have hse : s.support.val * e.val = 0 :=
    AlgebraProjection.remainder_orthogonal _ _ hsle
  have hte : s.target.val * e.val = 0 :=
    projection_orthogonal_of_le hse hst le_rfl
  let z := s.patch (onProjection e) hse (by
    rw [onProjection_target]
    exact hte)
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    change s.support.val + e.val = v.support.val
    change s.support.val + (v.support.val - s.support.val) = v.support.val
    abel
  · apply Subtype.ext
    have hz := s.patch_target (onProjection e) hse (by
      rw [onProjection_target]
      exact hte)
    have he := congrArg (fun q : AlgebraProjection M => s.target.val + q.val)
      (onProjection_target e)
    have hz' : z.target.val = s.target.val + e.val := hz.trans he
    refine hz'.trans ?_
    change s.target.val + (v.support.val - s.support.val) = p.val
    rw [hsplit]
    change s.target.val + (v.support.val - (d.val + s.target.val)) = p.val
    change s.target.val + (v.support.val - ((v.support.val - p.val) + s.target.val)) = p.val
    abel

end PartialIsometry

namespace AlgebraProjection

/-- Comparable projections satisfy Schroeder--Bernstein without any finite
trace or finite-isometry assumption. -/
theorem equivalent_of_le_of_subequivalent {p q : AlgebraProjection M}
    (hpq : p ≤ q) (hqp : q.Subequivalent p) : p.Equivalent q := by
  obtain ⟨v, hv, ht⟩ := hqp
  exact equivalent_symm (by
    rw [← hv] at hpq ⊢
    exact v.equivalent_intermediate p ht hpq)

end AlgebraProjection

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIProjectionComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonzero projections in separably acting type III factors

A nonfinite projection contains a proper isometry and hence countably
many orthogonal copies of a nonzero defect.  Factoriality supplies a
countable source partition under this defect.  It embeds the identity
into the original projection; concrete Schroeder--Bernstein gives the
required equivalence.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- A nonfinite projection in a separably acting factor is equivalent to
its identity.  The type III hypothesis is needed only to supply nonfiniteness. -/
theorem projection_equivalent_one_of_not_finite_of_projection_countability
    (hFamilies : HasCountableProjectionFamilies M) (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hInfinite : ¬ FiniteProjectionIn M p.val) :
    p.Equivalent (⟨1, IsStarProjection.one _⟩ : AlgebraProjection M) := by
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM c.val c.property (fun a ha =>
      congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  simp only [FiniteProjectionIn] at hInfinite
  push Not at hInfinite
  obtain ⟨w, hw, hpw, hproper⟩ := hInfinite
  let v : PartialIsometry M := ⟨p, w, hw⟩
  have hvp : v.target ≤ v.support := (v.target_le_iff_mul p).mpr hpw
  let d := AlgebraProjection.remainder v.target v.support hvp
  have hd : d.val ≠ 0 := by
    change p.val - w * star w ≠ 0
    exact sub_ne_zero.mpr hproper.symm
  obtain ⟨slot, hs, ht, ho⟩ := v.defect_copies hvp
  obtain ⟨a, ha, hao, hatotal⟩ :=
    exists_countable_source_partition_of_projection_countability hFamilies hf d hd
  let b (n : ℕ) := (slot n).compose (a n).adjoint (by
    rw [PartialIsometry.adjoint_target, hs]
    exact ha n)
  have hbs (n : ℕ) : (b n).support = (a n).target := rfl
  have hbt (n : ℕ) : (b n).target ≤ p :=
    ((slot n).compose_target_le _ _).trans (ht n)
  obtain ⟨B, _, hBs, hBt⟩ := PartialIsometry.traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact hao hij)
    (by
      intro i j hij
      exact projection_orthogonal_of_le (ho hij)
        ((slot i).compose_target_le _ _) ((slot j).compose_target_le _ _))
  let oneP : AlgebraProjection M := ⟨1, IsStarProjection.one _⟩
  have hB1 : B.support = oneP := Subtype.ext (hatotal _ (fun n => by
    simpa only [hbs] using (hBs B.support).mp le_rfl n)).symm
  have hBp : B.target ≤ p := (hBt _).mpr hbt
  have hp1 : p ≤ oneP := by change 1 * p.val = p.val; exact one_mul _
  exact AlgebraProjection.equivalent_of_le_of_subequivalent hp1 ⟨B, hB1, hBp⟩

/-- Every nonzero projection in the concrete type III factor is the range
of an isometry in the same algebra. -/
theorem TypeIIIFactor.exists_isometry_onto_projection_of_projection_countability
    (hM : TypeIIIFactor M) (hFamilies : HasCountableProjectionFamilies M)
    (p : Algebra M) (hp : IsStarProjection p) (hne : p ≠ 0) :
    ∃ v : Algebra M, star v * v = 1 ∧ v * star v = p := by
  have hInfinite : ¬ FiniteProjectionIn M p := fun h => hne (hM.purelyInfinite p hp h)
  have he := projection_equivalent_one_of_not_finite_of_projection_countability
    hFamilies hM.factor ⟨p, hp⟩ hInfinite
  obtain ⟨v, hv, ht⟩ := AlgebraProjection.equivalent_symm he
  refine ⟨v.val, ?_, ?_⟩
  · exact v.initial.trans (congrArg Subtype.val hv)
  · exact congrArg Subtype.val ht

theorem TypeIIIFactor.exists_isometry_onto_projection [TopologicalSpace.SeparableSpace H]
    (hM : TypeIIIFactor M) (p : Algebra M) (hp : IsStarProjection p) (hne : p ≠ 0) :
    ∃ v : Algebra M, star v * v = 1 ∧ v * star v = p :=
  hM.exists_isometry_onto_projection_of_projection_countability
    (fun _ p hp ho => countable_of_orthogonal_nonzero_projections p hp ho) p hp hne

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SymmetricSupportTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem exists_symmetric_support_isometries_oai [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (hM : TypeIIIFactor M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ) (hne : ξ ≠ 0) :
    ∃ (v : Algebra M) (w : Algebra M.commutant),
      star v * v = 1 ∧ star w * w = 1 ∧
      v.val * star v.val = (vectorSupportProjection M ξ).val.val ∧
      w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val := by
  let p := vectorSupportProjection M ξ
  have hp : p.val ≠ 0 := by
    intro h
    have he := vectorSupportProjection_apply M ξ
    change p.val.val ξ = ξ at he
    rw [h] at he
    exact hne he.symm
  obtain ⟨v,hv,hvp⟩ := hM.exists_isometry_onto_projection p.val p.property hp
  let w : Algebra M.commutant := ⟨conjugationOperator J v.val,hleft v⟩
  have hw : star w * w = 1 := by
    apply Subtype.ext
    change star (conjugationOperator J v.val) * conjugationOperator J v.val = 1
    rw [← conjugationOperator_star J hJ, ← conjugationOperator_mul J hJ]
    have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
    rw [hv',conjugationOperator_one J hJ]
  refine ⟨v,w,hv,hw,congrArg Subtype.val hvp,?_⟩
  change conjugationOperator J v.val * star (conjugationOperator J v.val) = _
  rw [← conjugationOperator_star J hJ, ← conjugationOperator_mul J hJ]
  have hvp' : v.val * star v.val = p.val.val := congrArg Subtype.val hvp
  rw [hvp']
  exact (vectorSupportProjection_conjugate M J hJ hleft hright ξ hξ).symm

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_symmetric_support_isometries_oai.{u_1} := @OAI.KadisonKastler.exists_symmetric_support_isometries_oai.{u_1}
