-- Prove2me | solution 1 for OAI.KadisonKastler.FullMatrixCorner.signedGroupUnion_generates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:56:13.238311+00:00
-- url     : https://prove2.me/submissions/42860e97-34b3-468a-bd0a-e752233c6c07

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
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
import Mathlib.Logic.Equiv.Fintype
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
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K035

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteCornerInflation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Inflation through countably many matrix corners

The hypotheses are the algebraic matrix-unit relations and the strong sum
of their diagonal projections. They give an actual Hilbert direct-sum
decomposition. A corner operator is then applied on each summand; in
particular a corner unitary inflates with no loss in displacement.
-/

namespace KadisonKastler

open scoped BigOperators Topology
open Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

namespace FullMatrixCorner

variable {E} (F : FullMatrixCorner E)

theorem column_adjoint_apply (i : ℕ) (x : H) :
    (F.column i).toContinuousLinearMap.adjoint x =
      E.orthogonalProjectionOnto (F.entry 0 i x) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (F.entry i 0 y) x =
    inner ℂ y (E.orthogonalProjectionOnto (F.entry 0 i x))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [← F.star_entry i 0, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem matrixEntry_apply (T : H →L[ℂ] H) (i j : ℕ) (x : E) :
    F.matrixEntry T i j x =
      E.orthogonalProjectionOnto (F.entry 0 i (T (F.entry j 0 x))) := by
  exact F.column_adjoint_apply i _

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InflatedConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingIsometry_column _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingOperator_column _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the full algebra from its common matrix corners -/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem extension_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) :
    cornerExtension E (F.matrixEntry T i j) = F.entry 0 i * T * F.entry j 0 := by
  have he : F.matrixEntry T i j =
      cornerCompression E (F.entry 0 i * T * F.entry j 0) := by
    apply ContinuousLinearMap.ext
    intro x
    exact F.matrixEntry_apply T i j x
  rw [he, cornerExtension_compression, ← F.zero_zero]
  calc
    F.entry 0 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 0 =
        (F.entry 0 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 0) := by
      noncomm_ring
    _ = _ := by rw [F.mul_entry, F.mul_entry]; simp

/-- Membership of every transported matrix entry determines membership of
the whole operator. The proof uses actual finite compressions and WOT closure. -/
theorem mem_of_matrixEntries (N : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ N) (T : H →L[ℂ] H)
    (hT : ∀ i j, cornerExtension E (F.matrixEntry T i j) ∈ N) : T ∈ N := by
  have hterm (i j : ℕ) : F.entry i i * T * F.entry j j ∈ N := by
    have h := N.mul_mem (N.mul_mem (hF i 0) (hT i j)) (hF 0 j)
    rw [F.extension_matrixEntry] at h
    have he : F.entry i 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 j =
        F.entry i i * T * F.entry j j := by
      calc
        _ = (F.entry i 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 j) := by
          noncomm_ring
        _ = _ := by rw [F.mul_entry, F.mul_entry]; simp
    rwa [he] at h
  have hmem (s : Finset ℕ) : F.partialDiagonal s * T * F.partialDiagonal s ∈ N := by
    simp only [partialDiagonal, Finset.sum_mul, Finset.mul_sum]
    exact N.sum_mem (fun i _ => N.sum_mem (fun j _ => hterm j i))
  let a (s : Finset ℕ) : Algebra N :=
    ⟨F.partialDiagonal s * T * F.partialDiagonal s, hmem s⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) N a T
  intro x y
  have ht := (F.partialDiagonal_tendsto y).inner (𝕜 := ℂ)
    (T.continuous.continuousAt.tendsto.comp (F.partialDiagonal_tendsto x))
  have he (s : Finset ℕ) :
      inner ℂ (F.partialDiagonal s y) (T (F.partialDiagonal s x)) =
        inner ℂ y ((F.partialDiagonal s * T * F.partialDiagonal s) x) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_left (F.partialDiagonal s)
      (T (F.partialDiagonal s x)) y]
    simp only [← ContinuousLinearMap.star_eq_adjoint, F.partialDiagonal_star]
  exact ht.congr he

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplifiedAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A concrete infinite amplification

The amplification of a corner algebra is the commutant of its diagonally
represented commutant. Its matrix entries are exactly the operators in the
corner algebra. This construction uses the actual countable matrix units.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem inner_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) (x y : E) :
    inner ℂ y (F.matrixEntry T i j x) = inner ℂ (F.column i y) (T (F.column j x)) := by
  exact ContinuousLinearMap.adjoint_inner_right (F.column i).toContinuousLinearMap y _

theorem matrixEntry_inflate_mul (S : E →L[ℂ] E) (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (F.inflateHom S * T) i j = S * F.matrixEntry T i j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [F.inner_matrixEntry]
  change inner ℂ (F.column i y) (F.inflateHom S (T (F.column j x))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (F.inflateHom S) (F.column i y)) (T (F.column j x)) = _
  rw [← map_star, F.inflateHom_column, ← F.inner_matrixEntry]
  exact ContinuousLinearMap.adjoint_inner_left S (F.matrixEntry T i j x) y

theorem matrixEntry_mul_inflate (S : E →L[ℂ] E) (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (T * F.inflateHom S) i j = F.matrixEntry T i j * S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [F.inner_matrixEntry]
  change inner ℂ (F.column i y) (T (F.inflateHom S (F.column j x))) = _
  rw [F.inflateHom_column, ← F.inner_matrixEntry]
  rfl

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FullMatrixInjectivity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The type I algebra generated by full countable matrix units

Taking the commutant of the diagonal corner operators realizes the scalar
matrix factor directly. Its matrix coefficients are scalar, so it lies in
any von Neumann algebra containing the original matrix units.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

/-- Each corner coefficient of a scalar matrix operator is scalar. -/
theorem scalarMatrixAlgebra_coefficient {T : H →L[ℂ] H}
    (hT : T ∈ F.scalarMatrixAlgebra) (i j : ℕ) :
    ∃ z : ℂ, F.matrixEntry T i j = z • (1 : E →L[ℂ] E) := by
  have hc : F.matrixEntry T i j ∈ Subalgebra.center ℂ (E →L[ℂ] E) := by
    rw [Subalgebra.mem_center_iff]
    intro S
    have h := congrArg (fun R => F.matrixEntry R i j)
      ((F.mem_scalarMatrixAlgebra_iff T).mp hT S).eq
    simpa only [F.matrixEntry_inflate_mul, F.matrixEntry_mul_inflate] using h
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hc
  obtain ⟨z,hz⟩ := hc
  exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz.symm⟩

/-- Every represented scalar matrix operator lies in any algebra containing the entries. -/
theorem scalarMatrixAlgebra_le (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) : F.scalarMatrixAlgebra ≤ M := by
  intro T hT
  apply F.mem_of_matrixEntries M hF
  intro i j
  obtain ⟨z,hz⟩ := F.scalarMatrixAlgebra_coefficient hT i j
  rw [hz, map_smul, cornerExtension_one, ← F.zero_zero]
  exact M.toStarSubalgebra.smul_mem (hF 0 0) z

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCornerGeneration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix entries generated by the finite corner groups -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem scalarBlockHom_single {n : ℕ} (i j : Fin n) (z : ℂ) :
    F.scalarBlockHom n (CStarMatrix.ofMatrix (Matrix.single i j z)) = z • F.entry i j := by
  rw [F.scalarBlockHom_apply]
  simp [CStarMatrix.ofMatrix_apply, Matrix.single_apply, ite_smul, ite_and]

/-- A single sign reflection isolates a diagonal matrix projection. -/
theorem finiteSignedRepresentation_reflection {n : ℕ} (i : Fin n) :
    (F.finiteSignedRepresentation n
      (SemidirectProduct.inl (Function.update (1 : Fin n → ℤˣ) i (-1))) : H →L[ℂ] H) =
      1 - (2 : ℂ) • F.entry i i := by
  have h : (signedPermutationHom
      (SemidirectProduct.inl (Function.update (1 : Fin n → ℤˣ) i (-1))) :
      Matrix (Fin n) (Fin n) ℂ) = 1 - (2 : ℂ) • Matrix.single i i 1 := by
    rw [← signDiagonal_reflection]
    simp [signedPermutationHom, signDiagonalHom, signDiagonalUnitary]
  have hp : (∑ j : Fin n, F.entry j j) = F.partialDiagonal (Finset.range n) :=
    Fin.sum_univ_eq_sum_range (fun j => F.entry j j) n
  have hsingle : (∑ k : Fin n, ∑ l : Fin n,
      Matrix.single i i (1 : ℂ) k l • F.entry k l) = F.entry i i := by
    simpa only [F.scalarBlockHom_apply, CStarMatrix.ofMatrix_apply, one_smul] using
      F.scalarBlockHom_single i i 1
  have hscale : (∑ k : Fin n, ∑ l : Fin n,
      ((2 : ℂ) • Matrix.single i i (1 : ℂ)) k l • F.entry k l) =
        (2 : ℂ) • F.entry i i := by
    change (∑ k : Fin n, ∑ l : Fin n,
      ((2 : ℂ) * Matrix.single i i (1 : ℂ) k l) • F.entry k l) = _
    simp_rw [mul_smul]
    simp only [← Finset.smul_sum, hsingle]
  rw [F.finiteSignedRepresentation_apply, h]
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hscale]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [hp]
  abel

theorem entry_scalarBlock_sandwich {n : ℕ} (i j : Fin n)
    (a : CStarMatrix (Fin n) (Fin n) ℂ) :
    F.entry i i * F.scalarBlockHom n a * F.entry j j = a i j • F.entry i j := by
  rw [F.scalarBlockHom_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, F.mul_entry]
  simp [Fin.val_inj, ite_mul, smul_ite, F.mul_entry]

/-- Sandwiching any finite group element recovers its matrix coefficient. -/
theorem entry_finiteSigned_sandwich {n : ℕ} (i j : Fin n) (g : SignedPermutation (Fin n)) :
    F.entry i i * (F.finiteSignedRepresentation n g : H →L[ℂ] H) * F.entry j j =
      (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) i j • F.entry i j := by
  change F.entry i i *
    (F.scalarBlockHom n (CStarMatrix.ofMatrix (signedPermutationHom g :
      Matrix (Fin n) (Fin n) ℂ)) + (1 - F.scalarBlockHom n 1)) * F.entry j j = _
  rw [mul_add, add_mul, F.entry_scalarBlock_sandwich]
  have hz : F.entry i i * (1 - F.scalarBlockHom n 1) * F.entry j j = 0 := by
    rw [mul_sub, mul_one, sub_mul, F.entry_scalarBlock_sandwich, F.mul_entry]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Fin.val_inj]
  rw [hz, add_zero]
  rfl

/-- Containing the finite signed groups forces containment of all countable
matrix entries. -/
theorem entries_mem_of_finiteSigned (Q : VonNeumannAlgebra H)
    (hQ : ∀ n (g : SignedPermutation (Fin n)),
      (F.finiteSignedRepresentation n g : H →L[ℂ] H) ∈ Q) :
    ∀ i j, F.entry i j ∈ Q := by
  have hdiag (n : ℕ) (i : Fin n) : F.entry i i ∈ Q := by
    change F.entry i i ∈ Q.toSubalgebra
    have h := hQ n (SemidirectProduct.inl (Function.update (1 : Fin n → ℤˣ) i (-1)))
    rw [F.finiteSignedRepresentation_reflection] at h
    have hh : (2 : ℂ) • F.entry i i ∈ Q.toSubalgebra := by
      simpa only [sub_sub_cancel] using Q.sub_mem Q.one_mem h
    exact (Q.toStarSubalgebra.toSubalgebra.toSubmodule.smul_mem_iff
      (by norm_num : (2 : ℂ) ≠ 0)).mp hh
  have hentry (n : ℕ) (i j : Fin n) : F.entry i j ∈ Q := by
    change F.entry i j ∈ Q.toSubalgebra
    have h := Q.mul_mem (Q.mul_mem (hdiag n i)
      (hQ n (SemidirectProduct.inr (Equiv.swap i j)))) (hdiag n j)
    rw [F.entry_finiteSigned_sandwich] at h
    have hm : (signedPermutationHom (SemidirectProduct.inr (Equiv.swap i j)) :
        Matrix (Fin n) (Fin n) ℂ) = Matrix.permMatrixHom (R := ℂ) (Equiv.swap i j) := by
      simp [signedPermutationHom, permutationHom, permutationUnitary]
    simpa only [hm, permutationMatrix_apply, Equiv.swap_apply_right, ite_true, if_true, one_smul] using h
  intro i j
  exact hentry (max i j + 1) ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩
    ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FullCornerEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed embeddings of countable scalar matrix algebras -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

/-- The finite signed groups generate exactly the scalar matrix algebra. -/
theorem signedGroupUnion_generates_oai :
    generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range (fun u =>
      (subgroupAlgebraRepresentation F.signedGroupUnion F.scalarMatrixAlgebra
        F.signedGroupUnion_mem u : H →L[ℂ] H)))) = F.scalarMatrixAlgebra := by
  let V := subgroupAlgebraRepresentation F.signedGroupUnion F.scalarMatrixAlgebra
    F.signedGroupUnion_mem
  let Q := generatedVonNeumannAlgebra
    (StarAlgebra.adjoin ℂ (Set.range (fun u => (V u : H →L[ℂ] H))))
  change Q = F.scalarMatrixAlgebra
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro _ ⟨u, rfl⟩
    exact (V u).val.property
  · apply F.scalarMatrixAlgebra_le
    apply F.entries_mem_of_finiteSigned
    intro n g
    let u : F.signedGroupUnion := ⟨F.finiteSignedRepresentation n g, ⟨n, g, rfl⟩⟩
    exact subset_generatedVonNeumannAlgebra _ (StarAlgebra.subset_adjoin ℂ _ ⟨u, rfl⟩)

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.FullMatrixCorner.signedGroupUnion_generates_oai.{u_1} := @OAI.KadisonKastler.FullMatrixCorner.signedGroupUnion_generates_oai.{u_1}
