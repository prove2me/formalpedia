-- Prove2me | solution 1 for OAI.KadisonKastler.minimal_row_family_right_module_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:15:46.299762+00:00
-- url     : https://prove2.me/submissions/2cd35522-096c-492b-a00b-70e25108d4ec

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_exists_central_localized_norm_le
import Theorems.Thm_OAI_KadisonKastler_exists_completelyBounded_weak_ultralimit
import Theorems.Thm_OAI_KadisonKastler_exists_unique_cyclic_factor_of_mem_orbitClosure
import Theorems.Thm_OAI_KadisonKastler_representationRowAverage_norm_le
import Theorems.Thm_OAI_KadisonKastler_right_module_of_factor_diagonal_norm

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowOperatorFactorization
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Operator factorizations and their exact behavior under finite row averages.
The representation is supplied by the proved Paulsen--Stinespring construction.
-/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace
open BoundedHochschild.KadisonRingrose

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonKastler.rowFactorOrder
attribute [local instance] OAI.KadisonKastler.rowFactorStarOrder
attribute [local instance] OAI.KadisonKastler.rowFactorOperatorOrder
local instance rowFactorOperatorStarOrder_rcba143_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
theorem finiteRightAverage_operator_factorization {M : VonNeumannAlgebra H}
    (F : Algebra M →ₗ[ℂ] Algebra M)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (hF : ∀ a, (F a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R))
    {ι : Type*} [Fintype ι] (r : ι → Algebra M) (a : Algebra M) :
    (finiteRightAverage r F a : H →L[ℂ] H) =
      L.adjoint.comp ((π a).comp (representationRowAverage π r R)) := by
  ext ξ
  have hsum : (finiteRightAverage r F a : H →L[ℂ] H) =
      ∑ i, (F (a * r i) : H →L[ℂ] H) * (star (r i) : H →L[ℂ] H) := by
    simp [finiteRightAverage_apply]
  rw [hsum]
  simp only [representationRowAverage, sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    mul_apply_eq_comp]
  change (∑ i, (F (a * r i) : H →L[ℂ] H) ((star (r i) : H →L[ℂ] H) ξ)) = _
  simp_rw [hF, map_mul, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorizationCyclicSpace
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The reducing subspace generated by the left operator in a factorization.
It retains every coefficient of the factored map and removes undetectable
vectors from the auxiliary representation. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

theorem factorizationCyclicSpace_total
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (z : factorizationCyclicSpace π L)
    (hz : ∀ a ξ, inner ℂ (cyclicFactorRepresentation π L a (cyclicFactorLeft π L ξ)) z = 0) :
    z = 0 := by
  have h : factorizationCyclicSpace π L ≤ (innerSL ℂ (z : K)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, ξ⟩, rfl⟩
      change inner ℂ (z : K) (π a (L ξ)) = 0
      exact inner_eq_zero_symm.mp (hz a ξ)
    · exact (innerSL ℂ (z : K)).isClosed_ker
  apply Subtype.ext
  exact inner_self_eq_zero.mp (h z.property)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicFactorCompression
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Compression of an operator factorization to its left generated space. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

theorem cyclicFactorRight_unique (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) (R S : H →L[ℂ] factorizationCyclicSpace π L)
    (h : ∀ a, (cyclicFactorLeft π L).adjoint.comp
      ((cyclicFactorRepresentation π L a).comp R) =
      (cyclicFactorLeft π L).adjoint.comp ((cyclicFactorRepresentation π L a).comp S)) :
    R = S := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply sub_eq_zero.mp
  apply factorizationCyclicSpace_total π L
  intro a η
  have he := congrArg (fun T : H →L[ℂ] H => inner ℂ η (T ξ)) (h (star a))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right] at he
  simpa only [inner_sub_right, sub_eq_zero] using he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularWeakCompact
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Weak operator compactness for the rectangular operators in a fixed
factorization. The source and target Hilbert spaces may differ. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
theorem exists_weak_rectangular_operator_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (R : ι → H →L[ℂ] K) (d : ℝ) (hd : 0 ≤ d) (hR : ∀ i, ‖R i‖ ≤ d) :
    ∃ T : H →L[ℂ] K, ‖T‖ ≤ d ∧ ∀ ξ η,
      Tendsto (fun i => inner ℂ η (R i ξ)) (ω : Filter ι) (𝓝 (inner ℂ η (T ξ))) := by
  have h (ξ : H) := Generator.Tracial.exists_weak_vector_ultralimit ω
    (fun i => R i ξ) (d * ‖ξ‖) (fun i => (R i).le_of_opNorm_le (hR i) ξ)
  choose v hv ht using h
  have ha (ξ ζ : H) : v (ξ + ζ) = v ξ + v ζ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (ξ + ζ) η)
    simpa only [map_add, inner_add_right] using (ht ξ η).add (ht ζ η)
  have hs (z : ℂ) (ξ : H) : v (z • ξ) = z • v ξ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (z • ξ) η)
    simpa only [map_smul, inner_smul_right] using (ht ξ η).const_mul z
  let T : H →L[ℂ] K := LinearMap.mkContinuous
    { toFun := v, map_add' := ha, map_smul' := hs } d hv
  exact ⟨T, T.opNorm_le_bound hd hv, ht⟩

omit [CompleteSpace H] in
theorem isCompact_weakRectangularBall {d : ℝ} (hd : 0 ≤ d) :
    IsCompact (weakRectangularBall H K d) := by
  classical
  apply isCompact_iff_ultrafilter_le_nhds'.mpr
  intro ω hω
  let R : (H →WOT[ℂ] K) → H →L[ℂ] K := fun T =>
    if ‖T.toCLM‖ ≤ d then T.toCLM else 0
  have hR (T : H →WOT[ℂ] K) : ‖R T‖ ≤ d := by
    dsimp [R]
    split_ifs with h
    · exact h
    · simpa only [norm_zero] using hd
  obtain ⟨T, hT, ht⟩ := exists_weak_rectangular_operator_ultralimit ω R d hd hR
  refine ⟨ContinuousLinearMapWOT.ofCLM T, hT, ?_⟩
  have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (R U))
      (ω : Filter (H →WOT[ℂ] K)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
  have he : (fun U => ContinuousLinearMapWOT.ofCLM (R U)) =ᶠ[ω] id := by
    filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] K)),
      U ∈ weakRectangularBall H K d from hω] with U hU
    simp only [weakRectangularBall, Set.mem_ofPred_eq] at hU
    simp only [R, ite_eq_left hU, ContinuousLinearMapWOT.ofCLM_toCLM, id_eq]
  exact hl.congr' he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakMapCompact
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The completely bounded ball is compact in the pointwise weak operator topology. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.weakMapCompactOrder
attribute [local instance] OAI.KadisonKastler.weakMapCompactStarOrder
/-- All matrix bounds are retained at a pointwise weak cluster point. -/
theorem isCompact_boundedWeakAlgebraMap (M : VonNeumannAlgebra H) {c : ℝ} (hc : 0 ≤ c) :
    IsCompact (Set.univ : Set (BoundedWeakAlgebraMap M c)) := by
  apply isCompact_iff_ultrafilter_le_nhds.mpr
  intro ω _
  obtain ⟨L, hL, ht⟩ := exists_completelyBounded_weak_ultralimit M ω
    (fun F : BoundedWeakAlgebraMap M c => F.map) hc (fun F => F.bound)
  let l : BoundedWeakAlgebraMap M c := ⟨L, hL⟩
  refine ⟨l, Set.mem_univ _, ?_⟩
  have hcoeff : Tendsto boundedWeakAlgebraCoefficients (ω : Filter (BoundedWeakAlgebraMap M c))
      (𝓝 (boundedWeakAlgebraCoefficients l)) := by
    apply tendsto_pi_nhds.mpr
    intro t
    exact ht t.1 t.2.1 t.2.2
  change (ω : Filter (BoundedWeakAlgebraMap M c)) ≤
    @nhds _ (TopologicalSpace.induced boundedWeakAlgebraCoefficients inferInstance) l
  rw [nhds_induced]
  exact Filter.map_le_iff_le_comap.mp hcoeff

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicRowFactorization
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Each member of a weak row-orbit closure has a unique bounded right
operator after compression to the left generated space. -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

theorem cyclic_right_factor_row_average
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (R S : H →L[ℂ] factorizationCyclicSpace π L)
    (F : Algebra M →ₗ[ℂ] Algebra M)
    (hF : ∀ a, (F a : H →L[ℂ] H) = (cyclicFactorLeft π L).adjoint.comp
      ((cyclicFactorRepresentation π L a).comp R))
    {ι : Type*} [Fintype ι] (r : ι → Algebra M)
    (hS : ∀ a, (finiteRightAverage r F a : H →L[ℂ] H) =
      (cyclicFactorLeft π L).adjoint.comp ((cyclicFactorRepresentation π L a).comp S)) :
    S = representationRowAverage (cyclicFactorRepresentation π L) r R := by
  apply cyclicFactorRight_unique π L
  intro a
  exact (hS a).symm.trans
    (finiteRightAverage_operator_factorization F (cyclicFactorRepresentation π L)
      (cyclicFactorLeft π L) R hF r a)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicFactorContinuity
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `continuous_of_isClosed_graph` (port compat, absent from our Mathlib). -/
private theorem continuousOfIsClosedGraphCompat {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [CompactSpace Y] (hf : IsClosed f.graph) : Continuous f := by
  rw [continuous_iff_isClosed]
  intro C hC
  convert isClosedMap_fst_of_compactSpace _ (hf.inter (isClosed_univ.prod hC))
  ext
  simp

/-! The uniquely determined cyclic right factor varies continuously in the
weak operator topology on every uniformly bounded family. -/

namespace KadisonKastler

noncomputable section

open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

theorem continuous_cyclic_right_factor
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (C : Set (BoundedWeakAlgebraMap M c)) (d : ℝ) (hd : 0 ≤ d)
    (R : C → H →L[ℂ] factorizationCyclicSpace π L)
    (hR : ∀ F, ‖R F‖ ≤ d)
    (hF : ∀ F a, (F.val.map a : H →L[ℂ] H) =
      (cyclicFactorLeft π L).adjoint.comp ((cyclicFactorRepresentation π L a).comp (R F))) :
    Continuous (fun F => ContinuousLinearMapWOT.ofCLM (R F)) := by
  let B := ↥(weakRectangularBall H (factorizationCyclicSpace π L) d)
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (isCompact_weakRectangularBall (H := H) (K := factorizationCyclicSpace π L) hd)
  let T : C → B := fun F => ⟨ContinuousLinearMapWOT.ofCLM (R F), hR F⟩
  have hgraph : T.graph = {p : C × B | ∀ a ξ η,
      boundedWeakAlgebraCoefficients p.1.val (a, ξ, η) =
        inner ℂ ((cyclicFactorRepresentation π L a).adjoint (cyclicFactorLeft π L η))
          (p.2.val.toCLM ξ)} := by
    ext p
    change T p.1 = p.2 ↔ _
    constructor
    · intro he a ξ η
      rw [← he]
      change inner ℂ η ((p.1.val.map a : H →L[ℂ] H) ξ) = _
      rw [hF]
      simp only [ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left]
    · intro he
      have hf (a : Algebra M) : (p.1.val.map a : H →L[ℂ] H) =
          (cyclicFactorLeft π L).adjoint.comp
            ((cyclicFactorRepresentation π L a).comp p.2.val.toCLM) := by
        apply ContinuousLinearMap.ext
        intro ξ
        apply ext_inner_left ℂ
        intro η
        simp only [ContinuousLinearMap.comp_apply]
        calc
          _ = inner ℂ ((cyclicFactorRepresentation π L a).adjoint
              (cyclicFactorLeft π L η)) (p.2.val.toCLM ξ) := he a ξ η
          _ = inner ℂ (cyclicFactorLeft π L η)
              (cyclicFactorRepresentation π L a (p.2.val.toCLM ξ)) :=
            ContinuousLinearMap.adjoint_inner_left _ _ _
          _ = _ := (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      have huniq : R p.1 = p.2.val.toCLM :=
        cyclicFactorRight_unique π L _ _ (fun a => (hF p.1 a).symm.trans (hf a))
      apply Subtype.ext
      change ContinuousLinearMapWOT.ofCLM (R p.1) = p.2.val
      rw [huniq, ContinuousLinearMapWOT.ofCLM_toCLM]
  have hclosed : IsClosed T.graph := by
    rw [hgraph]
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro ξ
    apply isClosed_iInter
    intro η
    have hcoeff : Continuous (boundedWeakAlgebraCoefficients (M := M) (c := c)) :=
      continuous_induced_dom
    exact isClosed_eq
      (((continuous_apply (a, ξ, η)).comp hcoeff).comp
        (continuous_subtype_val.comp continuous_fst))
      (ContinuousLinearMapWOT.continuous_inner_apply
        (continuous_subtype_val.comp continuous_snd) ξ
        ((cyclicFactorRepresentation π L a).adjoint (cyclicFactorLeft π L η)))
  exact continuous_subtype_val.comp (continuousOfIsClosedGraphCompat hclosed)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalFamilyQuantity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Norm minimization may be performed on the invariant family itself.
This lets us use the uniquely defined cyclic right factor without extending
that factor to maps outside the family. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {c : ℝ}

theorem minimal_row_family_quantity_constant_on
    (hc : 0 ≤ c) (C : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C)
    (q : C → ℝ) (hsub : ∀ a, IsClosed {F | q F ≤ a})
    (hdec : ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
      (F : C), q ⟨boundedWeakRowAverage hc r hr F.val, hinv n r hr F.property⟩ ≤ q F)
    (F G : C) : q F = q G := by
  have hle (A B : C) : q B ≤ q A := by
    let D : Set (BoundedWeakAlgebraMap M c) := Subtype.val '' {T : C | q T ≤ q A}
    have hDC : D ⊆ C := by
      rintro _ ⟨T, _, rfl⟩
      exact T.property
    have hne : D.Nonempty := ⟨A.val, A, show q A ≤ q A from le_rfl, rfl⟩
    have hcl : IsClosed D := hclosed.isClosedMap_subtype_val _ (hsub (q A))
    have hi : RowInvariant hc D := by
      intro n r hr T hT
      obtain ⟨T, hT, rfl⟩ := hT
      exact ⟨⟨boundedWeakRowAverage hc r hr T.val, hinv n r hr T.property⟩,
        (hdec n r hr T).trans hT, rfl⟩
    have he := hmin D hDC hne hcl hi
    have hB : B.val ∈ D := by rw [he]; exact B.property
    obtain ⟨B', hB', he'⟩ := hB
    change q B' ≤ q A at hB'
    have hBB : B' = B := Subtype.ext he'
    simpa only [hBB] using hB'
  exact le_antisymm (hle G F) (hle F G)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LocalizedFactorNorm
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The norm of a right factor localized by an operator in the original
commutant is constant on a minimal row family. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

omit [CompleteSpace H] in
theorem isClosed_weakRectangularBall (a : ℝ) :
    IsClosed (weakRectangularBall H K a) := by
  by_cases ha : 0 ≤ a
  · exact (isCompact_weakRectangularBall ha).isClosed
  · have he : weakRectangularBall H K a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact ha ((norm_nonneg T.toCLM).trans hT)
    rw [he]
    exact isClosed_empty

omit [CompleteSpace H] in
theorem isClosed_localized_factor_norm {X : Type*} [TopologicalSpace X]
    (R : X → H →L[ℂ] K) (hR : Continuous (fun x => ContinuousLinearMapWOT.ofCLM (R x)))
    (T : H →L[ℂ] H) (a : ℝ) : IsClosed {x | ‖(R x).comp T‖ ≤ a} := by
  have hc : Continuous (fun x => ContinuousLinearMapWOT.ofCLM ((R x).comp T)) := by
    apply ContinuousLinearMapWOT.continuous_iff.mpr
    intro ξ η
    exact ContinuousLinearMapWOT.continuous_inner_apply hR (T ξ) η
  exact (isClosed_weakRectangularBall (H := H) (K := K) a).preimage hc

theorem representationRowAverage_comp_commutant
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : H →L[ℂ] K)
    (T : H →L[ℂ] H)
    (hT : ∀ a : Algebra M, (a : H →L[ℂ] H).comp T = T.comp (a : H →L[ℂ] H))
    {ι : Type*} [Fintype ι] (r : ι → Algebra M) :
    (representationRowAverage π r R).comp T = representationRowAverage π r (R.comp T) := by
  ext ξ
  simp only [representationRowAverage, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hi := congrArg (fun A : H →L[ℂ] H => A ξ) (hT (star (r i)))
  change (star (r i) : H →L[ℂ] H) (T ξ) = T ((star (r i) : H →L[ℂ] H) ξ) at hi
  rw [hi]

theorem minimal_row_family_localized_factor_norm
    (hc : 0 ≤ c) (C : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : C → H →L[ℂ] K)
    (hR : Continuous (fun F => ContinuousLinearMapWOT.ofCLM (R F)))
    (hrow : ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (F : C),
      R ⟨boundedWeakRowAverage hc r hr F.val, hinv n r hr F.property⟩ =
        representationRowAverage π r (R F))
    (T : H →L[ℂ] H)
    (hT : ∀ a : Algebra M, (a : H →L[ℂ] H).comp T = T.comp (a : H →L[ℂ] H))
    (F G : C) : ‖(R F).comp T‖ = ‖(R G).comp T‖ := by
  apply minimal_row_family_quantity_constant_on hc C hclosed hinv hmin
    (fun F => ‖(R F).comp T‖) (isClosed_localized_factor_norm R hR T) _ F G
  intro n r hr A
  rw [hrow, representationRowAverage_comp_commutant π (R A) T hT r]
  exact representationRowAverage_norm_le π r hr ((R A).comp T)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalFamilyDiagonalNorm
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Diagonal norm preservation on a minimal row family. Central support
localization handles arbitrary centers and represented multiplicities. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

theorem minimal_row_family_diagonal_norm
    (hc : 0 ≤ c) (C : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : C → H →L[ℂ] K)
    (hR : Continuous (fun F => ContinuousLinearMapWOT.ofCLM (R F)))
    (hrow : ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (F : C),
      R ⟨boundedWeakRowAverage hc r hr F.val, hinv n r hr F.property⟩ =
        representationRowAverage π r (R F))
    (F : C) (e : AlgebraProjection M) :
    ‖(π e.val).comp ((R F).comp (e.val : H →L[ℂ] H))‖ =
      ‖(R F).comp (e.val : H →L[ℂ] H)‖ := by
  let : CompactSpace (BoundedWeakAlgebraMap M c) :=
    isCompact_univ_iff.mp (isCompact_boundedWeakAlgebraMap M hc)
  let : CompactSpace C := isCompact_iff_compactSpace.mp hclosed.isCompact
  obtain ⟨G, hG⟩ := exists_central_localized_norm_le π R hR
    (fun A n r hr => ⟨⟨boundedWeakRowAverage hc r hr A.val, hinv n r hr A.property⟩,
      hrow n r hr A⟩) e F
  have heq := minimal_row_family_localized_factor_norm hc C hclosed hinv hmin π R hR hrow
    ((centralSupport e).val : H →L[ℂ] H)
    (fun a => congrArg Subtype.val (centralSupport_commutes e a)) F G
  have hcore : ‖(R F).comp ((centralSupport e).val : H →L[ℂ] H)‖ ≤
      ‖(π e.val).comp ((R F).comp (e.val : H →L[ℂ] H))‖ := heq.trans_le hG
  have hep : ((centralSupport e).val : H →L[ℂ] H).comp (e.val : H →L[ℂ] H) =
      (e.val : H →L[ℂ] H) := congrArg Subtype.val (le_centralSupport e)
  have hsub : ‖(R F).comp (e.val : H →L[ℂ] H)‖ ≤
      ‖(R F).comp ((centralSupport e).val : H →L[ℂ] H)‖ := by
    calc
      _ = ‖((R F).comp ((centralSupport e).val : H →L[ℂ] H)).comp
          (e.val : H →L[ℂ] H)‖ := by rw [ContinuousLinearMap.comp_assoc, hep]
      _ ≤ _ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_left (e.property.map M.toStarSubalgebra.subtype).norm_le
          (norm_nonneg _)).trans_eq (mul_one _))
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right (e.property.map π).norm_le (norm_nonneg _)).trans_eq
        (one_mul _))
  · exact hsub.trans hcore

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalFamilyModule
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Every member of a minimal row family in a fixed completely bounded
orbit closure is right modular. The auxiliary factorization is constructed
before applying the central-support localization argument. -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

local instance minimalModuleOrder_rcba143_1 : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance minimalModuleStarOrder_rcba143_1 : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
theorem minimal_row_family_right_module_of_factorization_oai
    (hc : 0 ≤ c) (F₀ : BoundedWeakAlgebraMap M c)
    (C : Set (BoundedWeakAlgebraMap M c))
    (hC : C ⊆ closure (boundedWeakRowOrbit F₀)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R₀ : H →L[ℂ] K)
    (hF₀ : ∀ a, (F₀.map a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R₀)) :
    ∀ G ∈ C, ∀ a b, G.map (a * b) = G.map a * b := by
  have hex (G : C) : ∃ S : H →L[ℂ] factorizationCyclicSpace π L,
      ‖S‖ ≤ ‖R₀‖ ∧ ∀ a, (G.val.map a : H →L[ℂ] H) =
        (cyclicFactorLeft π L).adjoint.comp ((cyclicFactorRepresentation π L a).comp S) :=
    (exists_unique_cyclic_factor_of_mem_orbitClosure π L R₀ F₀ hF₀ (hC G.property)).exists
  choose R hR using hex
  have hcont := continuous_cyclic_right_factor π L C ‖R₀‖ (norm_nonneg _) R
    (fun G => (hR G).1) (fun G => (hR G).2)
  have hrow (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (G : C) :
      R ⟨boundedWeakRowAverage hc r hr G.val, hinv n r hr G.property⟩ =
        representationRowAverage (cyclicFactorRepresentation π L) r (R G) := by
    apply cyclic_right_factor_row_average π L (R G) _ G.val.map (hR G).2 r
    exact (hR ⟨boundedWeakRowAverage hc r hr G.val, hinv n r hr G.property⟩).2
  intro G hG
  let F : Algebra M →L[ℂ] Algebra M := G.map.mkContinuous c G.bound.apply_norm_le
  exact right_module_of_factor_diagonal_norm (cyclicFactorRepresentation π L)
    (cyclicFactorLeft π L) (R ⟨G, hG⟩) F (hR ⟨G, hG⟩).2
    (minimal_row_family_diagonal_norm hc C hclosed hinv hmin
      (cyclicFactorRepresentation π L) R hcont hrow ⟨G, hG⟩)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.minimal_row_family_right_module_of_factorization_oai.{u_1, u_2} := @OAI.KadisonKastler.minimal_row_family_right_module_of_factorization_oai.{u_1, u_2}
