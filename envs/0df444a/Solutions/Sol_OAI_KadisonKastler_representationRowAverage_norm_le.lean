-- Prove2me | solution 1 for OAI.KadisonKastler.representationRowAverage_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:21:03.080322+00:00
-- url     : https://prove2.me/submissions/6ee08af9-d4ae-434a-ba7a-f57790eeec05

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

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.finiteL2Basis_apply _root_.OAI.KadisonKastler.finiteLocalAmplificationValue_apply _root_.OAI.KadisonKastler.finiteLocalAmplification_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.operatorEntry_hilbertMatrix _root_.OAI.KadisonKastler.pointedPowerFibreEquiv_basis _root_.OAI.KadisonKastler.twoStateCornerEmbedding_adjoint _root_.OAI.KadisonKastler.twoStateCornerEmbedding_fst_one _root_.OAI.KadisonKastler.twoStateCornerEmbedding_fst_zero _root_.OAI.KadisonKastler.twoStateCornerEmbedding_snd_one _root_.OAI.KadisonKastler.twoStateCornerEmbedding_snd_zero _root_.OAI.KadisonKastler.twoStateSourceEmbedding_adjoint _root_.OAI.KadisonKastler.twoStateTargetEmbedding_adjoint _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rectangular operator matrices on finite Hilbert sums -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {m n : Type*} [Fintype m] [Fintype n]

attribute [local instance] OAI.KadisonKastler.rectangularHilbertOperatorStarOrder
omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem norm_hilbertRestrictRight_le (x : Generator.FiniteHilbert (m ⊕ n) H) :
    ‖hilbertRestrictRight x‖ ≤ ‖x‖ := by
  simp only [PiLp.norm_eq_of_L2, hilbertRestrictRight,
    Fintype.sum_sum_type]
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem hilbertMatrix_rectangularCorner [DecidableEq m] [DecidableEq n]
    (M : CStarMatrix m n (H →L[ℂ] H)) (x : Generator.FiniteHilbert (m ⊕ n) H) :
    hilbertMatrix (rectangularCorner M) x =
      hilbertExtendLeft (rectangularHilbertMatrix M (hilbertRestrictRight x)) := by
  ext i
  rcases i with i | i <;>
    simp [hilbertMatrix_apply, rectangularCorner, rectangularHilbertMatrix_apply,
      hilbertExtendLeft, hilbertRestrictRight, Fintype.sum_sum_type]

attribute [local instance] OAI.KadisonKastler.rectangularHilbertOperatorOrder
/-- The rectangular C⋆-matrix norm is its actual Hilbert-space operator norm. -/
theorem norm_rectangularHilbertMatrix (M : CStarMatrix m n (H →L[ℂ] H)) :
    ‖rectangularHilbertMatrix M‖ = ‖M‖ := by
  classical
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (hilbertMatrix (rectangularCorner M)).le_opNorm
      (hilbertExtendRight (m := m) x)
    rw [hilbertMatrix_rectangularCorner, norm_hilbertExtendLeft, norm_hilbertMatrix,
      norm_rectangularCorner, norm_hilbertExtendRight] at h
    simpa only [hilbertRestrictRight, hilbertExtendRight, Sum.elim_inr,
      WithLp.toLp_ofLp] using h
  · rw [← norm_rectangularCorner M, ← norm_hilbertMatrix]
    apply (hilbertMatrix (rectangularCorner M)).opNorm_le_bound
      (norm_nonneg (rectangularHilbertMatrix M))
    intro x
    rw [hilbertMatrix_rectangularCorner, norm_hilbertExtendLeft]
    exact (rectangularHilbertMatrix M).le_opNorm (hilbertRestrictRight x) |>.trans
      (mul_le_mul_of_nonneg_left (norm_hilbertRestrictRight_le x) (norm_nonneg _))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Adjoint and product formulas for rectangular operator matrices -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

attribute [local instance] OAI.KadisonKastler.rectangularOperatorStarOrder
omit [CompleteSpace H] [Fintype l] in
theorem rectangularHilbertMatrix_mul
    (M : CStarMatrix l m (H →L[ℂ] H)) (N : CStarMatrix m n (H →L[ℂ] H)) :
    rectangularHilbertMatrix (M * N) =
      (rectangularHilbertMatrix M).comp (rectangularHilbertMatrix N) := by
  ext x i
  simp only [rectangularHilbertMatrix_apply, ContinuousLinearMap.comp_apply,
    CStarMatrix.mul_apply, sum_apply, mul_apply_eq_comp, map_sum]
  rw [Finset.sum_comm]

theorem rectangularHilbertMatrix_conjTranspose (M : CStarMatrix m n (H →L[ℂ] H)) :
    rectangularHilbertMatrix M.conjTranspose = (rectangularHilbertMatrix M).adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply,
    rectangularHilbertMatrix_apply, CStarMatrix.conjTranspose_apply, inner_sum, sum_inner,
    ContinuousLinearMap.star_eq_adjoint]
  rw [Finset.sum_comm]

attribute [local instance] OAI.KadisonKastler.rectangularOperatorOrder
theorem norm_rectangular_mul_star [DecidableEq m]
    (M : CStarMatrix m n (H →L[ℂ] H)) : ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  rw [← norm_rectangularHilbertMatrix, rectangularHilbertMatrix_mul,
    rectangularHilbertMatrix_conjTranspose]
  have h := ContinuousLinearMap.norm_adjoint_comp_self (rectangularHilbertMatrix M).adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map,
    norm_rectangularHilbertMatrix, pow_two] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Products of operator rows on finite Hilbert sums -/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I J : Type*} [Fintype I] [Fintype J]

attribute [local instance] OAI.KadisonKastler.hilbertRowOrder
attribute [local instance] OAI.KadisonKastler.hilbertRowStarOrder
theorem norm_operatorRow_apply (C : I → H →L[ℂ] H) (x : Generator.FiniteHilbert I H) :
    ‖∑ i, C i (x i)‖ ≤ ‖operatorRow C‖ * ‖x‖ := by
  have h := (rectangularHilbertMatrix (operatorRow C)).le_opNorm x
  rw [norm_rectangularHilbertMatrix] at h
  simpa only [PiLp.norm_eq_of_L2, Fintype.sum_unique, rectangularHilbertMatrix_apply,
    operatorRow_apply, Real.sqrt_sq (norm_nonneg _)] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowVectorEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.finiteL2Basis_apply _root_.OAI.KadisonKastler.finiteLocalAmplificationValue_apply _root_.OAI.KadisonKastler.finiteLocalAmplification_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.pointedPowerFibreEquiv_basis _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.twoStateCornerEmbedding_adjoint _root_.OAI.KadisonKastler.twoStateCornerEmbedding_fst_one _root_.OAI.KadisonKastler.twoStateCornerEmbedding_fst_zero _root_.OAI.KadisonKastler.twoStateCornerEmbedding_snd_one _root_.OAI.KadisonKastler.twoStateCornerEmbedding_snd_zero _root_.OAI.KadisonKastler.twoStateSourceEmbedding_adjoint _root_.OAI.KadisonKastler.twoStateTargetEmbedding_adjoint _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Vector estimates for truncating the countable rows in module averaging. -/

namespace KadisonKastler

noncomputable section

open Generator
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance rowVectorAlgebraOrder_r3a5507_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance rowVectorAlgebraStarOrder_r3a5507_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowVectorOperatorOrder_r3a5507_1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance rowVectorOperatorStarOrder_r3a5507_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
theorem rowAdjointVector_norm_sq {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (ξ : H) :
    ‖rowAdjointVector r ξ‖ ^ 2 =
      (inner ℂ ξ (((∑ i, r i * star (r i) : Algebra M) : H →L[ℂ] H) ξ)).re := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i, ‖(star (r i) : H →L[ℂ] H) ξ‖ ^ 2) = _
  have hcoe : ((∑ i, r i * star (r i) : Algebra M) : H →L[ℂ] H) =
      ∑ i, (r i : H →L[ℂ] H) * star (r i : H →L[ℂ] H) := by simp
  rw [hcoe]
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), sum_apply, inner_sum]
  change (∑ i, (inner ℂ ((star (r i) : H →L[ℂ] H) ξ)
    ((star (r i) : H →L[ℂ] H) ξ)).re) =
    Complex.reCLM (∑ i, inner ℂ ξ (((r i : H →L[ℂ] H) * star (r i : H →L[ℂ] H)) ξ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_apply_eq_comp]
  simpa only [← ContinuousLinearMap.star_eq_adjoint, star_star, Complex.reCLM_apply] using
    congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right
      (star (r i : H →L[ℂ] H)) ξ ((star (r i : H →L[ℂ] H)) ξ)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowRepresentationContraction
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.finiteL2Basis_apply _root_.OAI.KadisonKastler.finiteLocalAmplificationValue_apply _root_.OAI.KadisonKastler.finiteLocalAmplification_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.pointedPowerFibreEquiv_basis _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.twoStateCornerEmbedding_adjoint _root_.OAI.KadisonKastler.twoStateCornerEmbedding_fst_one _root_.OAI.KadisonKastler.twoStateCornerEmbedding_fst_zero _root_.OAI.KadisonKastler.twoStateCornerEmbedding_snd_one _root_.OAI.KadisonKastler.twoStateCornerEmbedding_snd_zero _root_.OAI.KadisonKastler.twoStateSourceEmbedding_adjoint _root_.OAI.KadisonKastler.twoStateTargetEmbedding_adjoint _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The representation-side row action preserves the factorization bound. -/

namespace KadisonKastler

noncomputable section

open Generator
open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonKastler.rowRepOrder
attribute [local instance] OAI.KadisonKastler.rowRepStarOrder
theorem operatorRow_normalized_norm_le_one {ι : Type*} [Fintype ι]
    (s : ι → K →L[ℂ] K) (hs : ∑ i, s i * star (s i) = 1) :
    ‖operatorRow s‖ ≤ 1 := by
  classical
  have hp : operatorRow s * (operatorRow s).conjTranspose =
      (1 : CStarMatrix Unit Unit (K →L[ℂ] K)) := by
    ext1 i j
    cases i
    cases j
    simpa only [CStarMatrix.mul_apply, operatorRow_apply,
      CStarMatrix.conjTranspose_apply, CStarMatrix.one_apply, ite_eq_left] using hs
  have h := CStarRing.norm_star_mul_self (x := (1 : CStarMatrix Unit Unit (K →L[ℂ] K)))
  simp only [star_one, one_mul] at h
  have he := norm_rectangular_mul_star (operatorRow s)
  rw [hp] at he
  have h1 : ‖(1 : CStarMatrix Unit Unit (K →L[ℂ] K))‖ ≤ 1 := by
    nlinarith [norm_nonneg (1 : CStarMatrix Unit Unit (K →L[ℂ] K))]
  nlinarith [norm_nonneg (operatorRow s)]

theorem representationRowAverage_norm_le_oai {M : VonNeumannAlgebra H}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (R : H →L[ℂ] K) :
    ‖representationRowAverage π r R‖ ≤ ‖R‖ := by
  have hπ : ∑ i, π (r i) * star (π (r i)) = 1 := by
    simpa only [map_sum, map_mul, map_star, map_one] using congrArg π hr
  have hrow := operatorRow_normalized_norm_le_one (fun i => π (r i)) hπ
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
  intro ξ
  let v : FiniteHilbert ι K := WithLp.toLp 2 fun i => R ((star (r i) : H →L[ℂ] H) ξ)
  have hv : ‖v‖ ≤ ‖R‖ * ‖ξ‖ := by
    apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg (norm_nonneg R) (norm_nonneg ξ))).mp
    have hs : ∑ i, ‖(star (r i) : H →L[ℂ] H) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
      have hξ : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := by
        simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm
      have h := rowAdjointVector_norm_sq r ξ
      rw [hr] at h
      simpa only [PiLp.norm_sq_eq_of_L2, rowAdjointVector, PiLp.toLp_apply,
        OneMemClass.coe_one, one_apply_eq_self, hξ] using h
    rw [PiLp.norm_sq_eq_of_L2, mul_pow]
    calc
      _ ≤ ∑ i, (‖R‖ * ‖(star (r i) : H →L[ℂ] H) ξ‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm _) 2
      _ = ‖R‖ ^ 2 * ‖ξ‖ ^ 2 := by simp only [mul_pow, ← Finset.mul_sum, hs]
  have hb := norm_operatorRow_apply (fun i => π (r i)) v
  have he : (∑ i, π (r i) (v i)) = representationRowAverage π r R ξ := by
    simp [representationRowAverage, v]
  rw [he] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right hrow (norm_nonneg v)).trans
    (by simpa only [one_mul] using hv))

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.representationRowAverage_norm_le_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.representationRowAverage_norm_le_oai.{u_1, u_2, u_3}
