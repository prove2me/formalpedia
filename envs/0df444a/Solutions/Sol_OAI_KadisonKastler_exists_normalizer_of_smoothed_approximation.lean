-- Prove2me | solution 1 for OAI.KadisonKastler.exists_normalizer_of_smoothed_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:10.432287+00:00
-- url     : https://prove2.me/submissions/01991625-7d12-4542-bac8-dc5e0570ef82

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
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
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
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
import Definitions.Def_Q260K065
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_complete_bound_of_pointwise_weak_limit
import Theorems.Thm_OAI_KadisonKastler_concrete_ucp_unitary_of_published

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmenableEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moving an injective subalgebra into a nearby algebra

The published input is the one-sided assertion of Cameron--Christensen--
Sinclair--Smith--White--Wiggins, *Kadison--Kastler stable factors*, Duke
Math. J. 163 (2014), Theorem 3.3(i), arXiv:1209.4116v3, p. 13. Only
the inclusion and the displacement bound `150 * γ` are retained.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The algebra just constructed is the exact unitary image. -/
theorem conjugates_unitaryConjugateAlgebra (w : unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : Conjugates w M (unitaryConjugateAlgebra w M) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Matrix bounds for perturbation maps

All norms here are the C*-matrix norms, including for rectangular matrices.
The rectangular formulation records exactly the estimates needed for the
Haagerup product norm in the multiplication-correction argument.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
theorem rectangular_toCLM_mul {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix.toCLM (X * Y) = (CStarMatrix.toCLM Y).comp (CStarMatrix.toCLM X) := by
  ext v i
  simp only [CStarMatrix.toCLM_apply, ContinuousLinearMap.comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v X Y).symm i

/-- Submultiplicativity also holds for rectangular C*-matrices. -/
theorem rectangular_norm_mul_le {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
  simp only [CStarMatrix.norm_def, rectangular_toCLM_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem matrix_map_sub (F G : A →ₗ[ℂ] B) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (F - G) X = CStarMatrix.mapₗ F X - CStarMatrix.mapₗ G X := by
  ext i j
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Faithful representations are completely isometric

Injective star-algebra homomorphisms preserve C⋆-norms at each square
matrix level. The isometric corner embedding then gives the same statement
for every rectangular matrix size used in the perturbation estimates.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- Faithfulness preserves the norm of each square amplification. -/
theorem injective_starAlgHom_matrix_norm (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {n : Type*} [Fintype n] (X : CStarMatrix n n A) :
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ = ‖X‖ := by
  change ‖CStarMatrix.mapₙₐ φ.toNonUnitalStarAlgHom X‖ = ‖X‖
  exact NonUnitalStarAlgHom.norm_map _ (injective_starAlgHom_matrix φ hφ) X

/-- Every faithful star representation preserves all rectangular matrix norms. -/
theorem injective_starAlgHom_completelyIsometric (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) : CompletelyIsometric φ.toAlgHom.toLinearMap := by
  intro p q X
  calc
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ =
        ‖rectangularCorner (CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X)‖ :=
      (norm_rectangularCorner _).symm
    _ = ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap (rectangularCorner X)‖ := by
      rw [rectangularCorner_map]
    _ = ‖rectangularCorner X‖ := injective_starAlgHom_matrix_norm φ hφ _
    _ = ‖X‖ := norm_rectangularCorner X

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugationComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap_apply _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.matrixScalarHom_mul_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mul_matrixScalarHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete bounds for two operator conjugations

The smoothing operators need not be unitary. Their conjugation maps still
have a complete comparison bound controlled by their norms and distance.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem complete_operatorConjugation_sub (v w : B) :
    CompletelyBoundedBy (operatorConjugationLinear v - operatorConjugationLinear w)
      ((‖v‖ + ‖w‖) * ‖v - w‖) := by
  intro p q X
  let P : CStarMatrix (Fin p) (Fin p) B := matrixScalarHom v
  let R : CStarMatrix (Fin p) (Fin p) B := matrixScalarHom w
  let Q : CStarMatrix (Fin q) (Fin q) B := matrixScalarHom (star v)
  let S : CStarMatrix (Fin q) (Fin q) B := matrixScalarHom (star w)
  have hP : ‖P - R‖ ≤ ‖v - w‖ := by
    exact (map_sub (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) B) v w) ▸
      NonUnitalStarAlgHom.norm_apply_le
        (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) B) (v - w)
  have hQ : ‖Q‖ ≤ ‖v‖ := by
    simpa only [Q, norm_star] using NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) B) (star v)
  have hR : ‖R‖ ≤ ‖w‖ := NonUnitalStarAlgHom.norm_apply_le
    (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) B) w
  have hS : ‖Q - S‖ ≤ ‖v - w‖ := by
    change ‖(matrixScalarHom (star v) : CStarMatrix (Fin q) (Fin q) B) -
      matrixScalarHom (star w)‖ ≤ ‖v - w‖
    rw [← map_sub]
    have h := NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) B) (star v - star w)
    exact h.trans_eq (by rw [← star_sub, norm_star])
  have hmatrix (a : B) : CStarMatrix.mapₗ (operatorConjugationLinear a) X =
      (matrixScalarHom a : CStarMatrix (Fin p) (Fin p) B) * X *
        (matrixScalarHom (star a) : CStarMatrix (Fin q) (Fin q) B) := by
    apply Matrix.ext
    intro i j
    simp [operatorConjugationLinear, CStarMatrix.mul_apply, matrixScalarHom_apply]
  have hsplit : P * X * Q - R * X * S =
      (P - R) * X * Q + R * X * (Q - S) := by
    have hm (A B' : Matrix (Fin p) (Fin p) B) (Y : Matrix (Fin p) (Fin q) B)
        (C D : Matrix (Fin q) (Fin q) B) :
        A * Y * C - B' * Y * D = (A - B') * Y * C + B' * Y * (C - D) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    exact hm P R X Q S
  rw [matrix_map_sub, hmatrix, hmatrix, hsplit]
  calc
    _ ≤ ‖(P - R) * X * Q‖ + ‖R * X * (Q - S)‖ := norm_add_le _ _
    _ ≤ (‖P - R‖ * ‖X‖) * ‖Q‖ + (‖R‖ * ‖X‖) * ‖Q - S‖ :=
      add_le_add
        ((rectangular_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (rectangular_norm_mul_le _ _) (norm_nonneg Q)))
        ((rectangular_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (rectangular_norm_mul_le _ _) (norm_nonneg (Q - S))))
    _ ≤ (‖v - w‖ * ‖X‖) * ‖v‖ + (‖w‖ * ‖X‖) * ‖v - w‖ := by
      gcongr
    _ = ((‖v‖ + ‖w‖) * ‖v - w‖) * ‖X‖ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UCPDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Descending an amplified conjugacy through a UCP retraction

These are the operator-space estimates used when a character average or
an auxiliary tensor-factor average returns an amplified map to the base.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section Abstract

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]

/-- Restriction along a complete isometry preserves the same complete bound. -/
theorem completelyBoundedBy_comp_completeIsometry (F : B →ₗ[ℂ] C)
    (j : A →ₗ[ℂ] B) {c : ℝ} (hF : CompletelyBoundedBy F c)
    (hj : CompletelyIsometric j) : CompletelyBoundedBy (F.comp j) c := by
  intro p q X
  have he : CStarMatrix.mapₗ (F.comp j) X =
      CStarMatrix.mapₗ F (CStarMatrix.mapₗ j X) := by ext i k; rfl
  rw [he]
  exact (hF p q _).trans_eq (by rw [hj])

end Abstract

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity and norm bounds in pointwise weak operator limits

These lemmas retain the complete positivity of the maps obtained from
finite Hilbert-space tests. No normality of the limiting map is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A family of unital completely positive maps has a simultaneous
pointwise weak ultralimit. The limiting map is again unital and CP. -/
theorem exists_unitalCP_weak_ultralimit (ω : Ultrafilter ι)
    (F : ι → A →CP (H →L[ℂ] H)) (hF : ∀ i, F i 1 = 1) :
    ∃ S : A →CP (H →L[ℂ] H), S 1 = 1 ∧
      ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) (ω : Filter ι)
        (𝓝 (inner ℂ y (S a x))) := by
  choose S _hS ht using fun a : A => Generator.Tracial.exists_weak_operator_ultralimit
    ω (fun i => F i a) ‖a‖ (norm_nonneg a)
      (fun i => unital_completelyPositive_norm_le (F i) (hF i) a)
  have hadd (a b : A) : S (a + b) = S a + S b := by
    ext x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (a + b) x y)
    simpa only [map_add, add_apply, inner_add_right] using
      (ht a x y).add (ht b x y)
  have hsmul (c : ℂ) (a : A) : S (c • a) = c • S a := by
    ext x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • a) x y)
    simpa only [map_smul, smul_apply, inner_smul_right] using
      (ht a x y).const_mul c
  let L : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := S, map_add' := hadd, map_smul' := hsmul }
  let φ : A →CP (H →L[ℂ] H) := completelyPositive_of_pointwise_weak_limit F L ht
  refine ⟨φ, ?_, ht⟩
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (S 1 x) = inner ℂ y x
  apply tendsto_nhds_unique (ht 1 x y)
  simpa only [hF, one_apply_eq_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y x) (ω : Filter ι)
      (𝓝 (inner ℂ y x)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering a normalizer from weak limits of conjugations

The smoothing argument supplies exact normalizers close to moving linear
maps. Only the latter maps need to converge. A weak limit of the actual
conjugations is UCP and has range in the original algebra; the complete
error bound then gives a nearby exact normalizer.
-/

namespace KadisonKastler

open Filter
open scoped CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*}

section MovingLimit

attribute [local instance] OAI.KadisonKastler.normalizerLimitFactorStarOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {l : Filter ι} [l.NeBot]

/-- A complete bound survives when both compared maps vary and converge
only on individual weak operator coefficients. -/
theorem complete_bound_of_two_weak_limits
    (F R : ι → A →ₗ[ℂ] (H →L[ℂ] H)) (S ρ : A →ₗ[ℂ] (H →L[ℂ] H))
    (hF : ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) l
      (𝓝 (inner ℂ y (S a x))))
    (hR : ∀ a x y, Tendsto (fun i => inner ℂ y (R i a x)) l
      (𝓝 (inner ℂ y (ρ a x))))
    {e : ℝ} (he : 0 ≤ e) (hclose : ∀ i, CompletelyBoundedBy (F i - R i) e) :
    CompletelyBoundedBy (S - ρ) e := by
  have ht : ∀ a x y, Tendsto (fun i => inner ℂ y ((F i - R i) a x)) l
      (𝓝 (inner ℂ y ((S - ρ) a x))) := by
    intro a x y
    simpa only [LinearMap.sub_apply, sub_apply, inner_sub_right] using
      (hF a x y).sub (hR a x y)
  have hb := complete_bound_of_pointwise_weak_limit (fun i => F i - R i)
    (S - ρ) 0 ht he (fun i => by simpa only [sub_zero] using hclose i)
  simpa only [sub_zero] using hb

end MovingLimit

attribute [local instance] OAI.KadisonKastler.normalizerLimitFactorOrder
attribute [local instance] OAI.KadisonKastler.normalizerLimitFactorStarOrder
/-- The modular smoothing limit step. The comparison maps may be neither
positive nor multiplicative. The exact conjugations supply positivity and
range membership, while the comparison maps supply the limit representation. -/
theorem exists_normalizer_of_weak_comparison
    (P : VonNeumannAlgebra H) (W : unitary (H →L[ℂ] H))
    (hCorrection : PublishedMultiplicationCorrection (unitaryConjugateAlgebra W P))
    (hCommutant : PublishedBlockCommutantApproximation
      (Algebra (unitaryConjugateAlgebra W P)) H)
    (ω : Ultrafilter ι) (V : ι → unitary (H →L[ℂ] H))
    (hV : ∀ i, Conjugates (V i) P P)
    (R : ι → Algebra P →ₗ[ℂ] (H →L[ℂ] H))
    (hR : ∀ a x y, Tendsto (fun i => inner ℂ y (R i a x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (unitaryConj W a x))))
    {e g : ℝ} (he : 0 ≤ e) (hesmall : e < 1 / 1000)
    (hge : g + e < 1) (hgap : kkDistance (unitaryConjugateAlgebra W P) P < g)
    (hclose : ∀ i, CompletelyBoundedBy
      ((unitaryConjugationLinear (V i)).comp (algebraInclusion P).toAlgHom.toLinearMap -
        R i) e) :
    ∃ n : unitary (H →L[ℂ] H), Conjugates n P P ∧
      ‖(n : H →L[ℂ] H) - (W : H →L[ℂ] H)‖ ≤ 128 * e := by
  let Q := unitaryConjugateAlgebra W P
  let j : Algebra Q →⋆ₐ[ℂ] Algebra P := (unitaryConjugateEquiv W P).symm.toStarAlgHom
  let ρ (i : ι) : Algebra Q →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (V i)).toStarAlgHom.comp
      ((algebraInclusion P).comp j)
  let F (i : ι) : Algebra Q →CP (H →L[ℂ] H) :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (ρ i)
  obtain ⟨S, hS, ht⟩ := exists_unitalCP_weak_ultralimit ω F (fun i => map_one (ρ i))
  have hmem (x : Algebra Q) : S x ∈ P := by
    apply Generator.Tracial.weak_operator_limit_mem (l := (ω : Filter ι)) P (fun i =>
      (⟨F i x, (hV i).subset ⟨j x, (j x).property, rfl⟩⟩ : Algebra P)) (S x)
    exact ht x
  let L : Algebra Q →ₗ[ℂ] Algebra P :=
    S.toLinearMap.codRestrict P.toStarSubalgebra.toSubmodule hmem
  let φ : Algebra Q →CP Algebra P :=
    completelyPositive_of_embedding (algebraInclusion P) Subtype.val_injective S L
      (fun _ => rfl)
  have hφ : φ 1 = 1 := Subtype.ext hS
  have hj (x : Algebra Q) : unitaryConj W (j x) = (x : H →L[ℂ] H) := by
    have h := congrArg Subtype.val ((unitaryConjugateEquiv W P).apply_symm_apply x)
    exact h
  have hR' : ∀ a x y, Tendsto (fun i => inner ℂ y ((R i).comp j.toAlgHom.toLinearMap a x))
      (ω : Filter ι) (𝓝 (inner ℂ y ((algebraInclusion Q) a x))) := by
    intro a x y
    change Tendsto (fun i => inner ℂ y (R i (j a) x)) (ω : Filter ι)
      (𝓝 (inner ℂ y ((a : H →L[ℂ] H) x)))
    rw [← hj a]
    exact hR (j a) x y
  have hcl (i : ι) : CompletelyBoundedBy
      ((F i).toLinearMap - (R i).comp j.toAlgHom.toLinearMap) e := by
    have hb := completelyBoundedBy_comp_completeIsometry _ j.toAlgHom.toLinearMap
      (hclose i) (injective_starAlgHom_completelyIsometric j
        (unitaryConjugateEquiv W P).symm.injective)
    exact hb
  have hbound := complete_bound_of_two_weak_limits (fun i => (F i).toLinearMap)
    (fun i => (R i).comp j.toAlgHom.toLinearMap) S.toLinearMap
    (algebraInclusion Q).toAlgHom.toLinearMap ht hR' he hcl
  obtain ⟨q, hq, hqn⟩ := concrete_ucp_unitary_of_published hCorrection hCommutant
    φ hφ he hesmall hge hbound hgap
  refine ⟨q * W, (conjugates_unitaryConjugateAlgebra W P).trans hq, ?_⟩
  have hd : ((q * W : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - W =
      ((q : H →L[ℂ] H) - 1) * W := by
    simp only [Submonoid.coe_mul, sub_mul, one_mul]
  rw [hd, CStarRing.norm_mul_coe_unitary]
  exact hqn

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SmoothedNormalizerLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The strong-star smoothing limit gives an exact nearby normalizer -/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*}

attribute [local instance] OAI.KadisonKastler.smoothingFactorStarOrder
/-- Strong convergence of the adjoints already gives weak convergence of
the conjugated operators. No norm convergence of the smoothing is used. -/
theorem operatorConjugation_weak_tendsto {l : Filter ι}
    (Q : ι → (H →L[ℂ] H)) (W : H →L[ℂ] H)
    (hstar : ∀ x, Tendsto (fun i => star (Q i) x) l (𝓝 (star W x)))
    (a : H →L[ℂ] H) (x y : H) :
    Tendsto (fun i => inner ℂ y (operatorConjugationLinear (Q i) a x)) l
      (𝓝 (inner ℂ y (operatorConjugationLinear W a x))) := by
  have ht := (hstar y).inner (𝕜 := ℂ)
    (a.continuous.continuousAt.tendsto.comp (hstar x))
  have he (v : H →L[ℂ] H) :
      inner ℂ (star v y) (a (star v x)) =
        inner ℂ y (operatorConjugationLinear v a x) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint, operatorConjugationLinear_apply,
      mul_apply_eq_comp] using v.adjoint_inner_left (a (star v x)) y
  have ht' : Tendsto (fun i => inner ℂ (star (Q i) y) (a (star (Q i) x))) l
      (𝓝 (inner ℂ (star W y) (a (star W x)))) := ht
  simpa only [he] using ht'

attribute [local instance] OAI.KadisonKastler.smoothingFactorOrder
/-- A uniformly bounded strong-star approximation to a unitary, uniformly
close to exact normalizers, yields an actual normalizer with a universal
linear displacement estimate. This is the UCP limit step in Section 7. -/
theorem exists_normalizer_of_smoothed_approximation_oai
    (P : VonNeumannAlgebra H) (W : unitary (H →L[ℂ] H))
    (hCorrection : PublishedMultiplicationCorrection (unitaryConjugateAlgebra W P))
    (hCommutant : PublishedBlockCommutantApproximation
      (Algebra (unitaryConjugateAlgebra W P)) H)
    (ω : Ultrafilter ι) (V : ι → unitary (H →L[ℂ] H))
    (hV : ∀ i, Conjugates (V i) P P) (Q : ι → H →L[ℂ] H)
    (hstar : ∀ x, Tendsto (fun i => star (Q i) x) (ω : Filter ι)
      (𝓝 (star (W : H →L[ℂ] H) x)))
    {C d g : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hQ : ∀ i, ‖Q i‖ ≤ C) (hVQ : ∀ i, ‖(V i : H →L[ℂ] H) - Q i‖ ≤ d)
    (hsmall : (1 + C) * d < 1 / 1000) (hge : g + (1 + C) * d < 1)
    (hgap : kkDistance (unitaryConjugateAlgebra W P) P < g) :
    ∃ n : unitary (H →L[ℂ] H), Conjugates n P P ∧
      ‖(n : H →L[ℂ] H) - (W : H →L[ℂ] H)‖ ≤ 128 * ((1 + C) * d) := by
  let R (i : ι) : Algebra P →ₗ[ℂ] (H →L[ℂ] H) :=
    (operatorConjugationLinear (Q i)).comp (algebraInclusion P).toAlgHom.toLinearMap
  apply exists_normalizer_of_weak_comparison P W hCorrection hCommutant ω V hV R
    (fun a x y => operatorConjugation_weak_tendsto Q W hstar a x y)
    (mul_nonneg (by linarith) hd) hsmall hge hgap
  intro i
  have hcoef : (‖(V i : H →L[ℂ] H)‖ + ‖Q i‖) * ‖(V i : H →L[ℂ] H) - Q i‖ ≤
      (1 + C) * d := by
    have hnormV : ‖(V i : H →L[ℂ] H)‖ ≤ 1 := by
      nontriviality (H →L[ℂ] H)
      exact (CStarRing.norm_coe_unitary (V i)).le
    apply mul_le_mul
    · exact add_le_add hnormV (hQ i)
    · exact hVQ i
    · exact norm_nonneg _
    · linarith
  have hb := completelyBoundedBy_comp_completeIsometry _
    (algebraInclusion P).toAlgHom.toLinearMap
    (complete_operatorConjugation_sub (V i : H →L[ℂ] H) (Q i))
    (injective_starAlgHom_completelyIsometric (algebraInclusion P) Subtype.val_injective)
  intro p q X
  exact (hb p q X).trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg X))

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_normalizer_of_smoothed_approximation_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_normalizer_of_smoothed_approximation_oai.{u_1, u_2}
