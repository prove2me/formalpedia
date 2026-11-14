-- Prove2me | solution 1 for OAI.KadisonKastler.finiteCoefficientConjugations_of_separable_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:45:02.079689+00:00
-- url     : https://prove2.me/submissions/ed28fe48-8226-4aff-b0d4-9d3d1607d62c

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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
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
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K027
import Definitions.Def_Q260K028
import Theorems.Thm_OAI_KadisonKastler_kkDistance_generated_restriction_le

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
-- module Solutions.OAIQ075_KS.KadisonKastler_RepresentedCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.coe_cornerUnitary _root_.OAI.KadisonKastler.complement_mul_cornerExtension _root_.OAI.KadisonKastler.cornerExtension_mul_complement _root_.OAI.KadisonKastler.cornerExtension_mul_starProjection _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.starProjection_mul_cornerExtension _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete compression to a common closed subspace

The corner acts on the subspace itself. Its operators are characterized by
membership of their extension by zero in the original von Neumann algebra.
This constructs the actual corner and proves that a common compression does
not increase Kadison--Kastler distance.
-/

namespace KadisonKastler

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem norm_cornerExtension_le (T : E →L[ℂ] E) : ‖cornerExtension E T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖T (E.orthogonalProjectionOnto x)‖ ≤ _
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (E.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg T))

@[simp] theorem norm_cornerExtension (T : E →L[ℂ] E) : ‖cornerExtension E T‖ = ‖T‖ := by
  apply le_antisymm (norm_cornerExtension_le E T)
  simpa only [cornerCompression_extension] using
    norm_cornerCompression_le E (cornerExtension E T)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending a corner unitary by the identity

A unitary on a closed subspace extends to a unitary on the ambient Hilbert
space, acting as the identity on the orthogonal complement. Its displacement
from the identity is exactly the displacement in the corner.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

variable [CompleteSpace H]

theorem cornerUnitary_sub_one (v : unitary (E →L[ℂ] E)) :
    (cornerUnitary E v : H →L[ℂ] H) - 1 =
      cornerExtension E ((v : E →L[ℂ] E) - 1) := by
  rw [coe_cornerUnitary, map_sub, cornerExtension_one]
  abel

@[simp] theorem norm_cornerUnitary_sub_one (v : unitary (E →L[ℂ] E)) :
    ‖(cornerUnitary E v : H →L[ℂ] H) - 1‖ = ‖(v : E →L[ℂ] E) - 1‖ := by
  rw [cornerUnitary_sub_one, norm_cornerExtension]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingRestriction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restriction to a reducing subspace and finite coefficients

The restriction of a star algebra to a closed invariant subspace is an
actual star homomorphism. Extending a corner unitary by the identity
preserves the coefficients of its conjugation on that subspace.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (K : Submodule ℂ H) [CompleteSpace K]

theorem star_cornerUnitary_coe (v : unitary (K →L[ℂ] K)) :
    star (cornerUnitary K v : H →L[ℂ] H) =
      (cornerUnitary K (star v) : H →L[ℂ] H) := by
  have hp : star K.starProjection = K.starProjection := by
    rw [← cornerExtension_one K, ← cornerExtension_star K]
    exact congrArg (cornerExtension K) (star_one (R := K →L[ℂ] K))
  simp only [coe_cornerUnitary, star_add, star_sub, star_one,
    ← cornerExtension_star, Unitary.coe_star, hp]

/-- On the reducing subspace, the extended unitary gives exactly the
conjugation of the restricted operator. -/
theorem unitaryConj_cornerUnitary_apply (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
    (v : unitary (K →L[ℂ] K)) (a : A) (x : K) :
    unitaryConj (cornerUnitary K v) a.val (x : H) =
      (unitaryConj v (reducingRestriction K A hA a) x : H) := by
  simp only [unitaryConj, mul_apply_eq_comp, star_cornerUnitary_coe, Unitary.coe_star,
    cornerUnitary_apply]
  rw [← reducingRestriction_coe_apply K A hA a
    ((star (v : K →L[ℂ] K)) x), cornerUnitary_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LocalCoefficientTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Original-space coefficients from a reducing corner

Strong density of the restricted algebra gives finite coefficient
approximants in the original algebra. This step needs neither faithful
restriction nor norm bounds on the chosen coefficient approximants.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exists_strong_coefficient_approx
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (V : Finset H) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : S, ∀ ξ ∈ V, ∀ η ∈ V,
      ‖inner ℂ η (((b : H →L[ℂ] H) - T) ξ)‖ < ε := by
  classical
  let C : ℝ := 1 + ∑ η ∈ V, ‖η‖
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hηC (η : H) (hη : η ∈ V) : ‖η‖ ≤ C := by
    have h : ‖η‖ ≤ ∑ ζ ∈ V, ‖ζ‖ :=
      Finset.single_le_sum (fun ζ (_ : ζ ∈ V) => norm_nonneg ζ) hη
    dsimp [C]
    linarith only [h]
  obtain ⟨b, hb⟩ := Generator.bicommutant_finite_strong_approximation
    S T hT V (ε / C) (div_pos hε hC)
  refine ⟨b, ?_⟩
  intro ξ hξ η hη
  have hnorm : ‖((b : H →L[ℂ] H) - T) ξ‖ < ε / C := by
    simpa only [sub_apply, norm_sub_rev] using hb ξ hξ
  calc
    _ ≤ ‖η‖ * ‖((b : H →L[ℂ] H) - T) ξ‖ := norm_inner_le_norm _ _
    _ ≤ C * ‖((b : H →L[ℂ] H) - T) ξ‖ :=
      mul_le_mul_of_nonneg_right (hηC η hη) (norm_nonneg _)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hnorm hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

variable (K : Submodule ℂ H) [CompleteSpace K]
  (A B : StarSubalgebra ℂ (H →L[ℂ] H))
  (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
  (hB : ∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K)

theorem exists_original_coefficient_approx
    (v : unitary (K →L[ℂ] K)) (a : A)
    (ha : unitaryConj v (reducingRestriction K A hA a) ∈
      Set.centralizer (Set.centralizer (Set.range (reducingRestriction K B hB))))
    (V : Finset H) (hV : ∀ ξ ∈ V, ξ ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : B, ∀ ξ ∈ V, ∀ η ∈ V,
      ‖inner ℂ η (((b : H →L[ℂ] H) -
        unitaryConj (cornerUnitary K v) a.val) ξ)‖ < ε := by
  classical
  let W : Finset K := V.attach.image (fun ξ => ⟨ξ.val, hV ξ.val ξ.property⟩)
  let T := unitaryConj v (reducingRestriction K A hA a)
  let S : StarSubalgebra ℂ (K →L[ℂ] K) := (reducingRestriction K B hB).range
  have hS : (S : Set (K →L[ℂ] K)) = Set.range (reducingRestriction K B hB) := rfl
  have ha' : T ∈ Set.centralizer (Set.centralizer (S : Set (K →L[ℂ] K))) := by
    rw [hS]
    exact ha
  obtain ⟨c, hc⟩ := exists_strong_coefficient_approx (H := K) S T ha' W hε
  obtain ⟨b, hb⟩ := c.property
  change reducingRestriction K B hB b = (c : K →L[ℂ] K) at hb
  refine ⟨b, ?_⟩
  intro ξ hξ η hη
  let ξK : K := ⟨ξ, hV ξ hξ⟩
  let ηK : K := ⟨η, hV η hη⟩
  have hξW : ξK ∈ W := Finset.mem_image.mpr ⟨⟨ξ, hξ⟩, by simp, rfl⟩
  have hηW : ηK ∈ W := Finset.mem_image.mpr ⟨⟨η, hη⟩, by simp, rfl⟩
  have heq : inner ℂ η (((b : H →L[ℂ] H) -
      unitaryConj (cornerUnitary K v) a.val) ξ) =
      inner ℂ ηK (((c : K →L[ℂ] K) - T) ξK) := by
    rw [sub_apply, inner_sub_right]
    rw [show ξ = (ξK : H) from rfl,
      unitaryConj_cornerUnitary_apply K A hA v a ξK,
      ← reducingRestriction_coe_apply K B hB b ξK]
    rw [hb]
    simp only [sub_apply, inner_sub_right]
    rfl
  rw [heq]
  exact hc ξK hξW ηK hηW

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitBallClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit balls in norm closures of complex linear subspaces

Radial contraction keeps approximants in their original subspace. It
proves the norm-density statement needed for the separable test algebras.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem unitBallClip_norm_le (x : B) : ‖unitBallClip x‖ ≤ 1 := by
  have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [unitBallClip, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_eq_div]
  exact (div_le_one hp).mpr (le_max_right _ _)

theorem unitBallClip_eq_self {x : B} (hx : ‖x‖ ≤ 1) : unitBallClip x = x := by
  simp only [unitBallClip, max_eq_left hx, inv_one, Complex.ofReal_one, one_smul]

theorem continuous_unitBallClip : Continuous (unitBallClip : B → B) := by
  have hc : Continuous (fun x : B => (max 1 ‖x‖)⁻¹) :=
    (continuous_const.max continuous_norm).inv₀ (fun x => by
      have h : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      exact ne_of_gt h)
  exact (Complex.continuous_ofReal.comp hc).smul continuous_id

theorem unitBallClip_mem (S : Submodule ℂ B) {x : B} (hx : x ∈ S) :
    unitBallClip x ∈ S := S.smul_mem _ hx

/-- The unit ball of a linear subspace is norm dense in the unit ball of
its closure, even when the subspace is not closed. -/
theorem closure_submodule_unitBall (S : Submodule ℂ B) :
    closure {x : B | x ∈ S ∧ ‖x‖ ≤ 1} =
      {x : B | x ∈ closure (S : Set B) ∧ ‖x‖ ≤ 1} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro x hx
      exact ⟨subset_closure hx.1, hx.2⟩
    · exact isClosed_closure.inter (isClosed_le continuous_norm continuous_const)
  · intro x hx
    have hclip := mem_closure_image continuous_unitBallClip.continuousAt hx.1
    rw [unitBallClip_eq_self hx.2] at hclip
    apply closure_mono _ hclip
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨unitBallClip_mem S hy, unitBallClip_norm_le y⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableAlgebraPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nearby separable test algebras

Countably many generators are enlarged alternately by nearby contractions.
The increasing norm closures give the two separable C*-algebras in §9.
All choices and closure estimates are constructed here; there is no
separable-reduction hypothesis.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem zero_mem_starAlgebraBall (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    0 ∈ starAlgebraBall A := ⟨A.zero_mem, by simp⟩

theorem cstarHull_mono : Monotone (cstarHull (H := H)) :=
  fun _ _ h => StarSubalgebra.topologicalClosure_mono (StarAlgebra.adjoin_mono h)

theorem SeparableSeeds.next_spec {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    p.Extends (p.next hr) r := Classical.choose_spec (p.exists_extension hr)

theorem SeparableSeeds.stages_left_mono {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    Monotone (fun n => (p.stages hr n).left) :=
  monotone_nat_of_le_succ (fun n => ((p.stages hr n).next_spec hr).1)

theorem SeparableSeeds.stages_right_mono {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    Monotone (fun n => (p.stages hr n).right) :=
  monotone_nat_of_le_succ (fun n => ((p.stages hr n).next_spec hr).2.1)

theorem le_increasingCstarClosure (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) :
    A n ≤ increasingCstarClosure A :=
  (le_iSup A n).trans (StarSubalgebra.le_topologicalClosure _)

theorem isSeparable_increasingCstarClosure
    (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hA : Monotone A)
    (hsep : ∀ n, IsSeparable (A n : Set (H →L[ℂ] H))) :
    IsSeparable (increasingCstarClosure A : Set (H →L[ℂ] H)) := by
  apply IsSeparable.closure
  rw [StarSubalgebra.coe_iSup_of_directed hA.directed_le]
  exact IsSeparable.iUnion hsep

theorem infDist_increasingCstarClosure_ball
    (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hA : Monotone A)
    (t : Set (H →L[ℂ] H)) {r : ℝ}
    (hnear : ∀ n, ∀ x ∈ starAlgebraBall (A n), Metric.infDist x t ≤ r) :
    ∀ x ∈ starAlgebraBall (increasingCstarClosure A), Metric.infDist x t ≤ r := by
  intro x hx
  apply infDist_le_of_mem_closure (s := starAlgebraBall (iSup A)) ?_ ?_
  · intro y hy
    have hymem : y ∈ ⋃ n, (A n : Set (H →L[ℂ] H)) := by
      rw [← StarSubalgebra.coe_iSup_of_directed hA.directed_le]
      exact hy.1
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hymem
    exact hnear n y ⟨hn, hy.2⟩
  · change x ∈ closure {y | y ∈ (iSup A).toSubalgebra.toSubmodule ∧ ‖y‖ ≤ 1}
    rw [closure_submodule_unitBall]
    exact hx

/-- The alternating countable construction produces nearby closed separable
test algebras containing any prescribed finite operator tests. -/
theorem exists_near_separable_algebra_pair_countable (M N : VonNeumannAlgebra H)
    (E F : Set (H →L[ℂ] H)) (hEc : E.Countable) (hFc : F.Countable)
    (hE : ∀ x ∈ E, x ∈ M) (hF : ∀ x ∈ F, x ∈ N)
    {g : ℝ} (hg : kkDistance M N < g) :
    ∃ A B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      A ≤ M.toStarSubalgebra ∧ B ≤ N.toStarSubalgebra ∧
      (∀ x ∈ E, x ∈ A) ∧ (∀ x ∈ F, x ∈ B) ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g := by
  obtain ⟨r, hr, hrg⟩ := exists_between hg
  let p : SeparableSeeds M N :=
    ⟨E, F, hEc, hFc, hE, hF⟩
  let A (n : ℕ) := cstarHull (p.stages hr n).left
  let B (n : ℕ) := cstarHull (p.stages hr n).right
  have hA : Monotone A := cstarHull_mono.comp (p.stages_left_mono hr)
  have hB : Monotone B := cstarHull_mono.comp (p.stages_right_mono hr)
  have hAM : increasingCstarClosure A ≤ M.toStarSubalgebra :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun n => cstarHull_le M (p.stages hr n).left_mem) (isClosed_algebra M)
  have hBN : increasingCstarClosure B ≤ N.toStarSubalgebra :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun n => cstarHull_le N (p.stages hr n).right_mem) (isClosed_algebra N)
  refine ⟨increasingCstarClosure A, increasingCstarClosure B,
    StarSubalgebra.isClosed_topologicalClosure _, StarSubalgebra.isClosed_topologicalClosure _,
    isSeparable_increasingCstarClosure A hA
      (fun n => isSeparable_cstarHull (p.stages hr n).left_countable),
    isSeparable_increasingCstarClosure B hB
      (fun n => isSeparable_cstarHull (p.stages hr n).right_countable),
    hAM, hBN, ?_, ?_, ?_⟩
  · intro x hx
    exact le_increasingCstarClosure A 0 (subset_cstarHull p.left hx)
  · intro x hx
    exact le_increasingCstarClosure B 0 (subset_cstarHull p.right hx)
  · apply lt_of_le_of_lt (Metric.hausdorffDist_le_of_infDist
      ((kkDistance_nonneg M N).trans hr.le) ?_ ?_) hrg
    · apply infDist_increasingCstarClosure_ball A hA
      intro n x hx
      have hnext := ((p.stages hr n).next_spec hr).2.2.1 x hx
      apply le_trans (Metric.infDist_le_infDist_of_subset (t :=
        starAlgebraBall (increasingCstarClosure B)) ?_
        ⟨0, zero_mem_starAlgebraBall _⟩) hnext
      intro y hy
      exact ⟨le_increasingCstarClosure B (n + 1) hy.1, hy.2⟩
    · apply infDist_increasingCstarClosure_ball B hB
      intro n x hx
      have hnext := ((p.stages hr n).next_spec hr).2.2.2 x hx
      apply le_trans (Metric.infDist_le_infDist_of_subset (t :=
        starAlgebraBall (increasingCstarClosure A)) ?_
        ⟨0, zero_mem_starAlgebraBall _⟩) hnext
      intro y hy
      exact ⟨le_increasingCstarClosure A (n + 1) hy.1, hy.2⟩

/-- Finite prescribed tests are a special case of the countable construction. -/
theorem exists_near_separable_algebra_pair (M N : VonNeumannAlgebra H)
    (E F : Finset (H →L[ℂ] H)) (hE : ∀ x ∈ E, x ∈ M) (hF : ∀ x ∈ F, x ∈ N)
    {g : ℝ} (hg : kkDistance M N < g) :
    ∃ A B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      A ≤ M.toStarSubalgebra ∧ B ≤ N.toStarSubalgebra ∧
      (∀ x ∈ E, x ∈ A) ∧ (∀ x ∈ F, x ∈ B) ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g :=
  exists_near_separable_algebra_pair_countable M N E F E.countable_toSet F.countable_toSet hE hF hg

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableReducingSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A separable reducing subspace containing finitely many vectors

The closed complex span of the algebra orbits of a finite vector family
is separable when the algebra is norm separable. It is invariant under
the algebra and its adjoints, so its orthogonal projection commutes with
every element of the algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finiteAlgebraOrbit_subset (A : StarSubalgebra ℂ (H →L[ℂ] H)) (V : Finset H) :
    finiteAlgebraOrbit A V ⊆ finiteReducingSpace A V :=
  (Submodule.subset_span).trans (Submodule.le_topologicalClosure _)

theorem mem_finiteReducingSpace (A : StarSubalgebra ℂ (H →L[ℂ] H)) (V : Finset H)
    {v : H} (hv : v ∈ V) : v ∈ finiteReducingSpace A V := by
  apply finiteAlgebraOrbit_subset A V
  exact ⟨(1, ⟨v, hv⟩), by simp⟩

theorem isClosed_finiteReducingSpace (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (V : Finset H) : IsClosed (finiteReducingSpace A V : Set H) :=
  Submodule.isClosed_topologicalClosure _

theorem isSeparable_finiteAlgebraOrbit (A : StarSubalgebra ℂ (H →L[ℂ] H))
    [TopologicalSpace.SeparableSpace A] (V : Finset H) :
    TopologicalSpace.IsSeparable (finiteAlgebraOrbit A V) := by
  apply TopologicalSpace.isSeparable_range
  exact (continuous_subtype_val.comp continuous_fst).clm_apply
    (continuous_subtype_val.comp continuous_snd)

instance finiteReducingSpaceSeparable (A : StarSubalgebra ℂ (H →L[ℂ] H))
    [TopologicalSpace.SeparableSpace A] (V : Finset H) :
    TopologicalSpace.SeparableSpace (finiteReducingSpace A V) := by
  have hs : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (finiteAlgebraOrbit A V) : Set H) :=
    (isSeparable_finiteAlgebraOrbit A V).span
  exact hs.closure.separableSpace

theorem finiteReducingSpace_invariant (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (V : Finset H) (a : A) {x : H} (hx : x ∈ finiteReducingSpace A V) :
    (a : H →L[ℂ] H) x ∈ finiteReducingSpace A V := by
  have h : finiteReducingSpace A V ≤
      (finiteReducingSpace A V).comap (a : H →L[ℂ] H).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨b, v⟩, rfl⟩
      apply finiteAlgebraOrbit_subset A V
      exact ⟨(a * b, v), rfl⟩
    · exact (isClosed_finiteReducingSpace A V).preimage
        (a : H →L[ℂ] H).continuous
  exact h hx

/-- The actual closed separable reducing subspace needed for finitely
many vector tests, with its projection commutation stated explicitly. -/
theorem exists_separable_reducingSpace (A : StarSubalgebra ℂ (H →L[ℂ] H))
    [TopologicalSpace.SeparableSpace A] (V : Finset H) :
    ∃ K : Submodule ℂ H, IsClosed (K : Set H) ∧
      TopologicalSpace.SeparableSpace K ∧
      (∀ v ∈ V, v ∈ K) ∧
      (∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K) :=
  ⟨finiteReducingSpace A V, isClosed_finiteReducingSpace A V, inferInstance,
    fun _ hv => mem_finiteReducingSpace A V hv,
    fun a _ hx => finiteReducingSpace_invariant A V a hx⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common separable reducing spaces for nearby test algebras

The countable dense generators of both algebras generate one separable
ambient C*-algebra. Its finite-vector orbit supplies the common reducing
space, including when the original Hilbert space is not separable.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_separable_common_superalgebra
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H))) :
    ∃ C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsSeparable (C : Set (H →L[ℂ] H)) ∧ A ≤ C ∧ B ≤ C := by
  obtain ⟨s, hsA, hsc, hAs⟩ := hA.exists_countable_dense_subset
  obtain ⟨t, htB, htc, hBt⟩ := hB.exists_countable_dense_subset
  refine ⟨cstarHull (s ∪ t), isSeparable_cstarHull (hsc.union htc), ?_, ?_⟩
  · exact hAs.trans (closure_minimal
      (Set.subset_union_left.trans (subset_cstarHull (s ∪ t)))
      (StarSubalgebra.isClosed_topologicalClosure _))
  · exact hBt.trans (closure_minimal
      (Set.subset_union_right.trans (subset_cstarHull (s ∪ t)))
      (StarSubalgebra.isClosed_topologicalClosure _))

/-- One closed separable subspace reduces both algebras and contains
the finite prescribed vectors. -/
theorem exists_common_separable_reducingSpace
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H))) (V : Finset H) :
    ∃ K : Submodule ℂ H, IsClosed (K : Set H) ∧ SeparableSpace K ∧
      (∀ v ∈ V, v ∈ K) ∧
      (∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K) ∧
      (∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K) := by
  obtain ⟨C, hCsep, hAC, hBC⟩ := exists_separable_common_superalgebra A B hA hB
  let : SeparableSpace C := hCsep.separableSpace
  obtain ⟨K, hKclosed, hKsep, hVK, hCK⟩ := exists_separable_reducingSpace C V
  exact ⟨K, hKclosed, hKsep, hVK,
    fun a x hx => hCK ⟨a.val, hAC a.property⟩ x hx,
    fun b x hx => hCK ⟨b.val, hBC b.property⟩ x hx⟩

/-- The algebra and reducing-space portions of the separable tests lemma. -/
theorem exists_near_separable_tests (M N : VonNeumannAlgebra H)
    (E F : Finset (H →L[ℂ] H)) (V : Finset H)
    (hE : ∀ x ∈ E, x ∈ M) (hF : ∀ x ∈ F, x ∈ N)
    {g : ℝ} (hg : kkDistance M N < g) :
    ∃ (A B : StarSubalgebra ℂ (H →L[ℂ] H)) (K : Submodule ℂ H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      A ≤ M.toStarSubalgebra ∧ B ≤ N.toStarSubalgebra ∧
      (∀ x ∈ E, x ∈ A) ∧ (∀ x ∈ F, x ∈ B) ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g ∧
      IsClosed (K : Set H) ∧ SeparableSpace K ∧ (∀ v ∈ V, v ∈ K) ∧
      (∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K) ∧
      (∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K) := by
  obtain ⟨A, B, hAc, hBc, hAs, hBs, hAM, hBN, hEA, hFB, hdist⟩ :=
    exists_near_separable_algebra_pair M N E F hE hF hg
  obtain ⟨K, hKc, hKs, hVK, hAK, hBK⟩ :=
    exists_common_separable_reducingSpace A B hAs hBs V
  exact ⟨A, B, K, hAc, hBc, hAs, hBs, hAM, hBN, hEA, hFB, hdist,
    hKc, hKs, hVK, hAK, hBK⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reduction of the universal theorem to separable Hilbert spaces

Local restrictions to separable reducing spaces give finite coefficient
approximants and then a conjugacy on the original Hilbert space.
The tolerance precedes every ambient space.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

universe u

local instance reductionFactorOrder_ra79b1f_1 {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance reductionFactorStarOrder_ra79b1f_1 {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
theorem finiteCoefficientConjugations_of_separable_bound_oai
    (hK : PublishedKaplanskyDensity.{u}) {a δ : ℝ}
    (hsep : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [SeparableSpace K], ∀ P Q : VonNeumannAlgebra K,
        kkDistance P Q < δ → NearConjugacy P Q a)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M N : VonNeumannAlgebra H) (hgap : kkDistance M N < δ) :
    FiniteCoefficientConjugations M N a := by
  classical
  intro E V k
  obtain ⟨g, hgapg, hgδ⟩ := exists_between hgap
  let E' : Finset (H →L[ℂ] H) := E.image Subtype.val
  have hE' : ∀ x ∈ E', x ∈ M := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  obtain ⟨A, B, K, hAc, hBc, _, _, _, hBN, hEA, _, hAB,
      hKc, hKs, hVK, hAK, hBK⟩ :=
    exists_near_separable_tests M N E' ∅ V hE' (by simp) hgapg
  let : CompleteSpace K := hKc.completeSpace_coe
  let : SeparableSpace K := hKs
  let P := generatedVonNeumannAlgebra (reducingRestriction K A hAK).range
  let Q := generatedVonNeumannAlgebra (reducingRestriction K B hBK).range
  have hPQ : kkDistance P Q < δ :=
    ((kkDistance_generated_restriction_le hK K A B hAK hBK hAc hBc).trans_lt hAB).trans hgδ
  obtain ⟨v, hv, hva⟩ := hsep K P Q hPQ
  refine ⟨cornerUnitary K v, (norm_cornerUnitary_sub_one K v).le.trans hva.le, ?_⟩
  intro x hx
  let xA : A := ⟨x.val, hEA x.val (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
  have hxP : reducingRestriction K A hAK xA ∈ P :=
    subset_generatedVonNeumannAlgebra _ ⟨xA, rfl⟩
  have hxQ : unitaryConj v (reducingRestriction K A hAK xA) ∈ Q := by
    change unitaryConj v (reducingRestriction K A hAK xA) ∈ (Q : Set (K →L[ℂ] K))
    rw [← hv]
    exact ⟨_, hxP, rfl⟩
  have hxQ' : unitaryConj v (reducingRestriction K A hAK xA) ∈
      Set.centralizer (Set.centralizer (Set.range (reducingRestriction K B hBK))) := by
    change unitaryConj v (reducingRestriction K A hAK xA) ∈
      (generatedVonNeumannAlgebra (reducingRestriction K B hBK).range : Set _) at hxQ
    rw [generatedVonNeumannAlgebra_coe] at hxQ
    exact hxQ
  obtain ⟨b, hb⟩ := exists_original_coefficient_approx K A B hAK hBK v xA hxQ' V hVK
    (show 0 < (1 : ℝ) / (k + 1) by positivity)
  refine ⟨⟨b.val, hBN b.property⟩, ?_⟩
  intro ξ hξ η hη
  exact hb ξ hξ η hη

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.finiteCoefficientConjugations_of_separable_bound_oai.{u} := @OAI.KadisonKastler.finiteCoefficientConjugations_of_separable_bound_oai.{u}
