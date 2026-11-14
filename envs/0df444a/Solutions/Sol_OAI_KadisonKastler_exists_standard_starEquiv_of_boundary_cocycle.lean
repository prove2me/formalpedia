-- Prove2me | solution 1 for OAI.KadisonKastler.exists_standard_starEquiv_of_boundary_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:54:31.785565+00:00
-- url     : https://prove2.me/submissions/fb7986a6-78b9-4d69-9536-bcc6a32af6e8

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
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
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
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K032
import Definitions.Def_Q260K069
import Theorems.Thm_OAI_KadisonKastler_StandardTracialPosition_exists_ae_diagonal_unitary_comparison
import Theorems.Thm_OAI_KadisonKastler_StandardTracialPosition_scalar_of_diagonal_invariant
import Theorems.Thm_OAI_KadisonKastler_exists_near_starEquiv_of_traceDense_unitary_images
import Theorems.Thm_OAI_KadisonKastler_exists_product_boundary_intertwiner

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- Errors add when two unitary changes of position are composed. -/
theorem norm_unitary_mul_sub_one_le (v w : unitary (H →L[ℂ] H)) :
    ‖((v * w : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ ≤
      ‖(v : H →L[ℂ] H) - 1‖ + ‖(w : H →L[ℂ] H) - 1‖ := by
  have hid : (v : H →L[ℂ] H) * (w : H →L[ℂ] H) - 1 =
      (v : H →L[ℂ] H) * ((w : H →L[ℂ] H) - 1) + ((v : H →L[ℂ] H) - 1) := by
    noncomm_ring
  change ‖(v : H →L[ℂ] H) * (w : H →L[ℂ] H) - 1‖ ≤ _
  rw [hid]
  exact (norm_add_le _ _).trans_eq (by simp [add_comm])

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NonsingularBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonsingular boundary actions and simultaneous representatives

The action preserves null sets, not necessarily the measure. Countability
allows all the identities used in the boundary argument to hold on one
invariant conull set. The final definition isolates the exact unitary
coefficient property in Björklund, arXiv:1406.0763, Theorem 2.1 and
Remark 2.2, expressed as a property of the unitary coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {G D : Type*} [Group G] [MeasurableSpace D]

namespace NonsingularAction

variable {μ : Measure D} (α : NonsingularAction G D μ)

/-- A conull set contains a point when the measure is nonzero. -/
theorem exists_simultaneous_point [Countable G] [NeZero μ]
    {ι : Type*} [Countable ι] (P : ι → D → Prop)
    (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ x, ∀ g i, P i (α.toPerm g x) := by
  have h : ∀ᵐ x ∂μ, ∀ g i, P i (α.toPerm g x) :=
    eventually_countable_forall.mpr fun g =>
      eventually_countable_forall.mpr fun i => (α.quasi g).ae (hP i)
  exact h.exists

end NonsingularAction

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryErgodicReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.leftOnProduct_apply _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonKastler.randomWalkPathAction_apply _root_.OAI.KadisonKastler.shiftBoundaryAction_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the boundary variables by double ergodicity

The diagonal comparison gives the vector field `L* a Ω`.  Its covariance
is derived from the product intertwiner and the tracial right action.
Double ergodicity is used only for this actual bounded measurable field.
-/

namespace KadisonKastler

universe uG uD uH

open MeasureTheory Filter

noncomputable section

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator identity behind the equivariance of `L* a Ω`. -/
theorem boundary_intertwiner_adjoint (L K U V : unitary (H →L[ℂ] H))
    (h : (L : H →L[ℂ] H) * U = (V : H →L[ℂ] H) * K) :
    star (L : H →L[ℂ] H) * V = (U : H →L[ℂ] H) * star (K : H →L[ℂ] H) := by
  calc
    _ = (star (L : H →L[ℂ] H) * ((V : H →L[ℂ] H) * K)) *
        star (K : H →L[ℂ] H) := by
      simp only [mul_assoc, Unitary.mul_star_self_of_mem K.property, mul_one]
    _ = (star (L : H →L[ℂ] H) * ((L : H →L[ℂ] H) * U)) *
        star (K : H →L[ℂ] H) := by rw [h]
    _ = _ := by
      simp only [← mul_assoc, Unitary.star_mul_self_of_mem L.property, one_mul]

/-- Diagonal covariance follows from the genuine right-action identities. -/
theorem boundary_comparison_vector_covariance
    (L K U W Z R a b : unitary (H →L[ℂ] H)) (Ω : H)
    (hL : (L : H →L[ℂ] H) * U = ((W : H →L[ℂ] H) * R) * K)
    (ha : (a : H →L[ℂ] H) = ((W : H →L[ℂ] H) * b) * star (Z : H →L[ℂ] H))
    (hR : (R : H →L[ℂ] H) * b = (b : H →L[ℂ] H) * R)
    (hΩ : (R : H →L[ℂ] H) Ω = star (Z : H →L[ℂ] H) Ω) :
    star (L : H →L[ℂ] H) ((a : H →L[ℂ] H) Ω) =
      (U : H →L[ℂ] H) (star (K : H →L[ℂ] H) ((b : H →L[ℂ] H) Ω)) := by
  have hi := boundary_intertwiner_adjoint L K U (W * R) hL
  have hr := congrArg (fun t : H →L[ℂ] H => t Ω) hR
  change (R : H →L[ℂ] H) ((b : H →L[ℂ] H) Ω) =
    (b : H →L[ℂ] H) ((R : H →L[ℂ] H) Ω) at hr
  rw [hΩ] at hr
  rw [ha]
  change star (L : H →L[ℂ] H)
    ((W : H →L[ℂ] H) ((b : H →L[ℂ] H) (star (Z : H →L[ℂ] H) Ω))) = _
  rw [← hr]
  exact congrArg (fun t : H →L[ℂ] H => t ((b : H →L[ℂ] H) Ω)) hi

/-- A constant unit vector of the form `L* a Ω = z Ω` gives the normalized
unitary `z a* L` fixing `Ω`. -/
theorem normalized_boundary_unitary_fixes
    (L a : unitary (H →L[ℂ] H)) (Ω : H) (z : ℂ) (hz : ‖z‖ = 1)
    (hv : star (L : H →L[ℂ] H) ((a : H →L[ℂ] H) Ω) = z • Ω) :
    ((scalarUnitaryOfNormOne z hz * star a * L : unitary (H →L[ℂ] H)) :
      H →L[ℂ] H) Ω = Ω := by
  have h := congrArg (fun ξ => star (a : H →L[ℂ] H) ((L : H →L[ℂ] H) ξ)) hv
  have hLL (ξ : H) : (L : H →L[ℂ] H) (star (L : H →L[ℂ] H) ξ) = ξ :=
    congrArg (fun t : H →L[ℂ] H => t ξ) (Unitary.mul_star_self_of_mem L.property)
  have haa (ξ : H) : star (a : H →L[ℂ] H) ((a : H →L[ℂ] H) ξ) = ξ :=
    congrArg (fun t : H →L[ℂ] H => t ξ) (Unitary.star_mul_self_of_mem a.property)
  change z • (star (a : H →L[ℂ] H) ((L : H →L[ℂ] H) Ω)) = Ω
  simpa only [map_smul, hLL, haa] using h.symm

theorem normalized_boundary_unitary_distance
    (L a : unitary (H →L[ℂ] H)) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖((scalarUnitaryOfNormOne z hz * star a * L : unitary (H →L[ℂ] H)) :
      H →L[ℂ] H) - 1‖ ≤
      ‖z - 1‖ + ‖(a : H →L[ℂ] H) - 1‖ + ‖(L : H →L[ℂ] H) - 1‖ := by
  have hs : ‖((scalarUnitaryOfNormOne (H := H) z hz : unitary (H →L[ℂ] H)) :
      H →L[ℂ] H) - 1‖ ≤ ‖z - 1‖ := by
    change ‖z • (1 : H →L[ℂ] H) - 1‖ ≤ _
    have heq : z • (1 : H →L[ℂ] H) - 1 = (z - 1) • (1 : H →L[ℂ] H) := by
      rw [sub_smul, one_smul]
    rw [heq, norm_smul]
    have h₁ : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
      norm_unitary_le_one (1 : unitary (H →L[ℂ] H))
    calc
      _ ≤ ‖z - 1‖ * 1 := mul_le_mul_of_nonneg_left h₁ (norm_nonneg _)
      _ = _ := mul_one _
  have ha : ‖((star a : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(a : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((a : H →L[ℂ] H) - 1)
  exact (norm_unitary_mul_sub_one_le (scalarUnitaryOfNormOne z hz * star a) L).trans
    (add_le_add ((norm_unitary_mul_sub_one_le (scalarUnitaryOfNormOne z hz)
      (star a)).trans (add_le_add hs ha.le)) le_rfl)

/-- The one-sided product intertwiner gives the precise unitary image of
each group vector after scalar normalization. -/
theorem normalized_boundary_unitary_image
    (L K a b U W : unitary (H →L[ℂ] H)) (Ω : H) (z : ℂ)
    (hL : (L : H →L[ℂ] H) * U = (W : H →L[ℂ] H) * K)
    (hK : star (K : H →L[ℂ] H) ((b : H →L[ℂ] H) Ω) = z • Ω) :
    (z • (star (a : H →L[ℂ] H) * L)) ((U : H →L[ℂ] H) Ω) =
      (star (a : H →L[ℂ] H) * W * b) Ω := by
  have hb := congrArg (fun ξ => (K : H →L[ℂ] H) ξ) hK
  have hKK (ξ : H) : (K : H →L[ℂ] H) (star (K : H →L[ℂ] H) ξ) = ξ :=
    congrArg (fun t : H →L[ℂ] H => t ξ) (Unitary.mul_star_self_of_mem K.property)
  have hb' : (b : H →L[ℂ] H) Ω = z • (K : H →L[ℂ] H) Ω := by
    simpa only [map_smul, hKK] using hb
  change z • (star (a : H →L[ℂ] H) ((L : H →L[ℂ] H) ((U : H →L[ℂ] H) Ω))) = _
  have hLΩ : (L : H →L[ℂ] H) ((U : H →L[ℂ] H) Ω) =
      (W : H →L[ℂ] H) ((K : H →L[ℂ] H) Ω) :=
    congrArg (fun t : H →L[ℂ] H => t Ω) hL
  rw [hLΩ]
  simpa only [mul_apply_eq_comp, map_smul] using
    congrArg (fun ξ => star (a : H →L[ℂ] H) ((W : H →L[ℂ] H) ξ)) hb'.symm

/-- The image unitaries stay close to the original group elements. -/
theorem boundary_unitary_image_distance (a b W U : unitary (H →L[ℂ] H)) :
    ‖star (a : H →L[ℂ] H) * W * b - U‖ ≤
      ‖(a : H →L[ℂ] H) - 1‖ + ‖(W : H →L[ℂ] H) - U‖ +
        ‖(b : H →L[ℂ] H) - 1‖ := by
  calc
    _ ≤ ‖star (a : H →L[ℂ] H) * W * b - (W : H →L[ℂ] H) * b‖ +
        ‖(W : H →L[ℂ] H) * b - U‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (star (a : H →L[ℂ] H) * W * b) ((W : H →L[ℂ] H) * b) (U : H →L[ℂ] H)
    _ ≤ ‖star (a : H →L[ℂ] H) * W * b - (W : H →L[ℂ] H) * b‖ +
        (‖(W : H →L[ℂ] H) * b - (U : H →L[ℂ] H) * b‖ +
          ‖(U : H →L[ℂ] H) * b - U‖) := by
      have ht : ‖(W : H →L[ℂ] H) * b - U‖ ≤
          ‖(W : H →L[ℂ] H) * b - (U : H →L[ℂ] H) * b‖ +
            ‖(U : H →L[ℂ] H) * b - U‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          ((W : H →L[ℂ] H) * b) ((U : H →L[ℂ] H) * b) (U : H →L[ℂ] H)
      exact add_le_add le_rfl ht
    _ = _ := by
      have h₁ : star (a : H →L[ℂ] H) * W * b - (W : H →L[ℂ] H) * b =
          (star (a : H →L[ℂ] H) - 1) * W * b := by noncomm_ring
      have h₂ : (W : H →L[ℂ] H) * b - (U : H →L[ℂ] H) * b =
          ((W : H →L[ℂ] H) - U) * b := by noncomm_ring
      have h₃ : (U : H →L[ℂ] H) * b - U =
          (U : H →L[ℂ] H) * ((b : H →L[ℂ] H) - 1) := by noncomm_ring
      rw [h₁, h₂, h₃]
      simp only [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
      have ha : star (a : H →L[ℂ] H) - 1 = star ((a : H →L[ℂ] H) - 1) := by simp
      rw [ha, norm_star]
      ring

end Operators

section Ergodic

variable {G : Type uG} {D : Type uD} {H : Type uH} [Group G] [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {μ : Measure D} [SFinite μ] [NeZero (μ.prod μ)]

/-- Applying genuine double ergodicity to the diagonal comparison field
produces its scalar phase and the quantitative near-one bound. -/
theorem exists_boundary_scalar_of_doubleErgodic
    (α : NonsingularAction G D μ) (herg : UnitaryDoubleErgodic.{uG, uD, uH} α)
    (σ : G →* unitary (H →L[ℂ] H)) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hfixed : ∀ v : H, (∀ g, (σ g : H →L[ℂ] H) v = v) → ∃ z : ℂ, v = z • Ω)
    (L a : D × D → unitary (H →L[ℂ] H))
    (hLm : ∀ ξ, AEStronglyMeasurable
      (fun p => star (L p : H →L[ℂ] H) ξ) (μ.prod μ))
    (ham : AEStronglyMeasurable (fun p => (a p : H →L[ℂ] H) Ω) (μ.prod μ))
    (hcov : ∀ g, ∀ᵐ p ∂μ.prod μ,
      star (L (α.diagonal.toPerm g p) : H →L[ℂ] H)
        ((a (α.diagonal.toPerm g p) : H →L[ℂ] H) Ω) =
      (σ g : H →L[ℂ] H) (star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω)))
    {ε : ℝ} (hnear : ∀ᵐ p ∂μ.prod μ,
      ‖star (L p : H →L[ℂ] H) * (a p : H →L[ℂ] H) - 1‖ ≤ ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖z - 1‖ ≤ ε ∧
      (∀ᵐ p ∂μ.prod μ,
        star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω) := by
  let f : D × D → H := fun p =>
    star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω)
  have hfm : AEStronglyMeasurable f (μ.prod μ) :=
    aestronglyMeasurable_field_apply _ hLm _ ham
  have hfn (p : D × D) : ‖f p‖ = 1 := by
    dsimp [f]
    rw [← Unitary.coe_star, Unitary.norm_map, Unitary.norm_map, hΩ]
  obtain ⟨v, hv, hfv⟩ := herg H σ f hfm
    ⟨1, Eventually.of_forall fun p => (hfn p).le⟩ hcov
  obtain ⟨z, rfl⟩ := hfixed v hv
  have hz : ‖z‖ = 1 := by
    obtain ⟨p, hp⟩ := hfv.exists
    have hh := hfn p
    rw [hp, norm_smul, hΩ, mul_one] at hh
    exact hh
  refine ⟨z, hz, ?_, hfv⟩
  have hh : ∀ᵐ p ∂μ.prod μ, ‖z - 1‖ ≤ ε := by
    filter_upwards [hfv, hnear] with p hp hn
    have hb := ContinuousLinearMap.le_opNorm
      (star (L p : H →L[ℂ] H) * (a p : H →L[ℂ] H) - 1) Ω
    change ‖f p - Ω‖ ≤ _ at hb
    have heq : z • Ω - Ω = (z - 1) • Ω := by rw [sub_smul, one_smul]
    rw [hp, heq, norm_smul, hΩ, mul_one, mul_one] at hb
    exact hb.trans hn
  exact hh.exists.choose_spec

/-- The field used in double ergodicity is equivariant as a consequence
of the product intertwiner, diagonal comparison and tracial right action. -/
theorem exists_boundary_scalar_from_comparison
    (α : NonsingularAction G D μ) (herg : UnitaryDoubleErgodic.{uG, uD, uH} α)
    (σ : G →* unitary (H →L[ℂ] H)) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hfixed : ∀ v : H, (∀ g, (σ g : H →L[ℂ] H) v = v) → ∃ z : ℂ, v = z • Ω)
    (L a : D × D → unitary (H →L[ℂ] H))
    (W R : G → D → unitary (H →L[ℂ] H))
    (hLm : ∀ ξ, AEStronglyMeasurable
      (fun p => star (L p : H →L[ℂ] H) ξ) (μ.prod μ))
    (ham : AEStronglyMeasurable (fun p => (a p : H →L[ℂ] H) Ω) (μ.prod μ))
    (hL : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (L p : H →L[ℂ] H) * σ g =
        ((W g p.1 : H →L[ℂ] H) * R g p.2) * L (α.diagonal.toPerm g⁻¹ p))
    (ha : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (a p : H →L[ℂ] H) =
        ((W g p.1 : H →L[ℂ] H) * a (α.diagonal.toPerm g⁻¹ p)) *
          star (W g p.2 : H →L[ℂ] H))
    (hR : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (R g p.2 : H →L[ℂ] H) * a (α.diagonal.toPerm g⁻¹ p) =
        (a (α.diagonal.toPerm g⁻¹ p) : H →L[ℂ] H) * R g p.2)
    (hRΩ : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (R g p.2 : H →L[ℂ] H) Ω = star (W g p.2 : H →L[ℂ] H) Ω)
    {ε : ℝ} (hnear : ∀ᵐ p ∂μ.prod μ,
      ‖star (L p : H →L[ℂ] H) * (a p : H →L[ℂ] H) - 1‖ ≤ ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖z - 1‖ ≤ ε ∧
      (∀ᵐ p ∂μ.prod μ,
        star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω) := by
  apply exists_boundary_scalar_of_doubleErgodic α herg σ Ω hΩ hfixed L a hLm ham ?_ hnear
  intro g
  have hback : ∀ᵐ p ∂μ.prod μ,
      star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) =
        (σ g : H →L[ℂ] H) (star (L (α.diagonal.toPerm g⁻¹ p) : H →L[ℂ] H)
          ((a (α.diagonal.toPerm g⁻¹ p) : H →L[ℂ] H) Ω)) := by
    filter_upwards [hL g, ha g, hR g, hRΩ g] with p hp hpa hpr hpΩ
    exact boundary_comparison_vector_covariance (L p) (L (α.diagonal.toPerm g⁻¹ p))
      (σ g) (W g p.1) (W g p.2) (R g p.2) (a p) (a (α.diagonal.toPerm g⁻¹ p)) Ω
      hp hpa hpr hpΩ
  filter_upwards [(α.diagonal.quasi g).ae hback] with p hp
  have hs : α.diagonal.toPerm g⁻¹ (α.diagonal.toPerm g p) = p := by
    rw [← α.diagonal.mul_apply, inv_mul_cancel, α.diagonal.one_apply]
  simpa only [hs] using hp

omit [TopologicalSpace.SeparableSpace H] in
/-- Choose one pair on which the scalar-vector relation and all group
intertwiners hold simultaneously, including their separate translates. -/
theorem exists_simultaneous_boundary_normalization [Countable G]
    (α : NonsingularAction G D μ) (Ω : H)
    (L a : D × D → unitary (H →L[ℂ] H))
    (U : G → unitary (H →L[ℂ] H)) (W : G → D → unitary (H →L[ℂ] H))
    (z : ℂ) (hz : ‖z‖ = 1)
    (hvec : ∀ᵐ p ∂μ.prod μ,
      star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω)
    (hL : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (L p : H →L[ℂ] H) * U g = (W g p.1 : H →L[ℂ] H) *
        L (α.toPerm g⁻¹ p.1, p.2))
    {εL εa εW : ℝ} (hznear : ‖z - 1‖ ≤ εL + εa)
    (hLn : ∀ᵐ p ∂μ.prod μ, ‖(L p : H →L[ℂ] H) - 1‖ ≤ εL)
    (ha : ∀ᵐ p ∂μ.prod μ, ‖(a p : H →L[ℂ] H) - 1‖ ≤ εa)
    (hW : ∀ g, ∀ᵐ p ∂μ.prod μ,
      ‖(W g p.1 : H →L[ℂ] H) - U g‖ ≤ εW) :
    ∃ (p : D × D) (S : unitary (H →L[ℂ] H)),
      (S : H →L[ℂ] H) Ω = Ω ∧
      ‖(S : H →L[ℂ] H) - 1‖ ≤ 2 * (εL + εa) ∧
      ∀ g, (S : H →L[ℂ] H) ((U g : H →L[ℂ] H) Ω) =
        ((star (a p) * W g p.1 * a (α.toPerm g⁻¹ p.1, p.2) :
          unitary (H →L[ℂ] H)) : H →L[ℂ] H) Ω ∧
        ‖((star (a p) * W g p.1 * a (α.toPerm g⁻¹ p.1, p.2) :
          unitary (H →L[ℂ] H)) : H →L[ℂ] H) - U g‖ ≤ 2 * εa + εW := by
  let P : G → D × D → Prop := fun g p =>
    ((L p : H →L[ℂ] H) * U g = (W g p.1 : H →L[ℂ] H) *
      L (α.toPerm g⁻¹ p.1, p.2)) ∧
    (star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω) ∧
    ‖(L p : H →L[ℂ] H) - 1‖ ≤ εL ∧
    ‖(a p : H →L[ℂ] H) - 1‖ ≤ εa ∧ ‖(W g p.1 : H →L[ℂ] H) - U g‖ ≤ εW
  have hP : ∀ g, ∀ᵐ p ∂μ.prod μ, P g p := by
    intro g
    filter_upwards [hL g, hvec, hLn, ha, hW g] with p hp hv hl ha hw
    exact ⟨hp, hv, hl, ha, hw⟩
  obtain ⟨p, hp⟩ := α.prod.exists_simultaneous_point P hP
  have hp0 (g : G) : P g p := by
    simpa only [NonsingularAction.prod_apply, α.one_apply] using hp (1, 1) g
  let S := scalarUnitaryOfNormOne z hz * star (a p) * L p
  refine ⟨p, S, normalized_boundary_unitary_fixes (L p) (a p) Ω z hz (hp0 1).2.1, ?_, ?_⟩
  · exact (normalized_boundary_unitary_distance (L p) (a p) z hz).trans
      (by linarith [(hp0 1).2.2.1, (hp0 1).2.2.2.1])
  intro g
  let q : D × D := (α.toPerm g⁻¹ p.1, p.2)
  have hq : P 1 q := by
    simpa only [NonsingularAction.prod_apply, α.one_apply] using hp (g⁻¹, 1) 1
  constructor
  · change (z • (star (a p : H →L[ℂ] H) * L p)) ((U g : H →L[ℂ] H) Ω) = _
    exact normalized_boundary_unitary_image (L p) (L q) (a p) (a q) (U g) (W g p.1)
      Ω z (hp0 g).1 hq.2.1
  · have hh := boundary_unitary_image_distance (a p) (a q) (W g p.1) (U g)
    exact hh.trans (by linarith [(hp0 g).2.2.2.1, (hp0 g).2.2.2.2, hq.2.2.2.1])

end Ergodic

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryFiniteIsomorphism
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # From a normalized boundary field to a finite-factor isomorphism

This joins the measurable simultaneous-point argument to the algebraic
unitary-image construction. The boundary comparison unitaries are required
to take values in the neighboring algebra, as supplied by the restricted
operator-field mean and the diagonal trace construction.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G D : Type*} [Group G] [Countable G] [MeasurableSpace D]
  {μ : Measure D} [SFinite μ] [NeZero (μ.prod μ)]
  {M N : VonNeumannAlgebra H}

/-- Once the scalar boundary relation has been obtained, the actual
algebra-valued comparison fields yield a nearby star isomorphism. -/
theorem exists_starEquiv_of_boundary_normalization
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (Ω : H)
    (hMΩ : ∀ a, ‖algebraVectorMap M Ω a‖ = traceTwoNorm τM a)
    (hNΩ : ∀ a, ‖algebraVectorMap N Ω a‖ = traceTwoNorm τN a)
    (ρ : G → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ g, traceTwoNorm τM ((u : Algebra M) - ρ g) < ε)
    (α : NonsingularAction G D μ)
    (L a : D × D → unitary (H →L[ℂ] H))
    (W : G → D → unitary (H →L[ℂ] H))
    (haN : ∀ p, (a p : H →L[ℂ] H) ∈ N)
    (hWN : ∀ g d, (W g d : H →L[ℂ] H) ∈ N)
    (z : ℂ) (hz : ‖z‖ = 1)
    (hvec : ∀ᵐ p ∂μ.prod μ,
      star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω)
    (hL : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (L p : H →L[ℂ] H) * ambientAlgebraUnitary (ρ g) =
        (W g p.1 : H →L[ℂ] H) * L (α.toPerm g⁻¹ p.1, p.2))
    {εL εa εW : ℝ} (hC : 0 ≤ 2 * εa + εW)
    (hznear : ‖z - 1‖ ≤ εL + εa)
    (hLn : ∀ᵐ p ∂μ.prod μ, ‖(L p : H →L[ℂ] H) - 1‖ ≤ εL)
    (han : ∀ᵐ p ∂μ.prod μ, ‖(a p : H →L[ℂ] H) - 1‖ ≤ εa)
    (hWn : ∀ g, ∀ᵐ p ∂μ.prod μ,
      ‖(W g p.1 : H →L[ℂ] H) - ambientAlgebraUnitary (ρ g)‖ ≤ εW)
    (hsmall : 3 * (2 * (2 * εa + εW)) + (2 * (2 * εa + εW)) ^ 2 < 2)
    (hgap : kkDistance M N + 2 * (2 * εa + εW) < 1) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      ∀ x, ‖(θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤
        2 * (2 * εa + εW) * ‖x‖ := by
  obtain ⟨p, S, hSΩ, _, hS⟩ := exists_simultaneous_boundary_normalization
    α Ω L a (fun g => ambientAlgebraUnitary (ρ g)) W z hz hvec hL hznear hLn han hWn
  have hS1 : (S : H →L[ℂ] H) (algebraVectorMap M Ω 1) =
      algebraVectorMap N Ω 1 := by
    change (S : H →L[ℂ] H) ((1 : H →L[ℂ] H) Ω) = (1 : H →L[ℂ] H) Ω
    simpa only [one_apply_eq_self] using hSΩ
  have himages (g : G) : ∃ v : unitary (Algebra N),
      algebraVectorMap N Ω v = (S : H →L[ℂ] H) (algebraVectorMap M Ω (ρ g)) ∧
      ‖(v : H →L[ℂ] H) - (ρ g : Algebra M)‖ ≤ 2 * εa + εW := by
    let q : D × D := (α.toPerm g⁻¹ p.1, p.2)
    let v : unitary (H →L[ℂ] H) := star (a p) * W g p.1 * a q
    have hvN : (v : H →L[ℂ] H) ∈ N := by
      exact N.toStarSubalgebra.mul_mem
        (N.toStarSubalgebra.mul_mem (N.toStarSubalgebra.star_mem' (haN p)) (hWN g p.1))
        (haN q)
    exact ⟨algebraUnitaryOfMem v hvN, (hS g).1.symm, (hS g).2⟩
  obtain ⟨θ, _, hθ⟩ := exists_near_starEquiv_of_traceDense_unitary_images hM hN
    τM τN hτM hτN (algebraVectorMap M Ω) (algebraVectorMap N Ω) hMΩ hNΩ
    ρ hρ S hS1 hC himages hsmall hgap
  exact ⟨θ, hθ⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StandardTracialPosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete standard tracial position

A faithful vector trace and cyclicity suffice to construct the standard
tracial conjugation. Its isometry and involution are proved rather than
included in the common-position input.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StandardTracialPosition

variable {M : VonNeumannAlgebra H} (p : StandardTracialPosition M)

theorem finiteVectorTrace : FiniteVectorTrace p.trace := by
  refine ⟨1, fun _ => p.vector, fun _ => p.vector, ?_⟩
  intro a
  simpa only [Fin.sum_univ_one] using p.trace_eq a

end StandardTracialPosition

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StandardBoundaryIsomorphism
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the boundary variables in common standard position

The product intertwiner, trace-diagonal comparison and double ergodicity
give an actual near-identity star isomorphism. The scalar invariant-vector
condition and the right-action identities are proved from standard position.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u v w

variable {H : Type u} {G : Type v} {D : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [Group G] [Countable G]
  [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace D]
  {μ : Measure D} [IsProbabilityMeasure μ] {M N : VonNeumannAlgebra H}

/-- A close algebra-valued measurable cocycle yields a nearby star
isomorphism, with constant `18δ`. -/
theorem exists_standard_starEquiv_of_boundary_cocycle_oai
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (hΩ : pM.vector = pN.vector)
    (α : NonsingularAction G D μ) (m₂ : ScalarBoundaryMean α.prod)
    (hTom : PublishedFieldTomiyama (G := G × G) (H := H) (μ := μ.prod μ))
    (herg : UnitaryDoubleErgodic.{v, w, u} α)
    (U : G →* unitary (Algebra M))
    (hU : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ g, traceTwoNorm pM.trace ((u : Algebra M) - U g) < ε)
    (W : G → D → unitary (Algebra N))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : Algebra N).val ξ) μ)
    (hc : ∀ g t, ∀ᵐ x ∂μ, (W (g * t) x : Algebra N) =
      (W g x : Algebra N) * W t (α.toPerm g⁻¹ x))
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hclose : ∀ g, ∀ᵐ x ∂μ,
      ‖(W g x : Algebra N).val - (U g : Algebra M).val‖ ≤ δ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) -
      (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ)
    (hproduct : 2 * δ + 2 * κ < 1) (hdiag : 2 * δ < 1)
    (hsmall : 3 * (18 * δ) + (18 * δ) ^ 2 < 2)
    (hgap : kkDistance M N + 18 * δ < 1) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      ∀ x, ‖(θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤ 18 * δ * ‖x‖ := by
  let W₀ : G → D → unitary (H →L[ℂ] H) :=
    fun g x => ambientAlgebraUnitary (W g x)
  have hc₀ (g t : G) : ∀ᵐ x ∂μ,
      (W₀ g x : H →L[ℂ] H) * W₀ t (α.toPerm g⁻¹ x) = W₀ (g * t) x := by
    filter_upwards [hc g t] with x hx
    exact congrArg Subtype.val hx.symm
  obtain ⟨L, hLm, hLn, hL⟩ := exists_product_boundary_intertwiner pM pN α m₂ hTom U W₀
    hW (fun g => Filter.Eventually.of_forall fun x => (W g x : Algebra N).property)
    hc₀ hδ hκ hproduct hclose hJ
  obtain ⟨aN, ham, han, hac⟩ := pN.exists_ae_diagonal_unitary_comparison α W hc hW
    (fun g => ambientAlgebraUnitary (U g)) hδ hdiag hclose
  let a : D × D → unitary (H →L[ℂ] H) :=
    fun x => ambientAlgebraUnitary (aN x.1 x.2)
  let R : G → D → unitary (H →L[ℂ] H) := fun g x =>
    conjugationUnitary pN.conjugation pN.conjugation_involutive (W₀ g x)
  have hLdiag (g : G) : ∀ᵐ x ∂μ.prod μ,
      (L x : H →L[ℂ] H) * pM.diagonalRepresentation U g =
        ((W₀ g x.1 : H →L[ℂ] H) * R g x.2) * L (α.diagonal.toPerm g⁻¹ x) :=
    hL (g, g)
  have hR (g : G) : ∀ᵐ x ∂μ.prod μ,
      (R g x.2 : H →L[ℂ] H) * a (α.diagonal.toPerm g⁻¹ x) =
        (a (α.diagonal.toPerm g⁻¹ x) : H →L[ℂ] H) * R g x.2 := by
    apply Filter.Eventually.of_forall
    intro x
    exact (pN.commute_conjugationOperator
      (a (α.diagonal.toPerm g⁻¹ x)) (W₀ g x.2)
      (aN _ _ : Algebra N).property (W g x.2 : Algebra N).property).eq.symm
  have hRΩ (g : G) : ∀ᵐ x ∂μ.prod μ,
      (R g x.2 : H →L[ℂ] H) pM.vector = star (W₀ g x.2 : H →L[ℂ] H) pM.vector := by
    apply Filter.Eventually.of_forall
    intro x
    change pN.conjugation ((W g x.2 : Algebra N).val (pN.conjugation pM.vector)) = _
    rw [hΩ, pN.conjugation_vector]
    exact pN.conjugation_algebraVector (W g x.2)
  have han₀ (x : D × D) : ‖(a x : H →L[ℂ] H) - 1‖ ≤ 4 * δ := han x.1 x.2
  have hnear : ∀ᵐ x ∂μ.prod μ,
      ‖star (L x : H →L[ℂ] H) * (a x : H →L[ℂ] H) - 1‖ ≤
        (4 * δ + 4 * κ) + 4 * δ := by
    filter_upwards [hLn] with x hx
    have ht := norm_unitary_mul_sub_one_le (star (L x)) (a x)
    have hstar : ‖((star (L x) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
        ‖(L x : H →L[ℂ] H) - 1‖ := by
      simpa only [Unitary.coe_star, star_sub, star_one] using
        norm_star ((L x : H →L[ℂ] H) - 1)
    rw [hstar] at ht
    exact ht.trans (add_le_add hx (han₀ x))
  obtain ⟨z, hz, hzn, hzvec⟩ := exists_boundary_scalar_from_comparison α herg
    (pM.diagonalRepresentation U) pM.vector pM.vector_norm
    (pM.scalar_of_diagonal_invariant U (traceHilbert_factor hM) hU)
    L a W₀ R
    (operator_adjoint_eval_aestronglyMeasurable _ hLm)
    (ham pM.vector) hLdiag
    (fun g => (hac g).mono fun x hx => congrArg Subtype.val hx)
    hR hRΩ hnear
  have hWone : ∀ᵐ x ∂μ, (W₀ 1 x : H →L[ℂ] H) = 1 := by
    filter_upwards [hc₀ 1 1] with x hx
    simp only [one_mul, inv_one, α.one_apply] at hx
    apply (Unitary.toUnits (W₀ 1 x)).isUnit.mul_left_cancel
    simpa only [Unitary.val_toUnits_apply, mul_one] using hx
  have hLleft (g : G) : ∀ᵐ x ∂μ.prod μ,
      (L x : H →L[ℂ] H) * ambientAlgebraUnitary (U g) =
        (W₀ g x.1 : H →L[ℂ] H) * L (α.toPerm g⁻¹ x.1, x.2) := by
    filter_upwards [hL (g, 1), (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hWone]
      with x hx hone
    change (L x : H →L[ℂ] H) * (U g : Algebra M).val =
      (W₀ g x.1 : H →L[ℂ] H) * L (α.toPerm g⁻¹ x.1, x.2)
    simpa only [productBoundaryRepresentation_coe, Prod.fst, Prod.snd, map_one,
      OneMemClass.coe_one, productBoundaryValue_coe, hone,
      conjugationOperator_one pM.conjugation pM.conjugation_involutive,
      conjugationOperator_one pN.conjugation pN.conjugation_involutive,
      mul_one, Prod.inv_mk, inv_one, NonsingularAction.prod_apply, Equiv.Perm.one_apply,
      α.one_apply] using hx
  have hnsmall : 3 * (2 * (2 * (4 * δ) + δ)) + (2 * (2 * (4 * δ) + δ)) ^ 2 < 2 := by
    nlinarith only [hsmall]
  obtain ⟨θ, hθ⟩ := exists_starEquiv_of_boundary_normalization hM hN
    pM.trace pN.trace pM.finiteVectorTrace pN.finiteVectorTrace pM.vector
    pM.vectorMap_norm (by simpa only [hΩ] using pN.vectorMap_norm)
    U hU α L a W₀
    (fun x => (aN x.1 x.2 : Algebra N).property)
    (fun g x => (W g x : Algebra N).property)
    z hz hzvec hLleft (by positivity) hzn hLn
    (Filter.Eventually.of_forall han₀)
    (fun g => (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hclose g))
    hnsmall (by nlinarith only [hgap])
  refine ⟨θ, fun x => ?_⟩
  convert hθ x using 1 <;> first | rfl | ring

end

end KadisonKastler

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.KadisonKastler.exists_standard_starEquiv_of_boundary_cocycle_oai.{u, v, w} := @OAI.KadisonKastler.exists_standard_starEquiv_of_boundary_cocycle_oai.{u, v, w}
