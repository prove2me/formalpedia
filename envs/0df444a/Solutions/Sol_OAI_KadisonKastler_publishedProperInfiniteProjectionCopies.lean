-- Prove2me | solution 1 for OAI.KadisonKastler.publishedProperInfiniteProjectionCopies
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:07:36.991292+00:00
-- url     : https://prove2.me/submissions/077f0ca0-8f26-4f1d-821d-b6afd3e19b35

import Mathlib
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
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
import Mathlib.Analysis.Normed.Module.WeakDual
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
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
import Mathlib.Logic.Equiv.Fin.Basic
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
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteFactorProperInfiniteness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
-- module Solutions.OAIQ075_KS.KadisonKastler_ProperInfiniteProjectionCopies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable copies of a full projection

A maximal orthogonal family with sources under a full projection gives a
countable partition of the identity.  Two orthogonal isometries provide
room for countably many copies of the full projection.  The partition
embeds into their sum, and concrete projection Schroeder--Bernstein moves
that sum onto the identity.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem exists_link_of_full (p q : AlgebraProjection M)
    (hp : (centralSupport p).val = 1) (hq : q.val ≠ 0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val ≠ 0 := by
  have ha : ∃ a : Algebra M, q.val * a * p.val ≠ 0 := by
    by_contra h
    have hz : ∀ a : Algebra M, q.val * a * p.val = 0 := by
      simpa only [not_exists, not_not] using h
    have hh := mul_centralSupport_eq_zero_of_no_links p q hz
    rw [hp, mul_one] at hh
    exact hq hh
  obtain ⟨a, ha⟩ := ha
  apply exists_partialIsometry_of_link p q (q.val * a * p.val)
  · rw [mul_assoc, p.property.isIdempotentElem.eq]
  · rw [← mul_assoc, ← mul_assoc, q.property.isIdempotentElem.eq]
  · exact ha

private theorem exists_maximal_fullSourceFamily (p : AlgebraProjection M) :
    ∃ s : Set (PartialIsometry M), Maximal (fullSourceFamily p) s := by
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

private theorem nonzero_target (v : PartialIsometry M)
    (hv : v.support.val ≠ 0) : v.target.val ≠ 0 := by
  intro hz
  have he := v.target_mul
  rw [hz, zero_mul] at he
  have hi := v.initial
  rw [← he, star_zero, zero_mul] at hi
  exact hv hi.symm

/-- A full projection is the source bound for a countable orthogonal
partition of the identity, even when the algebra is not a factor. -/
theorem exists_countable_source_partition_of_full [TopologicalSpace.SeparableSpace H]
    (p : AlgebraProjection M) (hp : (centralSupport p).val = 1) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support ≤ p) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) ∧
      (∀ q : AlgebraProjection M, (∀ n, (a n).target ≤ q) →
        (1 : Algebra M) = q.val) := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_fullSourceFamily p
  have hcount : Countable s := countable_of_orthogonal_nonzero_projections
    (fun v : s => v.val.target)
    (fun v => nonzero_target v.val ((hs.1 v.val v.property).2))
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
  let r : AlgebraProjection M := ⟨1 - q.val, q.property.one_sub⟩
  have hr : r.val ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨v, hvp, hvr, hv0⟩ := exists_link_of_full p r hp hr
  have hsq (w : PartialIsometry M) (hw : w ∈ s) : w.target ≤ q := by
    simpa only [ha ⟨w, hw⟩] using hq (Encodable.encode (⟨w, hw⟩ : s))
  have hov (w : PartialIsometry M) (hw : w ∈ s) :
      v.target.val * w.target.val = 0 := by
    have hrq : r.val * q.val = 0 := by
      change (1 - q.val) * q.val = 0
      rw [sub_mul, one_mul, q.property.isIdempotentElem.eq, sub_self]
    exact projection_orthogonal_of_le hrq hvr (hsq w hw)
  have hnew : fullSourceFamily p (insert v s) := by
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
  exact nonzero_target v hv0 hz

/-- Orthogonal projection sums are strong sums in the original representation. -/
theorem exists_orthogonal_projection_sum (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    ∃ q : AlgebraProjection M, (∀ i, p i ≤ q) ∧
      (∀ r : AlgebraProjection M, (∀ i, p i ≤ r) → q ≤ r) ∧
      ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x)
        ((q.val : H →L[ℂ] H) x) := by
  let a := finiteProjectionSum p ho
  have ha : Monotone a := by
    intro s t hst
    apply (AlgebraProjection.finsetSum_le_iff p s _ _).mpr
    intro i hi
    exact (AlgebraProjection.finsetSum_le_iff p t _ _).mp le_rfl i (hst hi)
  obtain ⟨q, hq⟩ := AlgebraProjection.exists_isLUB_monotone a ha
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    have hi : p i ≤ a {i} :=
      (AlgebraProjection.finsetSum_le_iff p {i} _ _).mp le_rfl i (by simp)
    exact hi.trans (hq.1 ⟨{i}, rfl⟩)
  · intro r hr
    apply hq.2
    rintro _ ⟨s, rfl⟩
    exact (AlgebraProjection.finsetSum_le_iff p s _ r).mpr (fun i _ => hr i)
  · intro x
    have hv := AlgebraProjection.vectorValue_tendsto_monotone a ha q hq x
    have hs (s : Finset ℕ) :
        ‖(q.val : H →L[ℂ] H) x - ((a s).val : H →L[ℂ] H) x‖ ^ 2 =
          AlgebraProjection.vectorValue x q - AlgebraProjection.vectorValue x (a s) := by
      have hh := AlgebraProjection.vectorValue_remainder x (a s) q (hq.1 ⟨s, rfl⟩)
      rw [AlgebraProjection.vectorValue_eq_norm_sq] at hh
      exact hh
    have hc : Tendsto (fun _ : Finset ℕ => AlgebraProjection.vectorValue x q)
        atTop (𝓝 (AlgebraProjection.vectorValue x q)) := tendsto_const_nhds
    have hh := hc.sub hv
    rw [sub_self] at hh
    have hsquare := hh.congr (fun s => (hs s).symm)
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    have hnorm : Tendsto (fun s : Finset ℕ =>
        ‖((a s).val : H →L[ℂ] H) x - (q.val : H →L[ℂ] H) x‖) atTop (𝓝 0) := by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
        Real.sqrt_zero, norm_sub_rev, Function.comp_def] using hn
    have ht := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
    have ha_apply (s : Finset ℕ) :
        ((a s).val : H →L[ℂ] H) x = ∑ i ∈ s, ((p i).val : H →L[ℂ] H) x := by
      change (M.toStarSubalgebra.subtype (∑ i ∈ s, (p i).val)) x = _
      rw [map_sum]
      simp only [sum_apply]
      rfl
    simpa only [HasSum, SummationFilter.unconditional, ha_apply] using ht

private theorem copySlot_cross (u v : Algebra M) (hu : star u * u = 1)
    (hv : star v * v = 1) (huv : star u * v = 0) (p : AlgebraProjection M)
    {i j : ℕ} (hij : i < j) :
    star (copySlot u v hu hv p i).val * (copySlot u v hu hv p j).val = 0 := by
  have hvu : star v * u = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star huv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  change star (u ^ i * v * p.val) * (u ^ (i + (l + 1)) * v * p.val) = 0
  rw [star_mul, star_mul, p.property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = p.val * star v * (star (u ^ i) * u ^ i) * u ^ (l + 1) * v * p.val := by
      simp only [mul_assoc]
    _ = 0 := by
      rw [isometry_power u hu, mul_one, pow_succ']
      calc
        _ = p.val * (star v * u) * u ^ l * v * p.val := by simp only [mul_assoc]
        _ = 0 := by rw [hvu, mul_zero, zero_mul, zero_mul, zero_mul]

private theorem copySlot_orthogonal (u v : Algebra M) (hu : star u * u = 1)
    (hv : star v * v = 1) (huv : star u * v = 0) (p : AlgebraProjection M) :
    Pairwise (fun i j => (copySlot u v hu hv p i).target.val *
      (copySlot u v hu hv p j).target.val = 0) := by
  have hh {i j : ℕ} (hij : i < j) :
      (copySlot u v hu hv p i).target.val * (copySlot u v hu hv p j).target.val = 0 := by
    change ((copySlot u v hu hv p i).val * star (copySlot u v hu hv p i).val) *
      ((copySlot u v hu hv p j).val * star (copySlot u v hu hv p j).val) = 0
    calc
      _ = (copySlot u v hu hv p i).val *
          (star (copySlot u v hu hv p i).val * (copySlot u v hu hv p j).val) *
          star (copySlot u v hu hv p j).val := by simp only [mul_assoc]
      _ = 0 := by rw [copySlot_cross u v hu hv huv p hij, mul_zero, zero_mul]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hh h
  · exact PartialIsometry.orthogonal_reverse _ _ (hh h)

/-- Countably many copies of a full projection fill a properly infinite,
separably acting algebra. All the witnesses lie in the original algebra. -/
theorem exists_countable_projection_copies [TopologicalSpace.SeparableSpace H]
    (hM : ProperlyInfiniteIdentity M) (p : AlgebraProjection M)
    (hp : (centralSupport p).val = 1) : Nonempty (CountableProjectionCopies M p) := by
  obtain ⟨u, v, hu, hv, huv⟩ := hM.isometries
  let slot := copySlot u v hu hv p
  have ho : Pairwise (fun i j => (slot i).target.val * (slot j).target.val = 0) :=
    copySlot_orthogonal u v hu hv huv p
  obtain ⟨q, hq, _, hsum⟩ := exists_orthogonal_projection_sum (fun i => (slot i).target) ho
  obtain ⟨a, ha, hao, hatotal⟩ := exists_countable_source_partition_of_full p hp
  let b (n : ℕ) : PartialIsometry M := (slot n).compose (a n).adjoint (by
    rw [PartialIsometry.adjoint_target]
    exact ha n)
  have hbs (n : ℕ) : (b n).support = (a n).target := rfl
  have hbt (n : ℕ) : (b n).target ≤ (slot n).target :=
    PartialIsometry.compose_target_le _ _ _
  obtain ⟨B, _, hBs, hBt⟩ := PartialIsometry.traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact hao hij)
    (by intro i j hij; exact projection_orthogonal_of_le (ho hij) (hbt i) (hbt j))
  let oneP : AlgebraProjection M := ⟨1, IsStarProjection.one _⟩
  have hB1 : B.support = oneP := Subtype.ext (hatotal _ (fun n => by
    simpa only [hbs] using (hBs B.support).mp le_rfl n)).symm
  have hBq : B.target ≤ q := (hBt _).mpr (fun n => (hbt n).trans (hq n))
  have hq1 : q ≤ oneP := by change 1 * q.val = q.val; exact one_mul _
  obtain ⟨c, hcq, hc1⟩ := AlgebraProjection.equivalent_of_le_of_subequivalent hq1
    (show oneP.Subequivalent q from ⟨B, hB1, hBq⟩)
  let z (n : ℕ) := c.compose (slot n) (by rw [hcq]; exact hq n)
  have hzi (n : ℕ) : star (z n).val * (z n).val = p.val := (z n).initial
  have hzf (n : ℕ) : (z n).target.val = c.val * (slot n).target.val * star c.val :=
    PartialIsometry.compose_target c (slot n) _
  refine ⟨{ projection := fun n => (z n).target
            witness := fun n => (z n).val
            initial := hzi
            final := fun _ => rfl
            orthogonal := ?_
            total := ?_ }⟩
  · intro i j hij
    rw [hzf, hzf]
    calc
      _ = c.val * (slot i).target.val * (star c.val * c.val) *
          (slot j).target.val * star c.val := by simp only [mul_assoc]
      _ = 0 := by
        rw [c.initial, hcq]
        calc
          _ = c.val * ((slot i).target.val * q.val) * (slot j).target.val *
              star c.val := by simp only [mul_assoc]
          _ = c.val * ((slot i).target.val * (slot j).target.val) * star c.val := by
            rw [projection_mul_of_le (hq i)]
            simp only [mul_assoc]
          _ = 0 := by rw [ho hij, mul_zero, zero_mul]
  · intro x
    have hs := (c.val : H →L[ℂ] H).hasSum (hsum ((star c.val : H →L[ℂ] H) x))
    have hcx : (c.val : H →L[ℂ] H) ((q.val : H →L[ℂ] H)
        ((star c.val : H →L[ℂ] H) x)) = x := by
      have hmul : c.val * q.val = c.val := by rw [← hcq]; exact c.mul_support
      have hfinal : c.val * star c.val = 1 := congrArg Subtype.val hc1
      calc
        _ = (((c.val * q.val) * star c.val : Algebra M) : H →L[ℂ] H) x := rfl
        _ = x := by rw [hmul, hfinal]; rfl
    rw [hcx] at hs
    apply hs.congr_fun
    intro n
    rw [hzf]
    rfl

/-- Blackadar's countable full-projection copying assertion, proved from
partial-isometry sums and projection Schroeder--Bernstein. -/
theorem publishedProperInfiniteProjectionCopies_oai :
    PublishedProperInfiniteProjectionCopies.{u} := by
  intro H _ _ _ _ M hM p hp
  exact exists_countable_projection_copies hM p hp

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.publishedProperInfiniteProjectionCopies_oai.{u} := @OAI.KadisonKastler.publishedProperInfiniteProjectionCopies_oai.{u}
