-- Prove2me | solution 1 for OAI.KadisonKastler.projectionSemifinite_of_finite_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:25:25.500483+00:00
-- url     : https://prove2.me/submissions/41b3dc2d-8426-4e38-9acb-6ad53eea48a6

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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
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
import Definitions.Def_Q260K059
import Definitions.Def_Q260K061

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedProperInfiniteProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable copies of a full projection

Blackadar, *Operator Algebras*, III.1.3.6 (author PDF, printed p.243),
asserts that a full projection in a properly infinite, locally countably
 decomposable von Neumann algebra admits a countable orthogonal family of
 equivalent projections with strong sum one. Separably acting algebras are
 countably decomposable. The input below is only this projection assertion.

The projection's central support is the already constructed orbit-closure
projection. Proper infiniteness is expressed by two isometries with
orthogonal ranges. No trace, corner type, or perturbation conclusion is part
of this published input.

Primary source: https://bruceblackadar.com/Mathematics/Cycr.pdf
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Finiteness is preserved by Murray--von Neumann equivalence. -/
theorem finiteProjectionIn_of_equivalent (p q : AlgebraProjection M)
    (hfinite : FiniteProjectionIn M p.val) (v : Algebra M)
    (hvi : star v * v = p.val) (hvf : v * star v = q.val) :
    FiniteProjectionIn M q.val := by
  let V : PartialIsometry M := ⟨p, v, hvi⟩
  have hvp : v * p.val = v := V.mul_support
  have hqv : q.val * v = v := by
    have ht := V.target_mul
    change (v * star v) * v = v at ht
    rwa [hvf] at ht
  have hps : p.val * star v = star v := by
    simpa only [star_mul, star_star, p.property.isSelfAdjoint.star_eq] using
      congrArg star hvp
  have hsq : star v * q.val = star v := by
    simpa only [star_mul, star_star, q.property.isSelfAdjoint.star_eq] using
      congrArg star hqv
  intro w hwi hqw
  have hws : star w * q.val = star w := by
    simpa only [star_mul, q.property.isSelfAdjoint.star_eq] using congrArg star hqw
  let a : Algebra M := star v * w * v
  have hai : star a * a = p.val := by
    change star (star v * w * v) * (star v * w * v) = p.val
    rw [star_mul, star_mul, star_star]
    calc
      _ = star v * star w * (v * star v) * w * v := by noncomm_ring
      _ = star v * (star w * q.val) * w * v := by rw [hvf]; noncomm_ring
      _ = star v * (star w * w) * v := by rw [hws]; noncomm_ring
      _ = p.val := by rw [hwi, hsq, hvi]
  have hpa : p.val * a = a := by
    change p.val * (star v * w * v) = star v * w * v
    rw [← mul_assoc, ← mul_assoc, hps]
  have haa := hfinite a hai hpa
  have hrec : v * (a * star a) * star v = w * star w := by
    change v * ((star v * w * v) * star (star v * w * v)) * star v = w * star w
    rw [star_mul, star_mul, star_star]
    calc
      _ = (v * star v) * w * (v * star v) * star w * (v * star v) := by noncomm_ring
      _ = q.val * w * q.val * star w * q.val := by rw [hvf]
      _ = w * (q.val * star w) * q.val := by rw [hqw]; noncomm_ring
      _ = w * star w := by
        have hwq : w * q.val = w := (show PartialIsometry M from ⟨q, w, hwi⟩).mul_support
        rw [← mul_assoc, hwq, mul_assoc, hws]
  calc
    w * star w = v * (a * star a) * star v := hrec.symm
    _ = q.val := by rw [haa, hvp, hvf]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionSemifiniteness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection semifiniteness from one finite projection in a factor

This is the projection-theoretic step needed after constructing a finite
frequency window in the modular core.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem finiteProjectionIn_of_le {p q : AlgebraProjection M}
    (hp : FiniteProjectionIn M p.val) (hqp : q ≤ p) : FiniteProjectionIn M q.val := by
  intro v hvi hqv
  let V : PartialIsometry M := ⟨q, v, hvi⟩
  let r := AlgebraProjection.remainder q p hqp
  have hvq : v * q.val = v := V.mul_support
  have hqp' : q.val * p.val = q.val := by
    have h := congrArg star hqp
    simpa only [star_mul, p.property.isSelfAdjoint.star_eq,
      q.property.isSelfAdjoint.star_eq] using h
  have hpv : p.val * v = v := by
    calc
      p.val * v = p.val * (q.val * v) := by rw [hqv]
      _ = v := by rw [← mul_assoc, hqp, hqv]
  have hvp : v * p.val = v := by
    calc
      v * p.val = (v * q.val) * p.val := by rw [hvq]
      _ = v := by rw [mul_assoc, hqp', hvq]
  have hrv : r.val * v = 0 := by
    change (p.val - q.val) * v = 0
    rw [sub_mul, hpv, hqv, sub_self]
  have hvr : v * r.val = 0 := by
    change v * (p.val - q.val) = 0
    rw [mul_sub, hvp, hvq, sub_self]
  have hsvr : star v * r.val = 0 := by
    simpa only [star_mul, r.property.isSelfAdjoint.star_eq, star_zero]
      using congrArg star hrv
  have hrsv : r.val * star v = 0 := by
    simpa only [star_mul, r.property.isSelfAdjoint.star_eq, star_zero]
      using congrArg star hvr
  have hsum : q.val + r.val = p.val := by
    change q.val + (p.val - q.val) = p.val
    abel
  have hw : star (v + r.val) * (v + r.val) = p.val := by
    rw [star_add, r.property.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hvi, hsvr, hrv, r.property.isIdempotentElem.eq, add_zero, zero_add, hsum]
  have hleft : p.val * (v + r.val) = v + r.val := by
    rw [mul_add, hpv, show p.val * r.val = r.val from AlgebraProjection.remainder_le q p hqp]
  have hfinal := hp (v + r.val) hw hleft
  have hs : v * star v + r.val = p.val := by
    simpa only [star_add, r.property.isSelfAdjoint.star_eq, add_mul, mul_add,
      hvr, hrsv, r.property.isIdempotentElem.eq, add_zero, zero_add] using hfinal
  calc
    v * star v = (v * star v + r.val) - r.val := by abel
    _ = p.val - r.val := by rw [hs]
    _ = q.val := by change p.val - (p.val - q.val) = q.val; abel

theorem projectionSemifinite_of_finite_projection_oai (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp0 : p.val ≠ 0) (hp : FiniteProjectionIn M p.val) :
    ∀ q : AlgebraProjection M, q.val ≠ 0 →
      ∃ r : AlgebraProjection M, r ≤ q ∧ r.val ≠ 0 ∧ FiniteProjectionIn M r.val := by
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM c.val c.property
      (fun a ha => congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  intro q hq
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections hf p q hp0 hq
  have hfinite := finiteProjectionIn_of_le hp hvs
  refine ⟨v.target, hvt, ?_, finiteProjectionIn_of_equivalent
    v.support v.target hfinite v.val v.initial rfl⟩
  intro hz
  have hvnorm : ‖v.val‖ = 0 := by
    have hh := congrArg norm hz
    simp only [norm_zero] at hh
    change ‖v.val * star v.val‖ = 0 at hh
    rw [CStarRing.norm_self_mul_star] at hh
    nlinarith [norm_nonneg v.val]
  have hvzero := norm_eq_zero.mp hvnorm
  apply hv0
  calc
    v.support.val = star v.val * v.val := v.initial.symm
    _ = 0 := by rw [hvzero, star_zero, zero_mul]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.projectionSemifinite_of_finite_projection_oai.{u_1} := @OAI.KadisonKastler.projectionSemifinite_of_finite_projection_oai.{u_1}
