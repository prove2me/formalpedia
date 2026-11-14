-- Prove2me | solution 1 for OAI.KadisonKastler.normalizer_distance_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:56:59.741231+00:00
-- url     : https://prove2.me/submissions/ed970452-95cc-4ffb-8493-b2ffa72c4a6e

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
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
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
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
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.LinearAlgebra.Dual.Lemmas
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K030
import Theorems.Thm_OAI_KadisonKastler_norm_expUnitary_conjugation_remainder_le

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem unitaryConj_sub (v : unitary (H →L[ℂ] H)) (x y : H →L[ℂ] H) :
    unitaryConj v (x - y) = unitaryConj v x - unitaryConj v y := by
  simp [unitaryConj, mul_sub, sub_mul]

theorem isometry_unitaryConj (v : unitary (H →L[ℂ] H)) : Isometry (unitaryConj v) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm, ← unitaryConj_sub, norm_unitaryConj]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Normalizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Published small-normalizer factorization and its consequence

The factorization hypothesis is Proposition 3.2 of
Cameron–Christensen–Sinclair–Smith–White–Wiggins, *Kadison–Kastler stable
factors*, Duke Math. J. 163 (2014), 2639–2686.  That proposition factors
two sufficiently close normalizers through the algebra and its commutant.

Its specialization at the identity gives the small exact normalizer lemma
used in §7 of *Universal strong Kadison–Kastler stability* (2026), with
radius one and displacement constant four, under the stated factorization
hypothesis.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Unitaries belonging to the algebra normalize it. -/
theorem conjugates_self_of_mem {P : VonNeumannAlgebra H}
    {a : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P) :
    Conjugates a P P := by
  change unitaryConj a '' (P : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem ha hx) (star_mem ha)
  · intro hy
    refine ⟨unitaryConj (star a) y, ?_, ?_⟩
    · exact mul_mem (mul_mem (star_mem ha) hy)
        (by simpa only [Unitary.coe_star, star_star] using ha)
    · simpa only [star_star] using unitaryConj_star_unitaryConj (star a) y

/-- Unitaries in the commutant act trivially on the algebra by conjugation. -/
theorem unitaryConj_eq_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant)
    {x : H →L[ℂ] H} (hx : x ∈ P) : unitaryConj b x = x := by
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb x hx
  rw [unitaryConj, ← hcomm, mul_assoc,
    Unitary.mul_star_self_of_mem b.property, mul_one]

theorem conjugates_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant) :
    Conjugates b P P := by
  change unitaryConj b '' (P : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [unitaryConj_eq_self_of_mem_commutant hb hy] using hy
  · intro hx
    exact ⟨x, hx, unitaryConj_eq_self_of_mem_commutant hb hx⟩

/-- A product of an algebra unitary and a commutant unitary normalizes the algebra. -/
theorem conjugates_self_of_separate_factors {P : VonNeumannAlgebra H}
    {a b : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P)
    (hb : (b : H →L[ℂ] H) ∈ P.commutant) : Conjugates (a * b) P P :=
  (conjugates_self_of_mem_commutant hb).trans (conjugates_self_of_mem ha)

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Self-adjoint approximation by the algebra and its commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selfAdjointAlgebraCommutantSum_zero (M : VonNeumannAlgebra H) :
    0 ∈ selfAdjointAlgebraCommutantSum M :=
  ⟨0, 0, M.zero_mem, M.commutant.zero_mem, IsSelfAdjoint.zero _, IsSelfAdjoint.zero _,
    (zero_add 0).symm⟩

theorem selfAdjoint_of_mem_algebraCommutantSum (M : VonNeumannAlgebra H)
    {s : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M) : IsSelfAdjoint s := by
  obtain ⟨a, b, _, _, ha, hb, rfl⟩ := hs
  exact ha.add hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryExponentialBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A quantitative exponential bound for the normalizer path argument -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exponentialPath_deriv (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    HasDerivAt (fun s => (exponentialPath h s : H →L[ℂ] H))
      ((exponentialPath h t : H →L[ℂ] H) * (Complex.I • (h : H →L[ℂ] H))) t := by
  have he (s : ℝ) : (exponentialPath h s : H →L[ℂ] H) =
      NormedSpace.exp (s • (Complex.I • (h : H →L[ℂ] H))) := by
    change NormedSpace.exp (Complex.I • (s • (h : H →L[ℂ] H))) = _
    rw [smul_comm Complex.I s]
  simp_rw [he]
  exact hasDerivAt_exp_smul_const (Complex.I • (h : H →L[ℂ] H)) t

private theorem exponentialPath_deriv_left (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    HasDerivAt (fun s => (exponentialPath h s : H →L[ℂ] H))
      ((Complex.I • (h : H →L[ℂ] H)) * (exponentialPath h t : H →L[ℂ] H)) t := by
  have he (s : ℝ) : (exponentialPath h s : H →L[ℂ] H) =
      NormedSpace.exp (s • (Complex.I • (h : H →L[ℂ] H))) := by
    change NormedSpace.exp (Complex.I • (s • (h : H →L[ℂ] H))) = _
    rw [smul_comm Complex.I s]
  simp_rw [he]
  exact hasDerivAt_exp_smul_const' (Complex.I • (h : H →L[ℂ] H)) t

theorem norm_expUnitary_sub_expUnitary_le (h k : selfAdjoint (H →L[ℂ] H)) :
    ‖(selfAdjoint.expUnitary h : H →L[ℂ] H) - selfAdjoint.expUnitary k‖ ≤
      ‖(h : H →L[ℂ] H) - k‖ := by
  let f (t : ℝ) := (exponentialPath h t : H →L[ℂ] H) * exponentialPath k (1 - t)
  let f' (t : ℝ) := (exponentialPath h t : H →L[ℂ] H) *
    (Complex.I • ((h : H →L[ℂ] H) - k)) * exponentialPath k (1 - t)
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    have hk := (exponentialPath_deriv_left k (1 - t)).scomp t
      ((hasDerivAt_id t).const_sub (1 : ℝ))
    have hd := (exponentialPath_deriv h t).mul hk
    refine hd.congr_deriv ?_
    simp only [f', Function.comp_apply, one_smul, neg_smul, smul_sub]
    noncomm_ring
  have hn (t : ℝ) : ‖f' t‖ ≤ ‖(h : H →L[ℂ] H) - k‖ := by
    dsimp [f']
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      norm_smul, Complex.norm_I, one_mul]
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => hn t)
  have hzero (a : selfAdjoint (H →L[ℂ] H)) :
      (exponentialPath a 0 : H →L[ℂ] H) = 1 := by
    change NormedSpace.exp (Complex.I • ((0 : ℝ) • (a : H →L[ℂ] H))) = 1
    rw [zero_smul, smul_zero, NormedSpace.exp_zero]
  have hone (a : selfAdjoint (H →L[ℂ] H)) :
      exponentialPath a 1 = selfAdjoint.expUnitary a := by
    apply Subtype.ext
    change NormedSpace.exp (Complex.I • ((1 : ℝ) • (a : H →L[ℂ] H))) = _
    rw [one_smul]
    rfl
  simpa only [f, sub_self, sub_zero, hzero, hone, one_mul, mul_one] using hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfinitesimalExponentiation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exponentiating the infinitesimal normalizer estimate -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem one_mem_separateUnitaryProducts (M : VonNeumannAlgebra H) :
    1 ∈ separateUnitaryProducts M := by
  exact ⟨1, 1, M.one_mem, M.commutant.one_mem, by simp⟩

theorem separateUnitaryProducts_mul (M : VonNeumannAlgebra H)
    {s t : H →L[ℂ] H} (hs : s ∈ separateUnitaryProducts M)
    (ht : t ∈ separateUnitaryProducts M) : s * t ∈ separateUnitaryProducts M := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hs
  obtain ⟨c, d, hc, hd, rfl⟩ := ht
  refine ⟨a * c, b * d, M.mul_mem ha hc, M.commutant.mul_mem hb hd, ?_⟩
  change ((a : H →L[ℂ] H) * b) * ((c : H →L[ℂ] H) * d) =
    ((a : H →L[ℂ] H) * c) * ((b : H →L[ℂ] H) * d)
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb c hc
  calc
    _ = (a : H →L[ℂ] H) * ((b : H →L[ℂ] H) * c) * d := by noncomm_ring
    _ = (a : H →L[ℂ] H) * ((c : H →L[ℂ] H) * b) * d := by rw [← hcomm]
    _ = _ := by noncomm_ring

theorem separateUnitaryProducts_star (M : VonNeumannAlgebra H)
    {s : H →L[ℂ] H} (hs : s ∈ separateUnitaryProducts M) :
    star s ∈ separateUnitaryProducts M := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hs
  refine ⟨star a, star b, star_mem ha, star_mem hb, ?_⟩
  change star ((a : H →L[ℂ] H) * b) = star (a : H →L[ℂ] H) * star (b : H →L[ℂ] H)
  rw [star_mul]
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb a ha
  simpa only [star_mul] using congrArg star hcomm

theorem conjugates_of_mem_separateUnitaryProducts (M : VonNeumannAlgebra H)
    {u : unitary (H →L[ℂ] H)} (hu : (u : H →L[ℂ] H) ∈ separateUnitaryProducts M) :
    Conjugates u M M := by
  obtain ⟨a, b, ha, hb, he⟩ := hu
  have hue : u = a * b := Subtype.ext he
  rw [hue]
  exact conjugates_self_of_separate_factors ha hb

theorem infDist_separateUnitaryProducts_left (M : VonNeumannAlgebra H)
    (p : unitary (H →L[ℂ] H)) (hp : (p : H →L[ℂ] H) ∈ separateUnitaryProducts M)
    (T : H →L[ℂ] H) :
    Metric.infDist (star (p : H →L[ℂ] H) * T) (separateUnitaryProducts M) =
      Metric.infDist T (separateUnitaryProducts M) := by
  let f (x : H →L[ℂ] H) := star (p : H →L[ℂ] H) * x
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [dist_eq_norm]
    change ‖star (p : H →L[ℂ] H) * x - star (p : H →L[ℂ] H) * y‖ = ‖x - y‖
    rw [← mul_sub, ← Unitary.coe_star, CStarRing.norm_coe_unitary_mul]
  have himage : f '' separateUnitaryProducts M = separateUnitaryProducts M := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact separateUnitaryProducts_mul M (separateUnitaryProducts_star M hp) hx
    · intro hy
      refine ⟨(p : H →L[ℂ] H) * y, separateUnitaryProducts_mul M hp hy, ?_⟩
      dsimp [f]
      rw [← mul_assoc, Unitary.star_mul_self_of_mem p.property, one_mul]
  simpa only [himage] using Metric.infDist_image (x := T) (t := separateUnitaryProducts M) hf

theorem infDist_unitaryConj_normalizer (M : VonNeumannAlgebra H)
    (p : unitary (H →L[ℂ] H)) (hp : Conjugates p M M) (T : H →L[ℂ] H) :
    Metric.infDist (unitaryConj p T) (M : Set (H →L[ℂ] H)) =
      Metric.infDist T (M : Set (H →L[ℂ] H)) := by
  change unitaryConj p '' (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)) at hp
  simpa only [hp] using Metric.infDist_image (x := T) (t := (M : Set (H →L[ℂ] H)))
    (isometry_unitaryConj p)

theorem expUnitary_mem_vonNeumann (M : VonNeumannAlgebra H)
    (a : selfAdjoint (H →L[ℂ] H)) (ha : (a : H →L[ℂ] H) ∈ M) :
    (selfAdjoint.expUnitary a : H →L[ℂ] H) ∈ M := by
  let : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  change NormedSpace.exp (Complex.I • (a : H →L[ℂ] H)) ∈ M.toStarSubalgebra
  exact NormedSpace.exp_mem (R := ℂ) (S := StarSubalgebra ℂ (H →L[ℂ] H))
    (s := M.toStarSubalgebra) (isClosed_algebra M) (M.smul_mem ha _)

theorem expUnitary_mem_separateUnitaryProducts (M : VonNeumannAlgebra H)
    (h : selfAdjoint (H →L[ℂ] H))
    (hh : (h : H →L[ℂ] H) ∈ selfAdjointAlgebraCommutantSum M) :
    (selfAdjoint.expUnitary h : H →L[ℂ] H) ∈ separateUnitaryProducts M := by
  obtain ⟨a, b, ha, hb, hsa, hsb, he⟩ := hh
  let sa : selfAdjoint (H →L[ℂ] H) := ⟨a, hsa⟩
  let sb : selfAdjoint (H →L[ℂ] H) := ⟨b, hsb⟩
  have hsum : h = sa + sb := Subtype.ext he
  have hcomm : Commute (sa : H →L[ℂ] H) (sb : H →L[ℂ] H) :=
    VonNeumannAlgebra.mem_commutant_iff.mp hb a ha
  refine ⟨selfAdjoint.expUnitary sa, selfAdjoint.expUnitary sb,
    expUnitary_mem_vonNeumann M sa ha, expUnitary_mem_vonNeumann M.commutant sb hb, ?_⟩
  rw [hsum, hcomm.expUnitary_add]

theorem infDist_expUnitary_le_infDist_selfAdjointSum (M : VonNeumannAlgebra H)
    (h : selfAdjoint (H →L[ℂ] H)) :
    Metric.infDist (selfAdjoint.expUnitary h : H →L[ℂ] H) (separateUnitaryProducts M) ≤
      Metric.infDist (h : H →L[ℂ] H) (selfAdjointAlgebraCommutantSum M) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  obtain ⟨s, hs, hnear⟩ := (Metric.infDist_lt_iff
    (show (selfAdjointAlgebraCommutantSum M).Nonempty from
      ⟨0, selfAdjointAlgebraCommutantSum_zero M⟩)).mp hr
  let k : selfAdjoint (H →L[ℂ] H) := ⟨s, selfAdjoint_of_mem_algebraCommutantSum M hs⟩
  calc
    _ ≤ dist (selfAdjoint.expUnitary h : H →L[ℂ] H) (selfAdjoint.expUnitary k) :=
      Metric.infDist_le_dist_of_mem (expUnitary_mem_separateUnitaryProducts M k hs)
    _ = ‖(selfAdjoint.expUnitary h : H →L[ℂ] H) - selfAdjoint.expUnitary k‖ := dist_eq_norm _ _
    _ ≤ ‖(h : H →L[ℂ] H) - (k : H →L[ℂ] H)‖ := norm_expUnitary_sub_expUnitary_le h k
    _ ≤ r := by simpa only [dist_eq_norm] using hnear.le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerDefect
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # From a conjugation defect to an infinitesimal defect -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem commutator_exp_error (h : selfAdjoint (H →L[ℂ] H))
    (x y : H →L[ℂ] H) :
    ‖(h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H) - (-Complex.I) • (y - x)‖ ≤
      ‖unitaryConj (H := H) (selfAdjoint.expUnitary h) x - y‖ +
        ‖unitaryConj (H := H) (selfAdjoint.expUnitary h) x - x -
          Complex.I • ((h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H))‖ := by
  let c : H →L[ℂ] H := (h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H)
  let z : H →L[ℂ] H := (-Complex.I) • (y - x)
  have hIz : Complex.I • z = y - x := by
    dsimp [z]
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  have heq : Complex.I • (c - z) =
      (unitaryConj (H := H) (selfAdjoint.expUnitary h) x - y) -
      (unitaryConj (H := H) (selfAdjoint.expUnitary h) x - x - Complex.I • c) := by
    rw [smul_sub, hIz]
    abel
  change ‖c - z‖ ≤ _
  calc
    ‖c - z‖ = ‖Complex.I • (c - z)‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ _ := by rw [heq]; exact norm_sub_le _ _

private theorem infDist_commutator_le_of_exp_approx (M : VonNeumannAlgebra H)
    (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) (hx : x ∈ M) (hxn : ‖x‖ ≤ 1)
    {e : ℝ} (he : Metric.infDist (unitaryConj (H := H) (selfAdjoint.expUnitary h) x)
      (M : Set (H →L[ℂ] H)) ≤ e) :
    Metric.infDist ((h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H))
      (M : Set (H →L[ℂ] H)) ≤ e + 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hd : Metric.infDist (unitaryConj (H := H) (selfAdjoint.expUnitary h) x)
      (M : Set (H →L[ℂ] H)) < r - 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 :=
    he.trans_lt (by linarith)
  obtain ⟨y, hy, hnear⟩ := (Metric.infDist_lt_iff
    (show (M : Set (H →L[ℂ] H)).Nonempty from ⟨0, M.zero_mem⟩)).mp hd
  have hz : (-Complex.I) • (y - x) ∈ M := M.smul_mem (M.sub_mem hy hx) _
  have hdist := Metric.infDist_le_dist_of_mem
    (x := (h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H)) hz
  rw [dist_eq_norm] at hdist hnear
  have herror := commutator_exp_error h x y
  have hrem := norm_expUnitary_conjugation_remainder_le h x
  have hmul : 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ ≤ 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 := by
    calc
      _ ≤ 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hxn (by positivity)
      _ = _ := mul_one _
  linarith

theorem commutatorRangeError_le_of_exp_approx (M : VonNeumannAlgebra H)
    (h : selfAdjoint (H →L[ℂ] H)) {e : ℝ}
    (he : ∀ x ∈ unitBall M,
      Metric.infDist (unitaryConj (H := H) (selfAdjoint.expUnitary h) x)
        (M : Set (H →L[ℂ] H)) ≤ e) :
    commutatorRangeError M (h : H →L[ℂ] H) ≤ e + 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 := by
  apply csSup_le
    (show ((fun x : Algebra M => Metric.infDist
      (commutatorAlong M.toStarSubalgebra.subtype (h : H →L[ℂ] H) x)
      (M : Set (H →L[ℂ] H))) '' {x | ‖x‖ ≤ 1}).Nonempty from ⟨_, 0, by simp, rfl⟩)
  rintro _ ⟨x, hx, rfl⟩
  change Metric.infDist ((h : H →L[ℂ] H) * x.val - x.val * (h : H →L[ℂ] H)) _ ≤ _
  exact infDist_commutator_le_of_exp_approx M h x.val x.property hx (he x.val ⟨x.property, hx⟩)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryLogarithmBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A controlled self-adjoint logarithm near the identity -/

namespace KadisonKastler

open scoped Real

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_argSelfAdjoint_le_two_mul (u : unitary (H →L[ℂ] H))
    (hu : ‖(u : H →L[ℂ] H) - 1‖ < 2) :
    ‖Unitary.argSelfAdjoint u‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ := by
  let θ := ‖Unitary.argSelfAdjoint u‖
  let d := ‖(u : H →L[ℂ] H) - 1‖
  have hθ : 0 ≤ θ := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hθpi : θ ≤ Real.pi := Unitary.norm_argSelfAdjoint_le_pi u
  have hc := Real.cos_le_one_sub_mul_cos_sq
    (x := θ) (by rwa [abs_of_nonneg hθ])
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hc' : Real.pi ^ 2 * Real.cos θ ≤ Real.pi ^ 2 - 2 * θ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hc hpi.le
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have heq : 2 * (1 - Real.cos θ) = d ^ 2 :=
    Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint hu
  have heq' := congrArg (fun r : ℝ => Real.pi ^ 2 * r) heq
  have hb : 4 * θ ^ 2 ≤ Real.pi ^ 2 * d ^ 2 := by nlinarith
  have hpi4 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hb' := mul_le_mul_of_nonneg_right hpi4 (sq_nonneg d)
  change θ ≤ 2 * d
  nlinarith

theorem exists_small_selfAdjoint_log (u : unitary (H →L[ℂ] H))
    (hu : ‖(u : H →L[ℂ] H) - 1‖ < 2) :
    ∃ h : selfAdjoint (H →L[ℂ] H), selfAdjoint.expUnitary h = u ∧
      ‖h‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ :=
  ⟨Unitary.argSelfAdjoint u, expUnitary_argSelfAdjoint hu,
    norm_argSelfAdjoint_le_two_mul u hu⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerPathLocal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The local quadratic estimate for approximate normalizers -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exists_small_log_of_separate_translate
    (M : VonNeumannAlgebra H) (v : unitary (H →L[ℂ] H)) {r : ℝ}
    (hr : Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) < r)
    (hr2 : r < 2) :
    ∃ p : unitary (H →L[ℂ] H), (p : H →L[ℂ] H) ∈ separateUnitaryProducts M ∧
      ∃ h : selfAdjoint (H →L[ℂ] H), selfAdjoint.expUnitary h = star p * v ∧
        ‖(h : H →L[ℂ] H)‖ ≤ 2 * r := by
  obtain ⟨p0, hp0, hnear⟩ := (Metric.infDist_lt_iff
    (show (separateUnitaryProducts M).Nonempty from
      ⟨1, one_mem_separateUnitaryProducts M⟩)).mp hr
  obtain ⟨a, b, ha, hb, rfl⟩ := hp0
  let p : unitary (H →L[ℂ] H) := a * b
  have hp : (p : H →L[ℂ] H) ∈ separateUnitaryProducts M := ⟨a, b, ha, hb, rfl⟩
  let w : unitary (H →L[ℂ] H) := star p * v
  have hwn : ‖(w : H →L[ℂ] H) - 1‖ < r := by
    have heq : (w : H →L[ℂ] H) - 1 = star (p : H →L[ℂ] H) *
        ((v : H →L[ℂ] H) - p) := by
      change star (p : H →L[ℂ] H) * v - 1 = _
      rw [mul_sub, Unitary.star_mul_self_of_mem p.property]
    rw [heq, ← Unitary.coe_star, CStarRing.norm_coe_unitary_mul]
    simpa only [dist_eq_norm, p] using hnear
  obtain ⟨h, hlog, hnorm⟩ := exists_small_selfAdjoint_log w (hwn.trans hr2)
  exact ⟨p, hp, h, hlog, hnorm.trans (by linarith)⟩

private theorem conjugation_approximation_separate_translate
    (M : VonNeumannAlgebra H) (v p : unitary (H →L[ℂ] H))
    (hp : (p : H →L[ℂ] H) ∈ separateUnitaryProducts M) {e : ℝ}
    (he : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) v x)
      (M : Set (H →L[ℂ] H)) ≤ e) :
    ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) (star p * v) x)
      (M : Set (H →L[ℂ] H)) ≤ e := by
  intro x hx
  rw [unitaryConj_mul, infDist_unitaryConj_normalizer M (star p)
    (conjugates_of_mem_separateUnitaryProducts M hp).symm]
  exact he x hx

private theorem normalizer_distance_bound_with_slack
    (M : VonNeumannAlgebra H) {K : ℝ} (hK : 0 ≤ K)
    (hlinear : ∀ h : selfAdjoint (H →L[ℂ] H),
      Metric.infDist (h : H →L[ℂ] H) (selfAdjointAlgebraCommutantSum M) ≤
        K * commutatorRangeError M (h : H →L[ℂ] H))
    (v : unitary (H →L[ℂ] H)) {e r : ℝ}
    (he : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) v x)
      (M : Set (H →L[ℂ] H)) ≤ e)
    (hr : Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) < r)
    (hr2 : r < 2) :
    Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) ≤
      K * (e + 16 * r ^ 2) := by
  obtain ⟨p, hp, h, hlog, hn⟩ := exists_small_log_of_separate_translate M v hr hr2
  have heh : ∀ x ∈ unitBall M,
      Metric.infDist (unitaryConj (H := H) (selfAdjoint.expUnitary h) x)
        (M : Set (H →L[ℂ] H)) ≤ e := by
    rw [hlog]
    exact conjugation_approximation_separate_translate M v p hp he
  have hdef := commutatorRangeError_le_of_exp_approx M h heh
  have hdist := infDist_expUnitary_le_infDist_selfAdjointSum M h
  rw [hlog] at hdist
  have heqdist := infDist_separateUnitaryProducts_left M p hp (v : H →L[ℂ] H)
  change Metric.infDist (star (p : H →L[ℂ] H) * (v : H →L[ℂ] H))
    (separateUnitaryProducts M) ≤ _ at hdist
  rw [heqdist] at hdist
  calc
    _ ≤ K * commutatorRangeError M (h : H →L[ℂ] H) := hdist.trans (hlinear h)
    _ ≤ K * (e + 4 * ‖(h : H →L[ℂ] H)‖ ^ 2) := mul_le_mul_of_nonneg_left hdef hK
    _ ≤ K * (e + 16 * r ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      have hs := mul_self_le_mul_self (norm_nonneg (h : H →L[ℂ] H)) hn
      nlinarith

theorem normalizer_distance_quadratic_oai
    (M : VonNeumannAlgebra H) {K : ℝ} (hK : 0 ≤ K)
    (hlinear : ∀ h : selfAdjoint (H →L[ℂ] H),
      Metric.infDist (h : H →L[ℂ] H) (selfAdjointAlgebraCommutantSum M) ≤
        K * commutatorRangeError M (h : H →L[ℂ] H))
    (v : unitary (H →L[ℂ] H)) {e : ℝ}
    (he : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) v x)
      (M : Set (H →L[ℂ] H)) ≤ e)
    (hsmall : Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) < 1) :
    Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) ≤
      K * e + 16 * K * (Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M)) ^ 2 := by
  let d := Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M)
  let r (n : ℕ) := d + (1 - d) * (1 / (n + 1 : ℝ))
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have hdr : d < 1 := hsmall
  have hr (n : ℕ) : d < r n := by
    dsimp [r]
    exact lt_add_of_pos_right d (mul_pos (sub_pos.mpr hdr) (by positivity))
  have hr2 (n : ℕ) : r n < 2 := by
    have hn : 1 / (n + 1 : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      norm_num
    dsimp [r]
    have hmul := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hdr.le)
    linarith
  have hbound (n : ℕ) : d ≤ K * (e + 16 * r n ^ 2) :=
    normalizer_distance_bound_with_slack M hK hlinear v he (hr n) (hr2 n)
  have hrt : Tendsto r atTop (𝓝 d) := by
    have ht : Tendsto (fun n : ℕ => d + (1 - d) * (1 / (n + 1 : ℝ))) atTop
        (𝓝 (d + (1 - d) * 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa only [mul_zero, add_zero] using ht
  have ht : Tendsto (fun n : ℕ => K * (e + 16 * r n ^ 2)) atTop
      (𝓝 (K * (e + 16 * d ^ 2))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add
      (tendsto_const_nhds.mul (hrt.pow 2)))
  have hb := le_of_tendsto_of_tendsto' tendsto_const_nhds ht hbound
  convert hb using 1 <;> first | rfl | ring

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.normalizer_distance_quadratic_oai.{u_1} := @OAI.KadisonKastler.normalizer_distance_quadratic_oai.{u_1}
