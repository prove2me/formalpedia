-- Prove2me | solution 1 for OAI.KadisonKastler.exists_bounded_conjugacy_from_centralPair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:08:13.510519+00:00
-- url     : https://prove2.me/submissions/bd508360-780b-4686-805f-d423d7a462de

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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K020
import Definitions.Def_Q260K023

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem unitaryConj_unitBall {M N : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) :
    unitaryConj v '' unitBall M = unitBall N := by
  change unitaryConj v '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H)) at hv
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, by simpa using hx.2⟩
    change unitaryConj v x ∈ (N : Set (H →L[ℂ] H))
    rw [← hv]
    exact Set.mem_image_of_mem _ hx.1
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (show y ∈ unitaryConj v '' (M : Set (H →L[ℂ] H)) from
      hv.symm ▸ hy.1)
    exact ⟨x, ⟨hx, by simpa using hy.2⟩, rfl⟩

end

end KadisonKastler

end OAI
end

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
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transport and the canonical infinite amplification

Transport into the initial coordinate preserves the unit balls and their
Hausdorff distance. The abstract diagonal action obtained from the matrix
units is exactly the coordinatewise action on the Hilbert direct sum.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_spatialConjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map e.conjStarAlgEquiv e.conjStarAlgEquiv.injective T

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitBallClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem unitBallClip_mem (S : Submodule ℂ B) {x : B} (hx : x ∈ S) :
    unitBallClip x ∈ S := S.smul_mem _ hx

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableConjugacyTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable tests for the implementer relation

Strongly dense contraction families determine both inclusions of a
unitary conjugacy. This is the algebraic equivalence used when forming
the measurable implementer relation in the central decomposition.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitBall_subset_algebra_iff (M N : VonNeumannAlgebra H) :
    unitBall M ⊆ N ↔ M ≤ N := by
  constructor
  · intro h x hx
    have hclip : unitBallClip x ∈ N :=
      h ⟨unitBallClip_mem M.toStarSubalgebra.toSubalgebra.toSubmodule hx,
        unitBallClip_norm_le x⟩
    have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have heq : ((max 1 ‖x‖ : ℝ) : ℂ) • unitBallClip x = x := by
      rw [unitBallClip, smul_smul]
      have hn : ((max 1 ‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      simp only [Complex.ofReal_inv, mul_inv_cancel₀ hn, one_smul]
    rw [← heq]
    exact N.toStarSubalgebra.smul_mem hclip _
  · exact fun h _ hx => h hx.1

theorem unitaryConj_mem_of_strong_tests (N : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (T : ℕ → H →L[ℂ] H) (x : H →L[ℂ] H)
    (hlim : ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (x ξ)))
    (hT : ∀ n, unitaryConj v (T n) ∈ N) : unitaryConj v x ∈ N := by
  let b (n : ℕ) : Algebra N := ⟨unitaryConj v (T n), hT n⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) N b (unitaryConj v x)
  intro ξ η
  have h := ((v : H →L[ℂ] H).continuous.tendsto _).comp
    (hlim (star (v : H →L[ℂ] H) ξ))
  have h' : Tendsto
      (fun n => inner ℂ η ((v : H →L[ℂ] H) (T n (star (v : H →L[ℂ] H) ξ)))) atTop
      (𝓝 (inner ℂ η ((v : H →L[ℂ] H) (x (star (v : H →L[ℂ] H) ξ))))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)).inner (𝕜 := ℂ) h
  simpa only [b, unitaryConj, mul_apply_eq_comp] using h'

theorem unitaryConj_inclusion_of_dense_tests
    (M N : VonNeumannAlgebra H) (v : unitary (H →L[ℂ] H))
    (E : Set (H →L[ℂ] H))
    (hdense : ∀ x ∈ unitBall M, ∃ T : ℕ → H →L[ℂ] H,
      (∀ n, T n ∈ E) ∧ ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (x ξ)))
    (hE : ∀ x ∈ E, unitaryConj v x ∈ N) :
    unitaryConjugateAlgebra v M ≤ N := by
  apply (unitBall_subset_algebra_iff _ _).mp
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (unitaryConj_unitBall
    (conjugates_unitaryConjugateAlgebra v M)).symm ▸ hy
  obtain ⟨T, hTE, hlim⟩ := hdense x hx
  exact unitaryConj_mem_of_strong_tests N v T x hlim (fun n => hE (T n) (hTE n))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableStrongMembership
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable finite-vector tests for algebra membership

For contractions, approximation on finite prefixes of a dense vector
sequence is equivalent to membership in the strongly closed target
algebra, provided the test family is strongly dense in its unit ball.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_le_iff_dense_vector_tests (ξ : ℕ → H) (hξ : DenseRange ξ)
    (T : H →L[ℂ] H) {a : ℝ} (ha : 0 ≤ a) :
    ‖T‖ ≤ a ↔ ∀ n, ‖T (ξ n)‖ ≤ a * ‖ξ n‖ := by
  constructor
  · exact fun h n => (T.le_opNorm (ξ n)).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  · intro h
    apply T.opNorm_le_bound ha
    intro x
    exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n)
      (isClosed_le (T.continuous.norm) (continuous_const.mul continuous_norm)) (hξ x)

omit [CompleteSpace H] in
theorem countableStrongTests_of_strong_sequence
    (ξ : ℕ → H) (F : Set (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (S : ℕ → H →L[ℂ] H) (hSF : ∀ n, S n ∈ F)
    (hlim : ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (T x))) :
    CountableStrongTests ξ F T := by
  intro m k
  have hsmall : ∀ᶠ n in atTop, ∀ l ∈ Finset.range (m + 1),
      ‖(T - S n) (ξ l)‖ < 1 / (k + 1 : ℝ) := by
    apply (eventually_all_finset _).mpr
    intro l _
    have h := (Metric.tendsto_nhds.mp (hlim (ξ l))) (1 / (k + 1 : ℝ)) (by positivity)
    simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using h
  obtain ⟨n, hn⟩ := hsmall.exists
  exact ⟨S n, hSF n, fun l hl => hn l (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))⟩

/-- The countably quantified test predicate exactly recognizes the
contractive elements of the target algebra. -/
theorem mem_iff_countableStrongTests (N : VonNeumannAlgebra H)
    (ξ : ℕ → H) (hξ : DenseRange ξ) (F : Set (H →L[ℂ] H))
    (hFN : F ⊆ unitBall N)
    (hFdense : ∀ T ∈ unitBall N, ∃ S : ℕ → H →L[ℂ] H,
      (∀ n, S n ∈ F) ∧ ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (T x)))
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    T ∈ N ↔ CountableStrongTests ξ F T := by
  constructor
  · intro hTN
    obtain ⟨S, hSF, hlim⟩ := hFdense T ⟨hTN, hT⟩
    exact countableStrongTests_of_strong_sequence ξ F T S hSF hlim
  · intro htest
    obtain ⟨S, hSF, hlim⟩ := exists_strong_sequence_of_countable_tests ξ hξ F
      (fun S hS => (hFN hS).2) T hT htest
    simpa only [unitaryConj_one] using unitaryConj_mem_of_strong_tests N 1 S T hlim
      (fun n => by simpa only [unitaryConj_one] using (hFN (hSF n)).1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableStrongTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability of countable strong approximation conditions

Only vector evaluation is required to be measurable. Countable tests
then give a measurable implementer condition without placing the norm
topology on the operator algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

omit [MeasurableSpace X] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
theorem prefixStrongTests_iff (ξ : ℕ → H) (T : X → H →L[ℂ] H)
    (S : X → ℕ → H →L[ℂ] H) (p : X) :
    PrefixStrongTests ξ T S p ↔ CountableStrongTests ξ (Set.range (S p)) (T p) := by
  constructor
  · intro h m k
    obtain ⟨q, hq⟩ := h m k
    exact ⟨S p q, ⟨q, rfl⟩, hq⟩
  · intro h m k
    obtain ⟨a, ⟨q, rfl⟩, ha⟩ := h m k
    exact ⟨q, ha⟩

omit [CompleteSpace H] in
/-- Every condition is a countable combination of measurable vector-norm
inequalities. The operator maps need not be norm measurable. -/
theorem measurableSet_prefixStrongTests (ξ : ℕ → H) (T : X → H →L[ℂ] H)
    (S : X → ℕ → H →L[ℂ] H)
    (h : ∀ q l, Measurable (fun p => (T p - S p q) (ξ l))) :
    MeasurableSet {p | PrefixStrongTests ξ T S p} := by
  simp only [PrefixStrongTests, Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt (h q l).norm measurable_const

omit [CompleteSpace H] in
theorem measurableSet_countableStrongTests_range
    (ξ : ℕ → H) (T : X → H →L[ℂ] H) (S : X → ℕ → H →L[ℂ] H)
    (h : ∀ q l, Measurable (fun p => (T p - S p q) (ξ l))) :
    MeasurableSet {p | CountableStrongTests ξ (Set.range (S p)) (T p)} := by
  simpa only [← prefixStrongTests_iff] using measurableSet_prefixStrongTests ξ T S h

omit [CompleteSpace H] in
/-- An operator norm bound is a countable measurable condition when
evaluations on a dense vector family are measurable. -/
theorem measurableSet_operator_norm_le (ξ : ℕ → H) (hξ : DenseRange ξ)
    (T : X → H →L[ℂ] H) {a : ℝ} (ha : 0 ≤ a)
    (hT : ∀ n, Measurable (fun p => T p (ξ n))) :
    MeasurableSet {p | ‖T p‖ ≤ a} := by
  have heq : {p | ‖T p‖ ≤ a} = ⋂ n : ℕ, {p | ‖T p (ξ n)‖ ≤ a * ‖ξ n‖} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, norm_le_iff_dense_vector_tests ξ hξ _ ha]
  rw [heq]
  exact MeasurableSet.iInter fun n => measurableSet_le (hT n).norm measurable_const

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SequentialConjugacyTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sequential tests for the measurable conjugacy relation

Each represented algebra on a separable Hilbert space has an actual
sequence of contractions whose range is strongly dense in its unit ball.
Conjugacy is exactly two countable families of finite-vector tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem StrongUnitBallTestSequence.range_subset {M : VonNeumannAlgebra H}
    (A : StrongUnitBallTestSequence M) : Set.range A.op ⊆ unitBall M := by
  rintro _ ⟨n, rfl⟩
  exact A.mem n

theorem conjugates_iff_strong_sequence_mem {M N : VonNeumannAlgebra H}
    (A : StrongUnitBallTestSequence M) (B : StrongUnitBallTestSequence N)
    (v : unitary (H →L[ℂ] H)) :
    Conjugates v M N ↔ (∀ j, unitaryConj v (A.op j) ∈ N) ∧
      (∀ j, unitaryConj (star v) (B.op j) ∈ M) := by
  constructor
  · intro hv
    exact ⟨fun j => hv.subset ⟨A.op j, (A.mem j).1, rfl⟩,
      fun j => hv.symm.subset ⟨B.op j, (B.mem j).1, rfl⟩⟩
  · rintro ⟨hA, hB⟩
    have hMN := unitaryConj_inclusion_of_dense_tests M N v (Set.range A.op) A.dense
      (by rintro _ ⟨j, rfl⟩; exact hA j)
    have hNM := unitaryConj_inclusion_of_dense_tests N M (star v) (Set.range B.op) B.dense
      (by rintro _ ⟨j, rfl⟩; exact hB j)
    apply Set.Subset.antisymm
    · exact hMN
    · intro y hy
      refine ⟨unitaryConj (star v) y, hNM ⟨y, hy, rfl⟩, ?_⟩
      simpa only [star_star] using unitaryConj_star_unitaryConj (star v) y

/-- This is the exact countable relation used for choosing implementers. -/
theorem conjugates_iff_countable_strong_tests {M N : VonNeumannAlgebra H}
    (A : StrongUnitBallTestSequence M) (B : StrongUnitBallTestSequence N)
    (ξ : ℕ → H) (hξ : DenseRange ξ) (v : unitary (H →L[ℂ] H)) :
    Conjugates v M N ↔
      (∀ j, CountableStrongTests ξ (Set.range B.op) (unitaryConj v (A.op j))) ∧
      (∀ j, CountableStrongTests ξ (Set.range A.op) (unitaryConj (star v) (B.op j))) := by
  rw [conjugates_iff_strong_sequence_mem A B v]
  apply and_congr
  · apply forall_congr'
    intro j
    exact mem_iff_countableStrongTests N ξ hξ (Set.range B.op) B.range_subset B.dense
      _ (by simpa only [norm_unitaryConj] using (A.mem j).2)
  · apply forall_congr'
    intro j
    exact mem_iff_countableStrongTests M ξ hξ (Set.range A.op) A.range_subset A.dense
      _ (by simpa only [norm_unitaryConj] using (B.mem j).2)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearSeparableGenerators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nearby separable C-star algebras generating the original pair

In a separable representation, the alternating construction can retain
countable strong generators of both original algebras. This supplies
the norm-separable algebras needed for simultaneous fiber representations.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_norm_dense_unitBall_sequence (E : Type*) [NormedAddCommGroup E]
    [SeparableSpace E] :
    ∃ s : ℕ → E, (∀ j, ‖s j‖ ≤ 1) ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ j, ‖x - s j‖ < ε := by
  let S := {x : E | ‖x‖ ≤ 1}
  have : Nonempty S := ⟨0, by simp [S]⟩
  obtain ⟨s, hs⟩ := exists_dense_seq (α := S)
  refine ⟨fun j => s j, fun j => (s j).property, ?_⟩
  intro x hx ε hε
  obtain ⟨j, hj⟩ := hs.exists_dist_lt ⟨x, hx⟩ hε
  exact ⟨j, by simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hj⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableUnitaryAssembly
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling the dimension strata by a Hilbert direct sum -/

namespace KadisonKastler

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

theorem norm_l2FiberUnitary_sub_one_le (U : ∀ n, unitary (E n →L[ℂ] E n))
    {a : ℝ} (ha : 0 ≤ a) (hU : ∀ n, ‖(U n : E n →L[ℂ] E n) - 1‖ ≤ a) :
    ‖(l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) - 1‖ ≤ a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro f
  calc
    ‖((l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) - 1) f‖ ≤ ‖(a : ℂ) • f‖ := by
      apply lp.norm_mono (by norm_num)
      intro n
      have h := (((U n : E n →L[ℂ] E n) - 1).le_opNorm (f n)).trans
        (mul_le_mul_of_nonneg_right (hU n) (norm_nonneg _))
      simpa only [sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply,
        l2FiberUnitary_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using h
    _ = a * ‖f‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableConjugacyAssembly
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugacy on a countable Hilbert direct sum

The decomposition and reconstruction properties below describe a given
block decomposition. They do not assert that an arbitrary algebra admits
one. Coordinate conjugacies assemble without changing their uniform bound.
-/

namespace KadisonKastler

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

omit [∀ n, CompleteSpace (E n)] in
theorem RepresentsBlockOperators.unique {F : ∀ n, E n →L[ℂ] E n}
    {T S : lp E 2 →L[ℂ] lp E 2}
    (hT : RepresentsBlockOperators F T) (hS : RepresentsBlockOperators F S) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  exact (hT f n).trans (hS f n).symm

theorem l2FiberUnitary_star_apply (U : ∀ n, unitary (E n →L[ℂ] E n))
    (f : lp E 2) (n : ℕ) :
    ((star (l2FiberUnitary U) : lp E 2 →L[ℂ] lp E 2) f) n =
      (star (U n) : E n →L[ℂ] E n) (f n) := by
  let g := l2FiberUnitaryApply (fun n => star (U n)) f
  have hug : (l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) g = f := by
    apply lp.ext
    funext i
    exact congrArg (fun T : E i →L[ℂ] E i => T (f i)) (U i).property.2
  have h := congrArg (fun T : lp E 2 →L[ℂ] lp E 2 => T g)
    (l2FiberUnitary U).property.1
  calc
    ((star (l2FiberUnitary U) : lp E 2 →L[ℂ] lp E 2) f) n =
        ((star (l2FiberUnitary U) : lp E 2 →L[ℂ] lp E 2)
          ((l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) g)) n := by rw [hug]
    _ = g n := congrArg (fun x : lp E 2 => x n) h
    _ = _ := rfl

theorem blockOperator_conjugation_inclusion
    {M N : ∀ n, VonNeumannAlgebra (E n)} {A B : VonNeumannAlgebra (lp E 2)}
    (hA : BlockAlgebraDecomposition M A) (hB : BlockAlgebraDecomposition N B)
    (U : ∀ n, unitary (E n →L[ℂ] E n))
    (hU : ∀ n, Conjugates (U n) (M n) (N n)) :
    ∀ T ∈ A, unitaryConj (l2FiberUnitary U) T ∈ B := by
  intro T hT
  obtain ⟨F, hFn, hFM, hFT⟩ := hA.decompose T hT
  let G : ∀ n, E n →L[ℂ] E n := fun n => unitaryConj (U n) (F n)
  obtain ⟨S, hS, hSG⟩ := hB.reconstruct G ‖T‖ (norm_nonneg _)
    (fun n => by simpa only [G, norm_unitaryConj] using hFn n)
    (fun n => (hU n).subset ⟨F n, hFM n, rfl⟩)
  have hTG : RepresentsBlockOperators G (unitaryConj (l2FiberUnitary U) T) := by
    intro f n
    change ((l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2)
      (T ((star (l2FiberUnitary U) : lp E 2 →L[ℂ] lp E 2) f))) n = _
    rw [l2FiberUnitary_apply, hFT, l2FiberUnitary_star_apply]
    rfl
  rw [hTG.unique hSG]
  exact hS

theorem conjugates_l2FiberUnitary
    {M N : ∀ n, VonNeumannAlgebra (E n)} {A B : VonNeumannAlgebra (lp E 2)}
    (hA : BlockAlgebraDecomposition M A) (hB : BlockAlgebraDecomposition N B)
    (U : ∀ n, unitary (E n →L[ℂ] E n))
    (hU : ∀ n, Conjugates (U n) (M n) (N n)) :
    Conjugates (l2FiberUnitary U) A B := by
  have hs : l2FiberUnitary (fun n => star (U n)) = star (l2FiberUnitary U) := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    exact (l2FiberUnitary_star_apply U f n).symm
  have hf := blockOperator_conjugation_inclusion hA hB U hU
  have hr := blockOperator_conjugation_inclusion hB hA (fun n => star (U n))
    (fun n => (hU n).symm)
  rw [hs] at hr
  apply Set.Subset.antisymm
  · rintro _ ⟨T, hT, rfl⟩
    exact hf T hT
  · intro S hS
    refine ⟨unitaryConj (star (l2FiberUnitary U)) S, hr S hS, ?_⟩
    simpa only [star_star] using unitaryConj_star_unitaryConj (star (l2FiberUnitary U)) S

theorem exists_bounded_conjugacy_of_block_implementers
    {M N : ∀ n, VonNeumannAlgebra (E n)} {A B : VonNeumannAlgebra (lp E 2)}
    (hA : BlockAlgebraDecomposition M A) (hB : BlockAlgebraDecomposition N B)
    {a : ℝ} (ha : 0 ≤ a)
    (hex : ∀ n, ∃ u : unitary (E n →L[ℂ] E n),
      Conjugates u (M n) (N n) ∧ ‖(u : E n →L[ℂ] E n) - 1‖ ≤ a) :
    ∃ u : unitary (lp E 2 →L[ℂ] lp E 2),
      Conjugates u A B ∧ ‖(u : lp E 2 →L[ℂ] lp E 2) - 1‖ ≤ a := by
  choose U hc hn using hex
  exact ⟨l2FiberUnitary U, conjugates_l2FiberUnitary hA hB U hc,
    norm_l2FiberUnitary_sub_one_le U ha hn⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DirectIntegralUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounds and adjoints for assembled measurable unitaries

The assembly is the actual multiplication operator on `L²(X,H)`.
An almost-everywhere fiber bound gives the same operator-norm bound.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_regularUnitaryField_sub_one_le (μ : Measure X)
    (U : X → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ᵐ t ∂μ, ‖(U t : H →L[ℂ] H) - 1‖ ≤ a) :
    ‖(regularUnitaryField μ U hU hUs : Lp H 2 μ →L[ℂ] Lp H 2 μ) - 1‖ ≤ a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  change ∀ᵐ t ∂μ, ‖((regularUnitaryField μ U hU hUs : Lp H 2 μ →L[ℂ] Lp H 2 μ) f - f) t‖ ≤ a * ‖f t‖
  filter_upwards [hbound, regularUnitaryField_apply_ae μ U hU hUs f,
    Lp.coeFn_sub ((regularUnitaryField μ U hU hUs : Lp H 2 μ →L[ℂ] Lp H 2 μ) f) f]
    with t hb hu hs
  simp only [Pi.sub_apply] at hs
  rw [hs, hu]
  change ‖((U t : H →L[ℂ] H) - 1) (f t)‖ ≤ a * ‖f t‖
  exact (((U t : H →L[ℂ] H) - 1).le_opNorm (f t)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableConjugacyTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable conjugacy relations from vector evaluations

The two countable strong-test families recognize actual algebra
conjugacy. Their measurability and the countable operator norm tests
give the bounded implementer relation used for measurable selection.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]
  (M N : X → VonNeumannAlgebra H)

theorem measurableSet_conjugates_of_vector_tests
    (A : ∀ p, StrongUnitBallTestSequence (M p)) (B : ∀ p, StrongUnitBallTestSequence (N p))
    (ξ : ℕ → H) (hξ : DenseRange ξ) (U : X → unitary (H →L[ℂ] H))
    (hAB : ∀ j q l, Measurable (fun p =>
      (unitaryConj (U p) ((A p).op j) - (B p).op q) (ξ l)))
    (hBA : ∀ j q l, Measurable (fun p =>
      (unitaryConj (star (U p)) ((B p).op j) - (A p).op q) (ξ l))) :
    MeasurableSet {p | Conjugates (U p) (M p) (N p)} := by
  have hL : MeasurableSet {p | ∀ j,
      CountableStrongTests ξ (Set.range (B p).op) (unitaryConj (U p) ((A p).op j))} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_countableStrongTests_range ξ
      (fun p => unitaryConj (U p) ((A p).op j)) (fun p => (B p).op) (hAB j)
  have hR : MeasurableSet {p | ∀ j,
      CountableStrongTests ξ (Set.range (A p).op) (unitaryConj (star (U p)) ((B p).op j))} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_countableStrongTests_range ξ
      (fun p => unitaryConj (star (U p)) ((B p).op j)) (fun p => (A p).op) (hBA j)
  have heq : {p | Conjugates (U p) (M p) (N p)} =
      {p | ∀ j, CountableStrongTests ξ (Set.range (B p).op) (unitaryConj (U p) ((A p).op j))} ∩
      {p | ∀ j, CountableStrongTests ξ (Set.range (A p).op) (unitaryConj (star (U p)) ((B p).op j))} := by
    ext p
    exact conjugates_iff_countable_strong_tests (A p) (B p) ξ hξ (U p)
  rw [heq]
  exact hL.inter hR

theorem measurableSet_bounded_conjugates_of_vector_tests
    (A : ∀ p, StrongUnitBallTestSequence (M p)) (B : ∀ p, StrongUnitBallTestSequence (N p))
    (ξ : ℕ → H) (hξ : DenseRange ξ) (U : X → unitary (H →L[ℂ] H))
    (hAB : ∀ j q l, Measurable (fun p =>
      (unitaryConj (U p) ((A p).op j) - (B p).op q) (ξ l)))
    (hBA : ∀ j q l, Measurable (fun p =>
      (unitaryConj (star (U p)) ((B p).op j) - (A p).op q) (ξ l)))
    (hU : ∀ l, Measurable (fun p => ((U p : H →L[ℂ] H) - 1) (ξ l)))
    {a : ℝ} (ha : 0 ≤ a) :
    MeasurableSet {p | Conjugates (U p) (M p) (N p) ∧ ‖(U p : H →L[ℂ] H) - 1‖ ≤ a} :=
  (measurableSet_conjugates_of_vector_tests M N A B ξ hξ U hAB hBA).inter
    (measurableSet_operator_norm_le ξ hξ (fun p => (U p : H →L[ℂ] H) - 1) ha hU)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongUnitaryCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.strongUnitarySpaceBorel _root_.OAI.KadisonKastler.strongUnitarySpaceMeasurable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A closed Polish coordinate model of the unitary group

Both the operator and its adjoint are evaluated on a fixed dense sequence.
The range is closed: coordinate limits extend to contractions, and the
inverse and adjoint identities pass to strong limits.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryCoordinates_injective (ξ : ℕ → H) (hξ : DenseRange ξ) :
    Function.Injective (unitaryCoordinates ξ) := by
  intro u v h
  apply Subtype.ext
  apply DFunLike.coe_injective
  apply hξ.equalizer (u : H →L[ℂ] H).continuous (v : H →L[ℂ] H).continuous
  exact congrArg Prod.fst h

private theorem unitary_norm_le_one (u : unitary (H →L[ℂ] H)) :
    ‖(u : H →L[ℂ] H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [Unitary.norm_map, one_mul, le_refl]

theorem isClosed_range_unitaryCoordinates (ξ : ℕ → H) (hξ : DenseRange ξ) :
    IsClosed (Set.range (unitaryCoordinates ξ)) := by
  apply IsSeqClosed.isClosed
  intro z p hz hp
  choose u hu using hz
  have hleft (j : ℕ) :
      Tendsto (fun n => (u n : H →L[ℂ] H) (ξ j)) atTop (𝓝 (p.1 j)) := by
    have ht := tendsto_pi_nhds.mp ((continuous_fst.tendsto p).comp hp) j
    change Tendsto (fun n => (z n).1 j) atTop (𝓝 (p.1 j)) at ht
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact congrFun (congrArg Prod.fst (hu n)) j
  have hright (j : ℕ) :
      Tendsto (fun n => (star (u n) : H →L[ℂ] H) (ξ j)) atTop (𝓝 (p.2 j)) := by
    have ht := tendsto_pi_nhds.mp ((continuous_snd.tendsto p).comp hp) j
    change Tendsto (fun n => (z n).2 j) atTop (𝓝 (p.2 j)) at ht
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact congrFun (congrArg Prod.snd (hu n)) j
  obtain ⟨U, _, hlimU⟩ := exists_strong_limit_of_dense_contractions ξ hξ
    (fun n => (u n : H →L[ℂ] H)) (fun n => unitary_norm_le_one (u n))
    (fun j => (hleft j).cauchySeq)
  obtain ⟨V, _, hlimV⟩ := exists_strong_limit_of_dense_contractions ξ hξ
    (fun n => (star (u n) : H →L[ℂ] H)) (fun n => unitary_norm_le_one (star (u n)))
    (fun j => (hright j).cauchySeq)
  have hstar : star U = V := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_right ℂ
    intro x
    have ht := (hlimV y).inner (𝕜 := ℂ)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
    have ht' := (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).inner
      (𝕜 := ℂ) (hlimU x)
    simp only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at ht ⊢
    exact (tendsto_nhds_unique ht ht').symm
  have hUV : U * V = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have ht := tendsto_mul_contractions
      (fun n => (u n : H →L[ℂ] H)) (fun n => (star (u n) : H →L[ℂ] H))
      U V (fun n => unitary_norm_le_one (u n)) hlimU hlimV x
    have hz : (fun n : ℕ => ((u n : H →L[ℂ] H) *
        (star (u n) : H →L[ℂ] H)) x) = fun _ => (1 : H →L[ℂ] H) x := by
      funext n
      exact congrArg (fun T : H →L[ℂ] H => T x) (u n).property.2
    change Tendsto (fun n => ((u n : H →L[ℂ] H) *
      (star (u n) : H →L[ℂ] H)) x) atTop (𝓝 ((U * V) x)) at ht
    rw [hz] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hVU : V * U = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have ht := tendsto_mul_contractions
      (fun n => (star (u n) : H →L[ℂ] H)) (fun n => (u n : H →L[ℂ] H))
      V U (fun n => unitary_norm_le_one (star (u n))) hlimV hlimU x
    simp only [Unitary.coe_star_mul_self] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  let w : unitary (H →L[ℂ] H) := ⟨U, by rw [Unitary.mem_iff, hstar]; exact ⟨hVU, hUV⟩⟩
  refine ⟨w, ?_⟩
  apply Prod.ext
  · funext j
    exact tendsto_nhds_unique (hlimU (ξ j)) (hleft j)
  · funext j
    change star U (ξ j) = p.2 j
    rw [hstar]
    exact tendsto_nhds_unique (hlimV (ξ j)) (hright j)

theorem strongUnitarySpace_polish [SeparableSpace H] (ξ : ℕ → H) (hξ : DenseRange ξ) :
    PolishSpace (StrongUnitarySpace ξ) :=
  (isClosed_range_unitaryCoordinates ξ hξ).polishSpace

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongUnitaryEvaluation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.strongUnitarySpaceBorel _root_.OAI.KadisonKastler.strongUnitarySpaceMeasurable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Evaluation on the strong-star Polish unitary model -/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryCoordinates_decode (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    unitaryCoordinates ξ (decodeStrongUnitary ξ p) = p.val :=
  Classical.choose_spec p.property

@[simp] theorem decodeStrongUnitary_apply_test (ξ : ℕ → H) (p : StrongUnitarySpace ξ) (j : ℕ) :
    (decodeStrongUnitary ξ p : H →L[ℂ] H) (ξ j) = p.val.1 j :=
  congrFun (congrArg Prod.fst (unitaryCoordinates_decode ξ p)) j

@[simp] theorem star_decodeStrongUnitary_apply_test (ξ : ℕ → H)
    (p : StrongUnitarySpace ξ) (j : ℕ) :
    (star (decodeStrongUnitary ξ p) : H →L[ℂ] H) (ξ j) = p.val.2 j :=
  congrFun (congrArg Prod.snd (unitaryCoordinates_decode ξ p)) j

theorem decode_encodeStrongUnitary (ξ : ℕ → H) (hξ : DenseRange ξ)
    (u : unitary (H →L[ℂ] H)) :
    decodeStrongUnitary ξ (encodeStrongUnitary ξ u) = u :=
  unitaryCoordinates_injective ξ hξ (unitaryCoordinates_decode ξ _)

private theorem decode_norm_le_one (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    ‖(decodeStrongUnitary ξ p : H →L[ℂ] H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [Unitary.norm_map, one_mul, le_refl]

private theorem star_decode_norm_le_one (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    ‖(star (decodeStrongUnitary ξ p) : H →L[ℂ] H)‖ ≤ 1 := by
  rw [norm_star]
  exact decode_norm_le_one ξ p

theorem continuous_decodeStrongUnitary_apply (ξ : ℕ → H) (hξ : DenseRange ξ) (x : H) :
    Continuous (fun p : StrongUnitarySpace ξ => (decodeStrongUnitary ξ p : H →L[ℂ] H) x) := by
  apply SeqContinuous.continuous
  intro p q hp
  apply tendsto_apply_of_dense_contractions ξ hξ
    (fun n => (decodeStrongUnitary ξ (p n) : H →L[ℂ] H))
    (decodeStrongUnitary ξ q : H →L[ℂ] H)
    (fun n => decode_norm_le_one ξ (p n)) (decode_norm_le_one ξ q)
  intro j
  have hc : Continuous (fun p : StrongUnitarySpace ξ => p.val.1 j) :=
    (continuous_apply j).comp (continuous_fst.comp continuous_subtype_val)
  have ht := (hc.tendsto q).comp hp
  convert ht using 1
  · funext n
    exact decodeStrongUnitary_apply_test ξ (p n) j
  · rw [decodeStrongUnitary_apply_test]

theorem continuous_star_decodeStrongUnitary_apply (ξ : ℕ → H) (hξ : DenseRange ξ) (x : H) :
    Continuous (fun p : StrongUnitarySpace ξ =>
      (star (decodeStrongUnitary ξ p) : H →L[ℂ] H) x) := by
  apply SeqContinuous.continuous
  intro p q hp
  apply tendsto_apply_of_dense_contractions ξ hξ
    (fun n => (star (decodeStrongUnitary ξ (p n)) : H →L[ℂ] H))
    (star (decodeStrongUnitary ξ q) : H →L[ℂ] H)
    (fun n => star_decode_norm_le_one ξ (p n)) (star_decode_norm_le_one ξ q)
  intro j
  have hc : Continuous (fun p : StrongUnitarySpace ξ => p.val.2 j) :=
    (continuous_apply j).comp (continuous_snd.comp continuous_subtype_val)
  have ht := (hc.tendsto q).comp hp
  convert ht using 1
  · funext n
    exact star_decodeStrongUnitary_apply_test ξ (p n) j
  · rw [star_decodeStrongUnitary_apply_test]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PolishConjugacyRelation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The Borel implementer relation on the Polish unitary model

Measurable evaluation of the countable contraction fields suffices.
No measurability in the operator norm topology is imposed.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

omit [CompleteSpace H] in
theorem measurable_operator_field_apply (T : X → H →L[ℂ] H)
    (hT : ∀ x, Measurable (fun p => T p x)) (v : X → H) (hv : Measurable v) :
    Measurable (fun p => T p (v p)) := by
  have hm : Measurable (fun p : H × X => T p.2 p.1) :=
    measurable_uncurry_of_continuous_of_measurable (fun p => (T p).continuous) hT
  exact hm.comp (hv.prodMk measurable_id)

theorem measurable_conjugation_on_strongUnitarySpace
    (ξ : ℕ → H) (hξ : DenseRange ξ) (T : X → H →L[ℂ] H)
    (hT : ∀ x, Measurable (fun p => T p x)) (x : H) :
    Measurable (fun p : X × StrongUnitarySpace ξ =>
      unitaryConj (decodeStrongUnitary ξ p.2) (T p.1) x) := by
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  have hU (y : H) : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (decodeStrongUnitary ξ p.2 : H →L[ℂ] H) y) :=
    (continuous_decodeStrongUnitary_apply ξ hξ y).measurable.comp measurable_snd
  have hUs : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (star (decodeStrongUnitary ξ p.2) : H →L[ℂ] H) x) :=
    (continuous_star_decodeStrongUnitary_apply ξ hξ x).measurable.comp measurable_snd
  have hTx := measurable_operator_field_apply (fun p : X × StrongUnitarySpace ξ => T p.1)
    (fun y => (hT y).comp measurable_fst) _ hUs
  exact measurable_operator_field_apply
    (fun p : X × StrongUnitarySpace ξ => (decodeStrongUnitary ξ p.2 : H →L[ℂ] H)) hU _ hTx

theorem measurable_star_conjugation_on_strongUnitarySpace
    (ξ : ℕ → H) (hξ : DenseRange ξ) (T : X → H →L[ℂ] H)
    (hT : ∀ x, Measurable (fun p => T p x)) (x : H) :
    Measurable (fun p : X × StrongUnitarySpace ξ =>
      unitaryConj (star (decodeStrongUnitary ξ p.2)) (T p.1) x) := by
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  have hUs (y : H) : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (star (decodeStrongUnitary ξ p.2) : H →L[ℂ] H) y) :=
    (continuous_star_decodeStrongUnitary_apply ξ hξ y).measurable.comp measurable_snd
  have hU : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (decodeStrongUnitary ξ p.2 : H →L[ℂ] H) x) :=
    (continuous_decodeStrongUnitary_apply ξ hξ x).measurable.comp measurable_snd
  have hTx := measurable_operator_field_apply (fun p : X × StrongUnitarySpace ξ => T p.1)
    (fun y => (hT y).comp measurable_fst) _ hU
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp] using
    measurable_operator_field_apply
      (fun p : X × StrongUnitarySpace ξ => (star (decodeStrongUnitary ξ p.2) : H →L[ℂ] H))
      hUs _ hTx

/-- This relation has precisely the algebra-conjugacy and displacement
conditions required by the measurable selection step. -/
theorem measurableSet_bounded_implementer_relation
    (M N : X → VonNeumannAlgebra H)
    (A : ∀ p, StrongUnitBallTestSequence (M p)) (B : ∀ p, StrongUnitBallTestSequence (N p))
    (hA : ∀ j x, Measurable (fun p => (A p).op j x))
    (hB : ∀ j x, Measurable (fun p => (B p).op j x))
    (ξ : ℕ → H) (hξ : DenseRange ξ) {a : ℝ} (ha : 0 ≤ a) :
    MeasurableSet {p : X × StrongUnitarySpace ξ |
      Conjugates (decodeStrongUnitary ξ p.2) (M p.1) (N p.1) ∧
      ‖(decodeStrongUnitary ξ p.2 : H →L[ℂ] H) - 1‖ ≤ a} := by
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  apply measurableSet_bounded_conjugates_of_vector_tests
    (fun p : X × StrongUnitarySpace ξ => M p.1)
    (fun p : X × StrongUnitarySpace ξ => N p.1)
    (fun p => A p.1) (fun p => B p.1) ξ hξ
    (fun p => decodeStrongUnitary ξ p.2)
  · intro j q l
    simpa only [sub_apply, Pi.sub_def, Function.comp_def] using
      (measurable_conjugation_on_strongUnitarySpace ξ hξ (fun p => (A p).op j)
        (hA j) (ξ l)).sub ((hB q (ξ l)).comp measurable_fst)
  · intro j q l
    simpa only [sub_apply, Pi.sub_def, Function.comp_def] using
      (measurable_star_conjugation_on_strongUnitarySpace ξ hξ (fun p => (B p).op j)
        (hB j) (ξ l)).sub ((hA q (ξ l)).comp measurable_fst)
  · intro l
    simpa only [sub_apply, one_apply_eq_self, Pi.sub_def, Function.comp_def] using
      ((continuous_decodeStrongUnitary_apply ξ hξ (ξ l)).measurable.comp
        measurable_snd).sub measurable_const
  · exact ha

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableImplementers
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Selecting measurable implementer fields

The input is the published Borel uniformization theorem. The conjugacy
relation, its Borel structure, and the strong measurability of the
selected operator and adjoint evaluations are proved locally.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u v

variable {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

theorem exists_measurable_implementer_field
    (hpub : PublishedUnitaryBorelSelection.{u, v}) (μ : Measure X) [IsFiniteMeasure μ]
    (M N : X → VonNeumannAlgebra H)
    (A : ∀ p, StrongUnitBallTestSequence (M p)) (B : ∀ p, StrongUnitBallTestSequence (N p))
    (hA : ∀ j x, Measurable (fun p => (A p).op j x))
    (hB : ∀ j x, Measurable (fun p => (B p).op j x))
    {a : ℝ} (ha : 0 ≤ a)
    (hex : ∀ᵐ p ∂μ, ∃ u : unitary (H →L[ℂ] H),
      Conjugates u (M p) (N p) ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ a) :
    ∃ U : X → unitary (H →L[ℂ] H),
      (∀ x, AEStronglyMeasurable (fun p => (U p : H →L[ℂ] H) x) μ) ∧
      (∀ x, AEStronglyMeasurable (fun p => (star (U p) : H →L[ℂ] H) x) μ) ∧
      ∀ᵐ p ∂μ, Conjugates (U p) (M p) (N p) ∧ ‖(U p : H →L[ℂ] H) - 1‖ ≤ a := by
  obtain ⟨ξ, hξ⟩ := exists_dense_seq (α := H)
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  let R : Set (X × StrongUnitarySpace ξ) := {p |
    Conjugates (decodeStrongUnitary ξ p.2) (M p.1) (N p.1) ∧
    ‖(decodeStrongUnitary ξ p.2 : H →L[ℂ] H) - 1‖ ≤ a}
  have hR : MeasurableSet R :=
    measurableSet_bounded_implementer_relation M N A B hA hB ξ hξ ha
  have hne : ∀ᵐ p ∂μ, ∃ q : StrongUnitarySpace ξ, (p, q) ∈ R := by
    filter_upwards [hex] with p hp
    obtain ⟨u, hu⟩ := hp
    refine ⟨encodeStrongUnitary ξ u, ?_⟩
    change Conjugates (decodeStrongUnitary ξ (encodeStrongUnitary ξ u)) (M p) (N p) ∧ _
    simpa only [decode_encodeStrongUnitary ξ hξ] using hu
  obtain ⟨f, hf, hrel⟩ := hpub X H ξ hξ μ R hR hne
  refine ⟨fun p => decodeStrongUnitary ξ (f p), ?_, ?_, hrel⟩
  · intro x
    exact ((continuous_decodeStrongUnitary_apply ξ hξ x).measurable.comp_aemeasurable hf).aestronglyMeasurable
  · intro x
    exact ((continuous_star_decodeStrongUnitary_apply ξ hξ x).measurable.comp_aemeasurable hf).aestronglyMeasurable

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DirectIntegralConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling fiber conjugacies on the actual direct-integral space

`OperatorFieldDecomposition` records the decomposition and reconstruction
properties of a given constant-fiber direct integral. It is data, not a
published theorem or an existence assertion. The assembly argument below
uses actual multiplication unitaries on `L²(X,H)`.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.unique {μ : Measure X} {F : X → H →L[ℂ] H}
    {T S : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hT : RepresentsOperatorField μ F T) (hS : RepresentsOperatorField μ F S) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hT f).trans (hS f).symm)

theorem operatorField_conjugation_inclusion (μ : Measure X)
    {M N : X → VonNeumannAlgebra H} {A B : VonNeumannAlgebra (Lp H 2 μ)}
    (hA : OperatorFieldDecomposition μ M A) (hB : OperatorFieldDecomposition μ N B)
    (U : X → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    (u : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hu : ∀ f : Lp H 2 μ, (u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f =ᵐ[μ]
      fun t => (U t : H →L[ℂ] H) (f t))
    (hus : ∀ f : Lp H 2 μ, (star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f =ᵐ[μ]
      fun t => (star (U t) : H →L[ℂ] H) (f t))
    (hconj : ∀ᵐ t ∂μ, Conjugates (U t) (M t) (N t)) :
    ∀ T ∈ A, unitaryConj u T ∈ B := by
  intro T hT
  obtain ⟨F, hFm, hFn, hFM, hFT⟩ := hA.decompose T hT
  let G : X → H →L[ℂ] H := fun t => unitaryConj (U t) (F t)
  have hGm (x : H) : AEStronglyMeasurable (fun t => G t x) μ := by
    exact aestronglyMeasurable_field_apply (fun t => (U t : H →L[ℂ] H)) hU _
      (aestronglyMeasurable_field_apply F hFm _ (hUs x))
  have hGn : ∀ᵐ t ∂μ, ‖G t‖ ≤ ‖T‖ := by
    filter_upwards [hFn] with t ht
    simpa only [G, norm_unitaryConj] using ht
  have hGN : ∀ᵐ t ∂μ, G t ∈ N t := by
    filter_upwards [hFM, hconj] with t ht hc
    exact hc.subset ⟨F t, ht, rfl⟩
  obtain ⟨S, hS, hSG⟩ := hB.reconstruct G ‖T‖ (norm_nonneg _) hGm hGn hGN
  have hG : RepresentsOperatorField μ G (unitaryConj u T) := by
    intro f
    filter_upwards [hu (T ((star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f)),
      hFT ((star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f), hus f] with t huv htf husf
    change ((u : Lp H 2 μ →L[ℂ] Lp H 2 μ)
      (T ((star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f))) t = _
    rw [huv, htf, husf]
    rfl
  rw [hG.unique hSG]
  exact hS

theorem conjugates_regularUnitaryField (μ : Measure X)
    {M N : X → VonNeumannAlgebra H} {A B : VonNeumannAlgebra (Lp H 2 μ)}
    (hA : OperatorFieldDecomposition μ M A) (hB : OperatorFieldDecomposition μ N B)
    (U : X → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    (hconj : ∀ᵐ t ∂μ, Conjugates (U t) (M t) (N t)) :
    Conjugates (regularUnitaryField μ U hU hUs) A B := by
  let u := regularUnitaryField μ U hU hUs
  have hu := regularUnitaryField_apply_ae μ U hU hUs
  have hus := regularUnitaryField_star_apply_ae μ U hU hUs
  have hforward := operatorField_conjugation_inclusion μ hA hB U hU hUs u hu hus hconj
  have hreverse : ∀ S ∈ B, unitaryConj (star u) S ∈ A :=
    operatorField_conjugation_inclusion μ hB hA (fun t => star (U t)) hUs
      (fun x => by simpa only [Unitary.coe_star, star_star] using hU x) (star u) hus
      (fun f => by simpa only [Unitary.coe_star, star_star] using hu f)
      (hconj.mono fun _ h => h.symm)
  apply Set.Subset.antisymm
  · rintro _ ⟨T, hT, rfl⟩
    exact hforward T hT
  · intro S hS
    refine ⟨unitaryConj (star u) S, hreverse S hS, ?_⟩
    simpa only [star_star] using unitaryConj_star_unitaryConj (star u) S

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableConjugacyAssembly
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # From fiber implementers to a bounded global conjugacy

This completes selection and assembly for a constant-fiber stratum of a
given central decomposition. The decomposition data and the factor
implementers are the explicit premises; neither is silently assumed to
exist for an arbitrary pair of algebras.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u v

variable {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

theorem exists_bounded_conjugacy_of_fiber_implementers
    (hpub : PublishedUnitaryBorelSelection.{u, v}) (μ : Measure X) [IsFiniteMeasure μ]
    (M N : X → VonNeumannAlgebra H)
    (A B : VonNeumannAlgebra (Lp H 2 μ))
    (hMA : OperatorFieldDecomposition μ M A) (hNB : OperatorFieldDecomposition μ N B)
    (sM : ∀ p, StrongUnitBallTestSequence (M p))
    (sN : ∀ p, StrongUnitBallTestSequence (N p))
    (hmM : ∀ j x, Measurable (fun p => (sM p).op j x))
    (hmN : ∀ j x, Measurable (fun p => (sN p).op j x))
    {a : ℝ} (ha : 0 ≤ a)
    (hex : ∀ᵐ p ∂μ, ∃ u : unitary (H →L[ℂ] H),
      Conjugates u (M p) (N p) ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ a) :
    ∃ u : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ),
      Conjugates u A B ∧ ‖(u : Lp H 2 μ →L[ℂ] Lp H 2 μ) - 1‖ ≤ a := by
  obtain ⟨U, hU, hUs, hrel⟩ := exists_measurable_implementer_field hpub μ M N sM sN hmM hmN ha hex
  refine ⟨regularUnitaryField μ U hU hUs, ?_, ?_⟩
  · exact conjugates_regularUnitaryField μ hMA hNB U hU hUs (hrel.mono fun _ h => h.1)
  · exact norm_regularUnitaryField_sub_one_le μ U hU hUs ha (hrel.mono fun _ h => h.2)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialConjugacyTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting an implementer through Hilbert coordinates -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_spatialTransportUnitary_sub_one (e : H ≃ₗᵢ[ℂ] K)
    (u : unitary (H →L[ℂ] H)) :
    ‖(spatialTransportUnitary e u : K →L[ℂ] K) - 1‖ = ‖(u : H →L[ℂ] H) - 1‖ := by
  rw [coe_spatialTransportUnitary, ← map_one e.conjStarAlgEquiv, ← map_sub]
  exact norm_spatialConjugate e _

theorem unitaryConj_spatialTransport (e : H ≃ₗᵢ[ℂ] K)
    (u : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    unitaryConj (spatialTransportUnitary e u) (e.conjStarAlgEquiv T) =
      e.conjStarAlgEquiv (unitaryConj u T) := by
  simp only [unitaryConj, coe_spatialTransportUnitary, map_mul, map_star]

theorem Conjugates.spatialTransport {M N : VonNeumannAlgebra H}
    {u : unitary (H →L[ℂ] H)} (hu : Conjugates u M N) (e : H ≃ₗᵢ[ℂ] K) :
    Conjugates (spatialTransportUnitary e u)
      (spatialTransportAlgebra e M) (spatialTransportAlgebra e N) := by
  change unitaryConj (spatialTransportUnitary e u) ''
      (e.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H))) =
    e.conjStarAlgEquiv '' (N : Set (H →L[ℂ] H))
  simpa only [Set.image_image, unitaryConj_spatialTransport] using
    congrArg (fun S : Set (H →L[ℂ] H) => e.conjStarAlgEquiv '' S) hu

theorem exists_bounded_conjugacy_of_spatialTransport
    (e : H ≃ₗᵢ[ℂ] K) (M N : VonNeumannAlgebra H) {a : ℝ}
    (hex : ∃ u : unitary (K →L[ℂ] K),
      Conjugates u (spatialTransportAlgebra e M) (spatialTransportAlgebra e N) ∧
        ‖(u : K →L[ℂ] K) - 1‖ ≤ a) :
    ∃ u : unitary (H →L[ℂ] H),
      Conjugates u M N ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ a := by
  obtain ⟨u, hu, hnorm⟩ := hex
  refine ⟨spatialTransportUnitary e.symm u, ?_, ?_⟩
  · simpa only [spatialTransportAlgebra_symm] using hu.spatialTransport e.symm
  · simpa only [norm_spatialTransportUnitary_sub_one] using hnorm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralConjugacyAssembly
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Selecting and assembling implementers in a common central decomposition -/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_bounded_conjugacy_from_centralPair_oai
    (hK : PublishedKaplanskyDensity.{u}) (hSelect : PublishedUnitaryBorelSelection.{u, u})
    (M N : VonNeumannAlgebra H) (A B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H)))
    (hAs : IsSeparable (A : Set (H →L[ℂ] H)))
    (hBs : IsSeparable (B : Set (H →L[ℂ] H)))
    {hAC : A ≤ C} {hBC : B ≤ C} (D : CentralPairDecomposition M N A B C hAC hBC)
    {a : ℝ} (ha : 0 ≤ a)
    (hex : ∀ n, ∀ᵐ x ∂(D.stratum n).μ,
      ∃ v : unitary ((D.stratum n).K →L[ℂ] (D.stratum n).K),
        Conjugates v
          (generatedVonNeumannAlgebra
            ((D.representation n x).comp (StarSubalgebra.inclusion hAC)).range)
          (generatedVonNeumannAlgebra
            ((D.representation n x).comp (StarSubalgebra.inclusion hBC)).range) ∧
        ‖(v : (D.stratum n).K →L[ℂ] (D.stratum n).K) - 1‖ ≤ a) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧ ‖(v : H →L[ℂ] H) - 1‖ ≤ a := by
  let := StarSubalgebra.cstarAlgebra A (h_closed := hAc)
  let := StarSubalgebra.cstarAlgebra B (h_closed := hBc)
  let : SeparableSpace A := hAs.separableSpace
  let : SeparableSpace B := hBs.separableSpace
  obtain ⟨sA, hsA, hdA⟩ := exists_norm_dense_unitBall_sequence A
  obtain ⟨sB, hsB, hdB⟩ := exists_norm_dense_unitBall_sequence B
  apply exists_bounded_conjugacy_of_spatialTransport D.coordinates M N
  apply exists_bounded_conjugacy_of_block_implementers D.leftBlocks D.rightBlocks ha
  intro n
  let φA (x : (D.stratum n).X) :=
    (D.representation n x).comp (StarSubalgebra.inclusion hAC)
  let φB (x : (D.stratum n).X) :=
    (D.representation n x).comp (StarSubalgebra.inclusion hBC)
  let SA (x : (D.stratum n).X) := quotientStrongUnitBallTests hK (φA x) sA hsA hdA
  let SB (x : (D.stratum n).X) := quotientStrongUnitBallTests hK (φB x) sB hsB hdB
  apply exists_bounded_conjugacy_of_fiber_implementers hSelect (D.stratum n).μ
    (fun x => generatedVonNeumannAlgebra (φA x).range)
    (fun x => generatedVonNeumannAlgebra (φB x).range)
    (D.leftBlock n) (D.rightBlock n) (D.leftFields n) (D.rightFields n) SA SB
  · intro j ξ
    exact D.representation_measurable n (StarSubalgebra.inclusion hAC (sA j)) ξ
  · intro j ξ
    exact D.representation_measurable n (StarSubalgebra.inclusion hBC (sB j)) ξ
  · exact ha
  · exact hex n

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.exists_bounded_conjugacy_from_centralPair_oai.{u} := @OAI.KadisonKastler.exists_bounded_conjugacy_from_centralPair_oai.{u}
