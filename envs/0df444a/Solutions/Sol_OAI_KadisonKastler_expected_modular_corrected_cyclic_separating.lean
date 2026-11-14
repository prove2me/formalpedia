-- Prove2me | solution 1 for OAI.KadisonKastler.expected_modular_corrected_cyclic_separating
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:59:22.171378+00:00
-- url     : https://prove2.me/submissions/e5697680-c36c-48fb-a067-3298d346c63e

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
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
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
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K067
import Theorems.Thm_OAI_KadisonKastler_relative_irreducibility_of_near_increasing_matrices

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem kkDistance_triangle (M N P : VonNeumannAlgebra H) :
    kkDistance M P ≤ kkDistance M N + kkDistance N P :=
  Metric.hausdorffDist_triangle (unitBall_hausdorffEDist_ne_top M N)

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

/-- The elementary displacement estimate used at every matrix level in §2. -/
theorem norm_unitaryConj_sub_le (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj v x - x‖ ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ := by
  have hid : unitaryConj v x - x =
      (((v : H →L[ℂ] H) - 1) * x) * star (v : H →L[ℂ] H) +
        x * (star (v : H →L[ℂ] H) - 1) := by
    dsimp [unitaryConj]
    noncomm_ring
  have hstar : ‖star (v : H →L[ℂ] H) - 1‖ = ‖(v : H →L[ℂ] H) - 1‖ := by
    simpa only [star_sub, star_one] using norm_star ((v : H →L[ℂ] H) - 1)
  calc
    ‖unitaryConj v x - x‖ ≤
        ‖(((v : H →L[ℂ] H) - 1) * x) * star (v : H →L[ℂ] H)‖ +
          ‖x * (star (v : H →L[ℂ] H) - 1)‖ := hid ▸ norm_add_le _ _
    _ = ‖((v : H →L[ℂ] H) - 1) * x‖ +
          ‖x * (star (v : H →L[ℂ] H) - 1)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ +
          ‖x‖ * ‖star (v : H →L[ℂ] H) - 1‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ := by rw [hstar]; ring

theorem kkDistance_le_of_conjugates {M N : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) :
    kkDistance M N ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ := by
  have hb := unitaryConj_unitBall hv
  apply Metric.hausdorffDist_le_of_mem_dist (mul_nonneg (by norm_num) (norm_nonneg _))
  · intro x hx
    refine ⟨unitaryConj v x, hb ▸ Set.mem_image_of_mem _ hx, ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact (norm_unitaryConj_sub_le v x).trans
      (mul_le_of_le_one_right (mul_nonneg (by norm_num) (norm_nonneg _)) hx.2)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (show y ∈ unitaryConj v '' unitBall M from hb.symm ▸ hy)
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm]
    exact (norm_unitaryConj_sub_le v x).trans
      (mul_le_of_le_one_right (mul_nonneg (by norm_num) (norm_nonneg _)) hx.2)

/-- Moving one algebra by a small unitary increases its gap by at most twice
the unitary displacement (the ordinary-distance part of equation (2.1)). -/
theorem kkDistance_conjugate_le {M N P : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v N P) :
    kkDistance M P ≤ kkDistance M N + 2 * ‖(v : H →L[ℂ] H) - 1‖ :=
  (kkDistance_triangle M N P).trans (add_le_add le_rfl (kkDistance_le_of_conjugates hv))

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
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Right actions and the common subalgebra projection

The right action of a common unitary reduces the closed subspace generated
by the common algebra and the standard vector. Thus equality of the two
basic constructions gives the cross-commutant membership required for the
common right-action argument, without identifying the whole commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded operator preserving the algebra orbit also preserves its
closed linear span. -/
theorem vectorOrbitClosure_invariant_of_orbit
    (R : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (T : H →L[ℂ] H)
    (hT : ∀ x : R, ∃ y : R, T (x.val Ω) = y.val Ω)
    {ξ : H} (hξ : ξ ∈ Generator.vectorOrbitClosure R Ω) :
    T ξ ∈ Generator.vectorOrbitClosure R Ω := by
  have h : (Generator.vectorOrbitMap R Ω).range.topologicalClosure ≤
      (Generator.vectorOrbitClosure R Ω).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hT x
      exact Submodule.le_topologicalClosure _ ⟨y, hy.symm⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact h hξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedPairCyclicity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Cyclicity from the common left and right vector actions

The projection onto the closed commutant orbit belongs to the original
von Neumann algebra. Common vector actions make it commute with the
irreducible common subalgebra, so its scalar value is one. Applying the
same argument to the commutant proves both cyclicity and separation.
No cyclicity or standard-form conclusion is assumed.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A common right vector value makes the left action preserve the closed
commutant orbit. -/
theorem commutant_orbit_invariant_of_common_vector
    (N : VonNeumannAlgebra H) (Ω : H)
    (r : H →L[ℂ] H) (hr : r ∈ N)
    (s : H →L[ℂ] H) (hs : s ∈ N.commutant)
    (hvector : r Ω = s Ω)
    {ξ : H} (hξ : ξ ∈ Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω) :
    r ξ ∈ Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω := by
  apply vectorOrbitClosure_invariant_of_orbit N.commutant.toStarSubalgebra Ω r ?_ hξ
  intro x
  refine ⟨x * (⟨s, hs⟩ : Algebra N.commutant), ?_⟩
  have hc : r * x.val = x.val * r :=
    VonNeumannAlgebra.mem_commutant_iff.mp x.property r hr
  calc
    r (x.val Ω) = x.val (r Ω) :=
      congrArg (fun T : H →L[ℂ] H => T Ω) hc
    _ = x.val (s Ω) := by rw [hvector]
    _ = (x * (⟨s, hs⟩ : Algebra N.commutant)).val Ω := rfl

/-- Irreducibility and common vector actions force the commutant orbit to
be all of the actual Hilbert space. -/
theorem commutant_orbitClosure_eq_top_of_relative_scalar
    (N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (Ω : H) (hΩ : Ω ≠ 0)
    (hirr : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hvector : ∀ r ∈ R, ∃ s ∈ N.commutant, r Ω = s Ω) :
    Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω = ⊤ := by
  let K := Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω
  have hpN : K.starProjection ∈ N := by
    have hp : K.starProjection ∈ N.commutant.commutant := by
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro x hx
      exact (Generator.vectorOrbitProjection_commutes N.commutant.toStarSubalgebra
        Ω ⟨x, hx⟩).symm
    simpa only [VonNeumannAlgebra.commutant_commutant] using hp
  have hpR (r : H →L[ℂ] H) (hr : r ∈ R) : r * K.starProjection = K.starProjection * r := by
    symm
    apply Generator.starProjection_commutes_of_invariant
    · obtain ⟨s, hs, hvec⟩ := hvector r hr
      exact fun ξ hξ => commutant_orbit_invariant_of_common_vector N Ω r
        (hRN hr) s hs hvec hξ
    · obtain ⟨s, hs, hvec⟩ := hvector (star r) (R.star_mem' hr)
      exact fun ξ hξ => commutant_orbit_invariant_of_common_vector N Ω (star r)
        (hRN (R.star_mem' hr)) s hs hvec hξ
  obtain ⟨z, hz⟩ := hirr K.starProjection hpN hpR
  have hpΩ : K.starProjection Ω = Ω :=
    Submodule.starProjection_eq_self_iff.mpr (Generator.mem_vectorOrbitClosure _ _)
  have hz1 : z = 1 := by
    apply smul_left_injective ℂ hΩ
    have he := hpΩ
    rw [hz] at he
    simpa only [smul_apply, one_apply_eq_self, one_smul] using he
  have hp1 : K.starProjection = 1 := by simpa only [hz1, one_smul] using hz
  apply top_unique
  intro ξ _
  apply Submodule.starProjection_eq_self_iff.mp
  rw [show (Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω).starProjection = 1
    from hp1]
  rfl

/-- The corresponding dense-range formulation is suitable for uniqueness
of operators on the commutant orbit. -/
theorem commutant_orbit_dense_of_relative_scalar
    (N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (Ω : H) (hΩ : Ω ≠ 0)
    (hirr : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hvector : ∀ r ∈ R, ∃ s ∈ N.commutant, r Ω = s Ω) :
    DenseRange (fun x : Algebra N.commutant => x.val Ω) := by
  intro ξ
  have hξ : ξ ∈ Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω := by
    rw [commutant_orbitClosure_eq_top_of_relative_scalar N R hRN Ω hΩ hirr hvector]
    trivial
  exact hξ

/-- The common left/right vector correspondence gives both dense orbits.
Only the two relative scalar-commutant statements are used. -/
theorem preparedPair_dense_orbits
    (N : VonNeumannAlgebra H)
    (R S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (hSN : S ≤ N.commutant.toStarSubalgebra)
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirrR : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrS : ∀ T ∈ N.commutant, (∀ s ∈ S, s * T = T * s) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hRS : ∀ r ∈ R, ∃ s ∈ S, r Ω = s Ω)
    (hSR : ∀ s ∈ S, ∃ r ∈ R, s Ω = r Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) := by
  have hright : DenseRange (fun x : Algebra N.commutant => x.val Ω) :=
    commutant_orbit_dense_of_relative_scalar N R hRN Ω hΩ hirrR (by
      intro r hr
      obtain ⟨s, hs, hv⟩ := hRS r hr
      exact ⟨s, hSN hs, hv⟩)
  have hleft := commutant_orbit_dense_of_relative_scalar N.commutant S hSN Ω hΩ hirrS (by
    intro s hs
    obtain ⟨r, hr, hv⟩ := hSR s hs
    refine ⟨r, ?_, hv⟩
    rw [VonNeumannAlgebra.commutant_commutant]
    exact hRN hr)
  change DenseRange (fun x : N.commutant.commutant.toStarSubalgebra => x.val Ω) at hleft
  rw [VonNeumannAlgebra.commutant_commutant] at hleft
  exact ⟨hleft, hright⟩

/-- A vector cyclic for the commutant separates the original algebra. -/
theorem separating_of_dense_commutant_orbit
    (N : VonNeumannAlgebra H) (Ω : H)
    (hcyclic : DenseRange (fun x : Algebra N.commutant => x.val Ω))
    (a : Algebra N) (ha : a.val Ω = 0) : a = 0 := by
  apply Subtype.ext
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector N.commutant Ω hcyclic
    a.val 0
  · rw [VonNeumannAlgebra.commutant_commutant]
    exact a.property
  · exact N.commutant.commutant.zero_mem
  · simpa only [zero_apply] using ha

/-- In the prepared-pair argument, the actual common vector is cyclic and
separating for both sides; no separate standard-position premise remains. -/
theorem preparedPair_cyclic_separating
    (N : VonNeumannAlgebra H)
    (R S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (hSN : S ≤ N.commutant.toStarSubalgebra)
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirrR : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrS : ∀ T ∈ N.commutant, (∀ s ∈ S, s * T = T * s) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hRS : ∀ r ∈ R, ∃ s ∈ S, r Ω = s Ω)
    (hSR : ∀ s ∈ S, ∃ r ∈ R, s Ω = r Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) ∧
      (∀ a : Algebra N, a.val Ω = 0 → a = 0) ∧
      (∀ a : Algebra N.commutant, a.val Ω = 0 → a = 0) := by
  obtain ⟨hleft, hright⟩ := preparedPair_dense_orbits N R S hRN hSN Ω hΩ
    hirrR hirrS hRS hSR
  refine ⟨hleft, hright, separating_of_dense_commutant_orbit N Ω hright, ?_⟩
  apply separating_of_dense_commutant_orbit N.commutant Ω
  change DenseRange (fun x : N.commutant.commutant.toStarSubalgebra => x.val Ω)
  rw [VonNeumannAlgebra.commutant_commutant]
  exact hleft

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedPairCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Preserving the first inclusion under the commutant correction

The second local embedding in the preparation argument is chosen in the
von Neumann algebra generated by the right algebra and the neighboring
commutant. That entire generated algebra commutes with the common left
algebra. These are algebraic consequences of the location of the chosen
unitary; its existence is not assumed here as a new perturbation theorem.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The corrected pair has the same elementary gap loss as any unitary
movement of the neighbor. -/
theorem preparedPair_second_correction_gap
    (M N : VonNeumannAlgebra H) (w : unitary (H →L[ℂ] H)) :
    kkDistance M (unitaryConjugateAlgebra (star w) N) ≤
      kkDistance M N + 2 * ‖(w : H →L[ℂ] H) - 1‖ := by
  have hs : ‖((star w : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(w : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((w : H →L[ℂ] H) - 1)
  simpa only [hs] using
    (kkDistance_conjugate_le (M := M) (conjugates_unitaryConjugateAlgebra (star w) N))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateRightIrreducibility
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative irreducibility in the conjugate right algebra

The scalar relative commutant property transports through the actual
conjugate-linear operator map. In standard position its ambient image is
the commutant, so the source's left irreducibility supplies the right one.
The same central-vector identity supplies both orbit correspondences.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conjugateRightAlgebra_mono
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {R M : VonNeumannAlgebra H} (hRM : R ≤ M) :
    conjugateRightAlgebra J hJ R ≤ conjugateRightAlgebra J hJ M := by
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r, hRM hr, rfl⟩

/-- Scalar relative commutants are preserved by conjugation. -/
theorem relative_irreducibility_conjugateRightAlgebra
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R M : VonNeumannAlgebra H)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) :
    ∀ T ∈ conjugateRightAlgebra J hJ M,
      (∀ r ∈ conjugateRightAlgebra J hJ R, r * T = T * r) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  rintro _ ⟨T, hTM, rfl⟩ hcomm
  have hc : ∀ r ∈ R, r * T = T * r := by
    intro r hr
    have he := congrArg (conjugationOperator J)
      (hcomm (conjugationOperator J r) ⟨r, hr, rfl⟩)
    simpa only [conjugationOperator_mul J hJ, conjugationOperator_twice J hJ] using he
  obtain ⟨z, hz⟩ := hirr T hTM hc
  refine ⟨star z, ?_⟩
  rw [hz, conjugationOperator_smul, conjugationOperator_one J hJ]

/-- The right relative commutant in a standard-position source is scalar. -/
theorem relative_irreducibility_commutant_of_conjugation
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R M : VonNeumannAlgebra H)
    (hJM : conjugateRightAlgebra J hJ M = M.commutant)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) :
    ∀ T ∈ M.commutant,
      (∀ r ∈ conjugateRightAlgebra J hJ R, r * T = T * r) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  rw [← hJM]
  exact relative_irreducibility_conjugateRightAlgebra J hJ R M hirr

/-- The central-vector identity gives both directions of the left/right
orbit correspondence, including the adjoint required in the reverse one. -/
theorem commonRightVector_orbit_correspondence
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) (Ω : H)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω) :
    (∀ r ∈ R, ∃ s ∈ conjugateRightAlgebra J hJ R, r Ω = s Ω) ∧
    (∀ s ∈ conjugateRightAlgebra J hJ R, ∃ r ∈ R, s Ω = r Ω) := by
  constructor
  · intro r hr
    exact ⟨conjugationOperator J (star r),
      ⟨star r, R.toStarSubalgebra.star_mem' hr, rfl⟩, (hvector r hr).symm⟩
  · rintro _ ⟨r, hr, rfl⟩
    refine ⟨star r, R.toStarSubalgebra.star_mem' hr, ?_⟩
    simpa only [star_star] using hvector (star r) (R.toStarSubalgebra.star_mem' hr)

/-- The two relative scalar commutants and the common-vector identity
give actual cyclic and separating vectors for a neighbor. -/
theorem cyclic_separating_of_commonRight_irreducibility
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R N : VonNeumannAlgebra H) (hRN : R ≤ N)
    (hSN : conjugateRightAlgebra J hJ R ≤ N.commutant)
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirrR : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrS : ∀ T ∈ N.commutant,
      (∀ s ∈ conjugateRightAlgebra J hJ R, s * T = T * s) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) ∧
      (∀ a : Algebra N, a.val Ω = 0 → a = 0) ∧
      (∀ a : Algebra N.commutant, a.val Ω = 0 → a = 0) := by
  obtain ⟨hRS, hSR⟩ := commonRightVector_orbit_correspondence J hJ R Ω hvector
  exact preparedPair_cyclic_separating N R.toStarSubalgebra
    (conjugateRightAlgebra J hJ R).toStarSubalgebra hRN hSN Ω hΩ hirrR hirrS hRS hSR

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual matrix stages in the conjugate right algebra

Conjugation changes the scalar coefficients by complex conjugation, while
the conjugated matrix-unit entries retain their usual product laws. Thus
the right algebra is generated by actual increasing full matrix stages.
This lets the same finite averaging argument transfer its irreducibility
to a nearby commutant.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conjugateMatrixUnits_hom (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (H →L[ℂ] H)) (a : Matrix ι ι ℂ) :
    (conjugateMatrixUnits J hJ E).hom (fun i j => star (a i j)) =
      conjugationOperator J (E.hom a) := by
  change (∑ i, ∑ j, star (a i j) • conjugationOperator J (E.entry i j)) =
    conjugationOperator J (E.hom a)
  simp only [MatrixUnitSystem.hom_apply, conjugationOperator_sum_p0,
    conjugationOperator_smul]

theorem conjugation_mem_conjugateMatrixUnits (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (H →L[ℂ] H)) {x : H →L[ℂ] H} (hx : x ∈ E.algebra) :
    conjugationOperator J x ∈ (conjugateMatrixUnits J hJ E).algebra := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨(fun i j => star (a i j)), conjugateMatrixUnits_hom J hJ E a⟩

theorem conjugateMatrixUnits_mono (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra)) :
    Monotone (fun n => (conjugateMatrixUnits J hJ (E n)).algebra) := by
  intro i j hij
  apply ((conjugateMatrixUnits J hJ (E i)).algebra_le_iff
    (conjugateMatrixUnits J hJ (E j)).algebra).mpr
  intro a b
  exact conjugation_mem_conjugateMatrixUnits J hJ (E j)
    (hmono hij ((E i).entry_mem a b))

/-- The weakly generated right algebra is exactly generated by the
conjugated finite matrix stages. -/
theorem conjugateRightAlgebra_generated_matrixStages
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H)) :
    conjugateRightAlgebra J hJ (generatedVonNeumannAlgebra (⨆ n, (E n).algebra)) =
      generatedVonNeumannAlgebra (⨆ n, (conjugateMatrixUnits J hJ (E n)).algebra) := by
  let R := generatedVonNeumannAlgebra (⨆ n, (E n).algebra)
  let S := generatedVonNeumannAlgebra (⨆ n, (conjugateMatrixUnits J hJ (E n)).algebra)
  have hRS : R ≤ conjugateRightAlgebra J hJ S := by
    apply generatedVonNeumannAlgebra_le_of_le
    apply iSup_le
    intro n
    apply ((E n).algebra_le_iff (conjugateRightAlgebra J hJ S).toStarSubalgebra).mpr
    intro i j
    refine ⟨(conjugateMatrixUnits J hJ (E n)).entry i j, ?_, ?_⟩
    · exact subset_generatedVonNeumannAlgebra _
        ((le_iSup (fun n => (conjugateMatrixUnits J hJ (E n)).algebra) n)
          ((conjugateMatrixUnits J hJ (E n)).entry_mem i j))
    · exact conjugationOperator_twice J hJ ((E n).entry i j)
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, hs, he⟩ := hRS hr
    rw [← he, conjugationOperator_twice J hJ]
    exact hs
  · apply generatedVonNeumannAlgebra_le_of_le
    apply iSup_le
    intro n
    apply ((conjugateMatrixUnits J hJ (E n)).algebra_le_iff
      (conjugateRightAlgebra J hJ R).toStarSubalgebra).mpr
    intro i j
    exact ⟨(E n).entry i j,
      subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (E n).algebra) n)
        ((E n).entry_mem i j)), rfl⟩

/-- Small gaps on both sides transfer the two relative irreducibility
statements. Together with the common left/right vector action this proves
cyclicity and separation in the actual neighboring representation. -/
theorem preparedRight_cyclic_separating_of_matrix_gaps
    (M N R : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hJM : conjugateRightAlgebra J hJ M = M.commutant)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hSN : conjugateRightAlgebra J hJ R ≤ N.commutant)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2)
    (hgap' : kkDistance M.commutant N.commutant < 1 / 2)
    (Ω : H) (hΩ : Ω ≠ 0)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) ∧
      (∀ a : Algebra N, a.val Ω = 0 → a = 0) ∧
      (∀ a : Algebra N.commutant, a.val Ω = 0 → a = 0) := by
  have hEM (n : ℕ) : (E n).algebra ≤ M.toStarSubalgebra := by
    intro x hx
    apply hRM
    rw [hR]
    exact subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (E n).algebra) n) hx)
  have hirrN : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
    simpa only [← hR] using relative_irreducibility_of_near_increasing_matrices
      M N d E hmono hEM (by simpa only [← hR] using hirr) hgap
  let F := fun n => conjugateMatrixUnits J hJ (E n)
  have hS : conjugateRightAlgebra J hJ R =
      generatedVonNeumannAlgebra (⨆ n, (F n).algebra) := by
    rw [hR]
    exact conjugateRightAlgebra_generated_matrixStages J hJ d E
  have hSM : conjugateRightAlgebra J hJ R ≤ M.commutant := by
    rw [← hJM]
    exact conjugateRightAlgebra_mono J hJ hRM
  have hFM (n : ℕ) : (F n).algebra ≤ M.commutant.toStarSubalgebra := by
    intro x hx
    apply hSM
    rw [hS]
    exact subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (F n).algebra) n) hx)
  have hirrS := relative_irreducibility_commutant_of_conjugation J hJ R M hJM hirr
  have hirrN' : ∀ T ∈ N.commutant,
      (∀ r ∈ conjugateRightAlgebra J hJ R, r * T = T * r) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
    simpa only [← hS] using relative_irreducibility_of_near_increasing_matrices
      M.commutant N.commutant d F (conjugateMatrixUnits_mono J hJ d E hmono)
      hFM (by simpa only [← hS] using hirrS) hgap'
  exact cyclic_separating_of_commonRight_irreducibility J hJ R N hRN hSN Ω hΩ
    hirrN hirrN' hvector

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedCentralizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A finite expected subfactor gives a centralizing functional

The trace in this construction is only on the finite subfactor. Composing
it with a bimodular conditional expectation gives a functional on the
ambient algebra which centralizes that subfactor. No traciality of the
ambient algebra is asserted or used.
-/

namespace KadisonKastler

noncomputable section

section Abstract

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem expectedTrace_one (τ : FaithfulTracialState A) (E : B →L[ℂ] A)
    (hE : E 1 = 1) : expectedTrace τ E 1 = 1 := by
  rw [expectedTrace_apply, hE, τ.map_one]

/-- Bimodularity and the finite trace imply the centralizer identity. -/
theorem expectedTrace_centralizes (τ : FaithfulTracialState A) (E : B →L[ℂ] A)
    (ι : A →⋆ₐ[ℂ] B)
    (hleft : ∀ a x, E (ι a * x) = a * E x)
    (hright : ∀ a x, E (x * ι a) = E x * a) (a : A) (x : B) :
    expectedTrace τ E (ι a * x) = expectedTrace τ E (x * ι a) := by
  rw [expectedTrace_apply, expectedTrace_apply, hleft, hright]
  exact τ.tracial a (E x)

end Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- When the composed state is represented by a vector, its centralizer
identity is exactly the identity required by the matrix-state argument. -/
theorem vector_functional_centralizes_of_expectation
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (E : Algebra M →L[ℂ] Algebra R)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      E (StarSubalgebra.inclusion hRM r * x) = r * E x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      E (x * StarSubalgebra.inclusion hRM r) = E x * r)
    (Ω : H)
    (hΩ : ∀ x : Algebra M, expectedTrace τ E x = inner ℂ Ω (x.val Ω))
    (r : Algebra R) (x : Algebra M) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  have he := expectedTrace_centralizes τ E (StarSubalgebra.inclusion hRM)
    hleft hright r x
  rw [hΩ, hΩ] at he
  exact he

/-- A normalized expectation and a representing vector force unit norm. -/
theorem norm_vector_of_expectedTrace
    (M R : VonNeumannAlgebra H) (τ : FaithfulTracialState (Algebra R))
    (E : Algebra M →L[ℂ] Algebra R) (hE : E 1 = 1) (Ω : H)
    (hΩ : ∀ x : Algebra M, expectedTrace τ E x = inner ℂ Ω (x.val Ω)) :
    ‖Ω‖ = 1 := by
  have he : inner ℂ Ω Ω = 1 := by
    simpa only [OneMemClass.coe_one, one_apply_eq_self] using
      (hΩ 1).symm.trans (expectedTrace_one τ E hE)
  have hs : ‖Ω‖ ^ 2 = 1 := by
    have hr := congrArg Complex.re he
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) Ω]
    exact hr
  nlinarith [norm_nonneg Ω]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularConjugationData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular conjugation data used in preparing a pair

For a cyclic separating vector, Tomita--Takesaki gives `J M J = M′`.
The vector identity `J(r* Ω) = r Ω` is needed only for elements in the
vector-state centralizer. It is not imposed on the whole algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ModularConjugationData

variable {M R : VonNeumannAlgebra H} {Ω : H} (d : ModularConjugationData M Ω)

/-- Only centralization of the vector state on the common subalgebra is
needed for the right-vector identity in graph comparison. -/
theorem common_vector (hRM : R ≤ M)
    (hcentral : ∀ r : Algebra R, ∀ x : Algebra M,
      inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω))
    (r : Algebra R) :
    conjugationOperator d.conjugation (star r.val) Ω = r.val Ω :=
  d.centralizer_vector ⟨r.val, hRM r.property⟩ (hcentral r)

end ModularConjugationData

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedModularPreparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Modular preparation from an expected finite subalgebra

The trace used here is only on the finite subalgebra. Its composition with
an actual bimodular expectation is represented by the supplied vector.
The modular conjugation data then give precisely the common right-vector
identity used by matrix averaging and graph comparison. The corrected
neighbor is proved cyclic and separating when the two ordinary gaps are
small; these properties are not supplied as preparation assumptions.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ModularConjugationData

variable {M R : VonNeumannAlgebra H} {Ω : H}

/-- Bimodularity of an expectation onto a finite algebra supplies the
centralizer hypothesis required by modular conjugation. -/
theorem common_vector_of_expectation
    (d : ModularConjugationData M Ω) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (r : Algebra R) :
    conjugationOperator d.conjugation (star r.val) Ω = r.val Ω :=
  d.common_vector hRM
    (vector_functional_centralizes_of_expectation M R hRM τ P hleft hright Ω hΩ) r

/-- The expected-state vector has unit norm, and its common right action
has the exact membership and vector identities needed in preparation. -/
theorem expected_right_data
    (d : ModularConjugationData M Ω) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R) (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω)) :
    ‖Ω‖ = 1 ∧
      (∀ r ∈ R, conjugationOperator d.conjugation r ∈ M.commutant) ∧
      (∀ r ∈ R, conjugationOperator d.conjugation (star r) Ω = r Ω) := by
  refine ⟨norm_vector_of_expectedTrace M R τ P hP Ω hΩ, ?_, ?_⟩
  · intro r hr
    exact d.right_mem hRM ⟨r, hr⟩
  · intro r hr
    exact d.common_vector_of_expectation hRM τ P hleft hright hΩ ⟨r, hr⟩

end ModularConjugationData

/-- Conjugation transports the actual commutant, so the same elementary
movement bound applies to the second gap in preparation. -/
theorem unitaryConjugateAlgebra_commutant
    (w : unitary (H →L[ℂ] H)) (N : VonNeumannAlgebra H) :
    (unitaryConjugateAlgebra w N).commutant =
      unitaryConjugateAlgebra w N.commutant := by
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w
  apply SetLike.coe_injective
  rw [VonNeumannAlgebra.coe_commutant]
  change Set.centralizer (e '' (N : Set (H →L[ℂ] H))) =
    e '' (N.commutant : Set (H →L[ℂ] H))
  rw [VonNeumannAlgebra.coe_commutant]
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    rw [map_mul, map_mul]
    change e y * e (e.symm x) = e (e.symm x) * e y
    rw [e.apply_symm_apply]
    exact hx (e y) ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩ z ⟨v, hv, rfl⟩
    simpa only [map_mul] using congrArg e (hy v hv)

theorem preparedPair_second_correction_commutant_gap
    (M N : VonNeumannAlgebra H) (w : unitary (H →L[ℂ] H)) :
    kkDistance M.commutant (unitaryConjugateAlgebra (star w) N).commutant ≤
      kkDistance M.commutant N.commutant + 2 * ‖(w : H →L[ℂ] H) - 1‖ := by
  rw [unitaryConjugateAlgebra_commutant]
  exact preparedPair_second_correction_gap M.commutant N.commutant w

local instance expectedModularOrder_rfb7848_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance expectedModularStarOrder_rfb7848_1 (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
local instance expectedModularOperatorOrder_rfb7848_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance expectedModularOperatorStarOrder_rfb7848_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- The same expected vector is cyclic and separating for the corrected
neighbor. Smallness of the commutant gap is stated independently of the
left gap and transported through the actual chosen correction. -/
theorem expected_modular_corrected_cyclic_separating_oai
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R) (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (d : ModularConjugationData M Ω)
    (s : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (w : unitary (H →L[ℂ] H))
    (hRN : R ≤ unitaryConjugateAlgebra (star w) N)
    (hSN : conjugateRightAlgebra d.conjugation d.involutive R ≤
      (unitaryConjugateAlgebra (star w) N).commutant)
    (hgap : kkDistance M N + 2 * ‖(w : H →L[ℂ] H) - 1‖ < 1 / 2)
    (hgap' : kkDistance M.commutant N.commutant +
      2 * ‖(w : H →L[ℂ] H) - 1‖ < 1 / 2) :
    DenseRange (algebraVectorMap (unitaryConjugateAlgebra (star w) N) Ω) ∧
      Function.Injective (algebraVectorMap (unitaryConjugateAlgebra (star w) N) Ω) ∧
      DenseRange (algebraVectorMap (unitaryConjugateAlgebra (star w) N).commutant Ω) ∧
      Function.Injective (algebraVectorMap (unitaryConjugateAlgebra (star w) N).commutant Ω) := by
  obtain ⟨hnorm, _, hvector⟩ := d.expected_right_data hRM τ P hP hleft hright hΩ
  have hΩ0 : Ω ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨hc, hc', hs, hs'⟩ := preparedRight_cyclic_separating_of_matrix_gaps
    M (unitaryConjugateAlgebra (star w) N) R d.conjugation d.involutive d.commutant
    s E hmono hR hRM hRN hSN hirr
    ((preparedPair_second_correction_gap M N w).trans_lt hgap)
    ((preparedPair_second_correction_commutant_gap M N w).trans_lt hgap') Ω hΩ0 hvector
  refine ⟨hc, ?_, hc', ?_⟩
  · intro x y hxy
    have hz : (x - y).val Ω = 0 := by
      change (algebraVectorMap (unitaryConjugateAlgebra (star w) N) Ω) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hs (x - y) hz)
  · intro x y hxy
    have hz : (x - y).val Ω = 0 := by
      change (algebraVectorMap (unitaryConjugateAlgebra (star w) N).commutant Ω) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hs' (x - y) hz)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.expected_modular_corrected_cyclic_separating_oai.{u_1} := @OAI.KadisonKastler.expected_modular_corrected_cyclic_separating_oai.{u_1}
