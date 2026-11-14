-- Prove2me | solution 1 for OAI.KadisonKastler.exists_commonPositionData_of_matrix_cyclic_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:08:51.918177+00:00
-- url     : https://prove2.me/submissions/b3bb5aa3-c05d-4366-b0db-33631be30a34

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Spectrum
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
import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.LinearAlgebra.Complex.Module
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
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
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
import Definitions.Def_Q260K032
import Definitions.Def_Q260K071
import Theorems.Thm_OAI_Generator_Tracial_traceFreeHilbertClosureTrace_copy
import Theorems.Thm_OAI_KadisonKastler_conjugated_representation_comparison
import Theorems.Thm_OAI_KadisonKastler_exists_matrix_right_alignment
import Theorems.Thm_OAI_KadisonKastler_nearInclusion_of_representation_comparison
import Theorems.Thm_OAI_KadisonKastler_relative_irreducibility_of_near_increasing_matrices
import Theorems.Thm_OAI_KadisonKastler_reverse_nearInclusion_of_representation_comparison
import Theorems.Thm_OAI_KadisonKastler_unitaryConjugateAlgebra_isII1
import Theorems.Thm_OAI_KadisonKastler_vector_state_eq_trace_of_relative_central

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common right actions in a cyclic representation

Two operators in the same commutant are equal if they agree on the cyclic
vector. Equality of the right actions obtained this way makes the product
of the two tracial conjugations commute with both module actions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- A common left multiplier has the same right-action value on the
common standard vector, before equality of the right operators is known. -/
theorem conjugationOperator_common_vector
    (M N : VonNeumannAlgebra H) (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ x : Algebra N, J₂ (x.val Ω) = (star x).val Ω)
    (a : H →L[ℂ] H) (haM : a ∈ M) (haN : a ∈ N) :
    conjugationOperator J₁ a Ω = conjugationOperator J₂ a Ω := by
  have h₁ : J₁ Ω = Ω := by
    simpa only [star_one, OneMemClass.coe_one, one_apply_eq_self] using hM 1
  have h₂ : J₂ Ω = Ω := by
    simpa only [star_one, OneMemClass.coe_one, one_apply_eq_self] using hN 1
  change J₁ (a (J₁ Ω)) = J₂ (a (J₂ Ω))
  rw [h₁, h₂]
  exact (hM ⟨a, haM⟩).trans (hN ⟨a, haN⟩).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRightProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The source's central-vector identity supplies both vector
correspondences when the right algebra is the conjugate of the left one. -/
theorem preparedPair_cyclic_separating_of_conjugate_algebra
    (N : VonNeumannAlgebra H)
    (R S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (hSN : S ≤ N.commutant.toStarSubalgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hS : (S : Set (H →L[ℂ] H)) = conjugationOperator J '' (R : Set (H →L[ℂ] H)))
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirrR : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrS : ∀ T ∈ N.commutant, (∀ s ∈ S, s * T = T * s) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ r ∈ R, r Ω = conjugationOperator J (star r) Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) ∧
      (∀ a : Algebra N, a.val Ω = 0 → a = 0) ∧
      (∀ a : Algebra N.commutant, a.val Ω = 0 → a = 0) := by
  apply preparedPair_cyclic_separating N R S hRN hSN Ω hΩ hirrR hirrS
  · intro r hr
    refine ⟨conjugationOperator J (star r), ?_, hcentral r hr⟩
    change conjugationOperator J (star r) ∈ (S : Set (H →L[ℂ] H))
    rw [hS]
    exact ⟨star r, R.star_mem' hr, rfl⟩
  · intro s hs
    change s ∈ (S : Set (H →L[ℂ] H)) at hs
    rw [hS] at hs
    obtain ⟨r, hr, rfl⟩ := hs
    refine ⟨star r, R.star_mem' hr, ?_⟩
    simpa only [star_star] using (hcentral (star r) (R.star_mem' hr)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Normalizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Unitaries in the commutant act trivially on the algebra by conjugation. -/
theorem unitaryConj_eq_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant)
    {x : H →L[ℂ] H} (hx : x ∈ P) : unitaryConj b x = x := by
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb x hx
  rw [unitaryConj, ← hcomm, mul_assoc,
    Unitary.mul_star_self_of_mem b.property, mul_one]

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedPairCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_IrreducibleTracialState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative centrality determines the vector trace of a finite factor -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commuting right representatives of the common algebra make the
vector state central over that algebra. -/
theorem vector_state_central_of_commuting_right_representatives
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (ξ : H)
    (hright : ∀ r : Algebra R, ∃ b : H →L[ℂ] H,
      b ∈ M.commutant ∧ b ξ = r.val ξ ∧ star b ξ = star r.val ξ)
    (r : Algebra R) (a : Algebra M) :
    inner ℂ ξ ((coordinateInclusion hRM r * a).val ξ) =
      inner ℂ ξ ((a * coordinateInclusion hRM r).val ξ) := by
  obtain ⟨b, hb, hbr, hbstar⟩ := hright r
  have hcomm : a.val * b = b * a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp hb a.val a.property
  change inner ℂ ξ (r.val (a.val ξ)) = inner ℂ ξ (a.val (r.val ξ))
  calc
    inner ℂ ξ (r.val (a.val ξ)) = inner ℂ (star r.val ξ) (a.val ξ) := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.adjoint_inner_left r.val (a.val ξ) ξ).symm
    _ = inner ℂ (star b ξ) (a.val ξ) := by rw [hbstar]
    _ = inner ℂ ξ (b (a.val ξ)) := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using
        ContinuousLinearMap.adjoint_inner_left b (a.val ξ) ξ
    _ = inner ℂ ξ (a.val (b ξ)) := by
      have he := congrArg (fun T : H →L[ℂ] H => T ξ) hcomm
      exact congrArg (fun v : H => inner ℂ ξ v) he.symm
    _ = inner ℂ ξ (a.val (r.val ξ)) := by rw [hbr]

theorem ii1_vector_state_eq_trace_of_relative_central
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hirr : ∀ a : Algebra M, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcentral : ∀ (r : Algebra R) (a : Algebra M),
      inner ℂ ξ ((coordinateInclusion hRM r * a).val ξ) =
      inner ℂ ξ ((a * coordinateInclusion hRM r).val ξ))
    (x : Algebra M) : inner ℂ ξ (x.val ξ) = (concreteFactorTrace hM).toLinearMap x := by
  let hf := traceHilbert_factor hM
  let hu := traceHilbert_nonzero hM
  let P := traceFreeHilbertClosure hf hM.diffuse hM.finite hu
  let e := traceFreeHilbertEquiv hf hM.diffuse hM.finite hu
  let τ : TracialRepresentation P := traceFreeHilbertClosureTrace hf hM.diffuse hM.finite hu
  calc
    inner ℂ ξ (x.val ξ) = τ.trace (e x) :=
      vector_state_eq_trace_of_relative_central M R hRM P e τ
        (traceFreeHilbertBallMap_continuous hf hM.diffuse hM.finite hu)
        hirr ξ hξ hcentral x
    _ = (concreteFactorTrace hM).toLinearMap x :=
      traceFreeHilbertClosureTrace_copy hf hM.diffuse hM.finite hu x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SharedTracialRightAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A shared tracial right action determines the neighboring vector state -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem StandardTracialPosition.common_right_representatives
    {M N R : VonNeumannAlgebra H} (p : StandardTracialPosition M) (hRM : R ≤ M)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (r : Algebra R) :
    ∃ b : H →L[ℂ] H, b ∈ N.commutant ∧ b p.vector = r.val p.vector ∧
      star b p.vector = star r.val p.vector := by
  let b := conjugationOperator p.conjugation (star r.val)
  have hb : b ∈ N.commutant := hright
    ⟨star r.val, R.toStarSubalgebra.star_mem' r.property, rfl⟩
  refine ⟨b, hb, ?_, ?_⟩
  · change p.conjugation (star r.val (p.conjugation p.vector)) = r.val p.vector
    rw [p.conjugation_vector]
    have he := p.conjugation_algebraVector (star (coordinateInclusion hRM r))
    change p.conjugation (star r.val p.vector) = star (star r.val) p.vector at he
    simpa only [star_star] using he
  · change star (conjugationOperator p.conjugation (star r.val)) p.vector = _
    rw [← conjugationOperator_star p.conjugation p.conjugation_involutive, star_star]
    change p.conjugation (r.val (p.conjugation p.vector)) = star r.val p.vector
    rw [p.conjugation_vector]
    exact p.conjugation_algebraVector (coordinateInclusion hRM r)

/-- Once the right action is aligned, the same unit vector implements
the neighboring factor's trace. -/
theorem StandardTracialPosition.neighbor_trace
    {M N R : VonNeumannAlgebra H} (p : StandardTracialPosition M)
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hirr : ∀ a : Algebra N, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (x : Algebra N) :
    inner ℂ p.vector (x.val p.vector) = (concreteFactorTrace hN).toLinearMap x :=
  ii1_vector_state_eq_trace_of_relative_central N R hRN hN hirr
    p.vector p.vector_norm
    (vector_state_central_of_commuting_right_representatives N R hRN p.vector
      (p.common_right_representatives hRM hright)) x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SharedStandardTracialPosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructing the neighboring standard trace from common module actions -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_neighbor_standardTracialPosition
    {M N R : VonNeumannAlgebra H} (p : StandardTracialPosition M)
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (hirr : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrRight : ∀ T ∈ N.commutant,
      (∀ r ∈ conjugateRightAlgebra p.conjugation p.conjugation_involutive R,
        r * T = T * r) → ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) :
    ∃ q : StandardTracialPosition N, q.vector = p.vector := by
  let S := conjugateRightAlgebra p.conjugation p.conjugation_involutive R
  have hn : p.vector ≠ 0 := by
    intro h
    have he := p.vector_norm
    rw [h, norm_zero] at he
    exact zero_ne_one he
  have hc (r : H →L[ℂ] H) (hr : r ∈ R.toStarSubalgebra) :
      r p.vector = conjugationOperator p.conjugation (star r) p.vector := by
    change r p.vector = p.conjugation (star r (p.conjugation p.vector))
    rw [p.conjugation_vector]
    have he := p.conjugation_algebraVector (star (⟨r, hRM hr⟩ : Algebra M))
    change p.conjugation (star r p.vector) = star (star r) p.vector at he
    simpa only [star_star] using he.symm
  obtain ⟨hcyclic, _, _, _⟩ := preparedPair_cyclic_separating_of_conjugate_algebra
    N R.toStarSubalgebra S.toStarSubalgebra hRN hright p.conjugation
    (conjugateRightAlgebra_coe p.conjugation p.conjugation_involutive R)
    p.vector hn hirr hirrRight hc
  have hi (a : Algebra N) (ha : a.val ∈ R.commutant) : ∃ c : ℂ, a = c • 1 := by
    obtain ⟨c, hc⟩ := hirr a.val a.property
      (fun r hr => VonNeumannAlgebra.mem_commutant_iff.mp ha r hr)
    exact ⟨c, Subtype.ext hc⟩
  refine ⟨{ trace := concreteFactorTrace hN
            vector := p.vector
            trace_eq := fun x => (p.neighbor_trace hRM hRN hN hi hright x).symm
            cyclic := hcyclic }, rfl⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SharedConjugationBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tracial conjugation comparison from the constructed common right action -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N R : VonNeumannAlgebra H}

theorem StandardTracialPosition.right_action_eq
    (p : StandardTracialPosition M) (q : StandardTracialPosition N)
    (hsame : p.vector = q.vector) (hRM : R ≤ M) (hRN : R ≤ N)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (r : H →L[ℂ] H) (hr : r ∈ R) :
    conjugationOperator p.conjugation r = conjugationOperator q.conjugation r := by
  have hcyclic : DenseRange (fun x : Algebra N => x.val p.vector) := by
    rw [hsame]
    exact q.cyclic
  have hq : ∀ x : Algebra N, q.conjugation (x.val p.vector) = (star x).val p.vector := by
    rw [hsame]
    exact q.conjugation_algebraVector
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector N p.vector hcyclic
  · exact hright ⟨r, hr, rfl⟩
  · exact conjugationOperator_mem_commutant N q.conjugation p.vector hq hcyclic ⟨r, hRN hr⟩
  · exact conjugationOperator_common_vector M N p.conjugation q.conjugation p.vector
      p.conjugation_algebraVector hq r (hRM hr) (hRN hr)


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StandardTracialCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant in the constructed standard tracial position -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem StandardTracialPosition.conjugation_commutant_vector
    (p : StandardTracialPosition M) (r : Algebra M.commutant) :
    p.conjugation (r.val p.vector) = star r.val p.vector := by
  apply ext_inner_left ℂ
  intro ξ
  apply p.cyclic.induction_on (p := fun ξ =>
    inner ℂ ξ (p.conjugation (r.val p.vector)) = inner ℂ ξ (star r.val p.vector)) ξ
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro a
    have hCa : p.conjugation (star a.val p.vector) = a.val p.vector := by
      simpa only [StarMemClass.coe_star, star_star] using p.conjugation_algebraVector (star a)
    have hc := congrArg (fun T : H →L[ℂ] H => T p.vector)
      (VonNeumannAlgebra.mem_commutant_iff.mp r.property a.val a.property)
    change a.val (r.val p.vector) = r.val (a.val p.vector) at hc
    calc
      inner ℂ (a.val p.vector) (p.conjugation (r.val p.vector)) =
          inner ℂ (p.conjugation (star a.val p.vector)) (p.conjugation (r.val p.vector)) := by rw [hCa]
      _ = star (inner ℂ (star a.val p.vector) (r.val p.vector)) :=
        conjugateIsometry_inner p.conjugation _ _
      _ = inner ℂ (r.val p.vector) (star a.val p.vector) := inner_conj_symm _ _
      _ = inner ℂ (a.val (r.val p.vector)) p.vector :=
        ContinuousLinearMap.adjoint_inner_right a.val _ p.vector
      _ = inner ℂ (r.val (a.val p.vector)) p.vector := by rw [hc]
      _ = inner ℂ (a.val p.vector) (star r.val p.vector) :=
        (ContinuousLinearMap.adjoint_inner_right r.val _ p.vector).symm

theorem StandardTracialPosition.conjugate_algebra_eq_commutant
    (p : StandardTracialPosition M) :
    conjugateRightAlgebra p.conjugation p.conjugation_involutive M = M.commutant := by
  have hcyc : DenseRange (algebraVectorMap M.commutant p.vector) :=
    Generator.commutant_orbit_dense M p.vector (fun a ha => p.separating ha)
  apply le_antisymm
  · rintro T ⟨a, ha, rfl⟩
    exact conjugationOperator_mem_commutant M p.conjugation p.vector
      p.conjugation_algebraVector p.cyclic ⟨a, ha⟩
  · intro T hT
    have hM := conjugationOperator_mem_commutant M.commutant p.conjugation p.vector
      p.conjugation_commutant_vector hcyc ⟨T, hT⟩
    rw [VonNeumannAlgebra.commutant_commutant] at hM
    exact ⟨conjugationOperator p.conjugation T, hM,
      conjugationOperator_twice _ p.conjugation_involutive T⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialOrbitClosed
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded tracial vectors in a subalgebra orbit closure

The constructed conditional expectation shows that a bounded algebra
element whose trace vector belongs to the subalgebra's closed orbit
already belongs to that subalgebra.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M R : VonNeumannAlgebra H}

theorem mem_subalgebra_of_tracial_vector_mem_orbitClosure
    (τ : TracialRepresentation M) (hRM : R ≤ M) (a : M.toStarSubalgebra)
    (ha : a.val τ.vector ∈ vectorOrbitClosure R.toStarSubalgebra τ.vector) :
    a.val ∈ R := by
  let c := conditionalExpectation τ hRM a
  have hc : c.val ∈ R := conditionalExpectation_mem τ hRM a
  let ξ := (a - c).val τ.vector
  have hξ : ξ ∈ vectorOrbitClosure R.toStarSubalgebra τ.vector := by
    change a.val τ.vector - c.val τ.vector ∈ _
    exact (vectorOrbitClosure R.toStarSubalgebra τ.vector).sub_mem ha
      (Submodule.le_topologicalClosure _ ⟨⟨c.val, hc⟩, rfl⟩)
  have ho (r : R.toStarSubalgebra) : inner ℂ (r.val τ.vector) ξ = 0 := by
    have ht := conditionalExpectation_orthogonal τ hRM a
      ⟨star (coordinateInclusion hRM r), star_mem r.property⟩
    change inner ℂ τ.vector ((star r.val * (a - c).val) τ.vector) = 0 at ht
    simpa only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right] using ht
  have hz : inner ℂ ξ ξ = 0 := by
    have hclosed : IsClosed {x : H | inner ℂ x ξ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hs : closure (Set.range (fun r : R.toStarSubalgebra => r.val τ.vector)) ⊆
        {x : H | inner ℂ x ξ = 0} :=
      closure_minimal (by rintro _ ⟨r, rfl⟩; exact ho r) hclosed
    exact hs hξ
  have hzero : ξ = 0 := inner_self_eq_zero.mp hz
  have hac : a = c := sub_eq_zero.mp (τ.separating (a - c) hzero)
  simpa only [hac] using hc

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialBasicConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant of the tracial basic construction -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M R : VonNeumannAlgebra H}

theorem StandardTracialPosition.right_commutes_orbitProjection
    (p : StandardTracialPosition M) (hRM : R ≤ M) (r : Algebra R) :
    (vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection *
        conjugationOperator p.conjugation r.val =
      conjugationOperator p.conjugation r.val *
        (vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection := by
  have hinv (a : Algebra R) : ∀ x ∈ vectorOrbitClosure R.toStarSubalgebra p.vector,
      conjugationOperator p.conjugation a.val x ∈ vectorOrbitClosure R.toStarSubalgebra p.vector := by
    apply vectorOrbitClosure_invariant_of_orbit
    intro b
    exact ⟨b * star a, conjugationOperator_algebraVector M p.conjugation p.vector
      p.conjugation_algebraVector (coordinateInclusion hRM a) (coordinateInclusion hRM b)⟩
  apply starProjection_commutes_of_invariant
  · exact hinv r
  · rw [← conjugationOperator_star p.conjugation p.conjugation_involutive]
    exact hinv (star r)

theorem StandardTracialPosition.basicConstruction_commutant
    (p : StandardTracialPosition M) (hRM : R ≤ M) :
    Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
      {(vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection}) =
      (conjugateRightAlgebra p.conjugation p.conjugation_involutive R : Set (H →L[ℂ] H)) := by
  ext T
  constructor
  · intro hT
    have hTM : T ∈ M.commutant := VonNeumannAlgebra.mem_commutant_iff.mpr
      (fun a ha => hT a (Or.inl ha))
    rw [← p.conjugate_algebra_eq_commutant] at hTM
    obtain ⟨a, ha, he⟩ := hTM
    have hv := congrArg (fun S : H →L[ℂ] H => S p.vector)
      (hT _ (Or.inr (Set.mem_singleton _)))
    change (vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection (T p.vector) =
      T ((vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection p.vector) at hv
    rw [Submodule.starProjection_eq_self_iff.mpr (mem_vectorOrbitClosure _ _)] at hv
    have hTv : T p.vector ∈ vectorOrbitClosure R.toStarSubalgebra p.vector :=
      Submodule.starProjection_eq_self_iff.mp hv
    have hvec : T p.vector = star a p.vector := by
      rw [← he]
      change p.conjugation (a (p.conjugation p.vector)) = _
      rw [p.conjugation_vector]
      exact p.conjugation_algebraVector ⟨a, ha⟩
    have haR : star a ∈ R := mem_subalgebra_of_tracial_vector_mem_orbitClosure
      p.toTracialRepresentation hRM (star (⟨a, ha⟩ : Algebra M)) (by
        change star a p.vector ∈ _
        rwa [hvec] at hTv)
    have haR' : a ∈ R := by
      have h : star (star a) ∈ R := R.toStarSubalgebra.star_mem' haR
      rw [star_star] at h
      exact h
    exact ⟨a, haR', he⟩
  · rintro ⟨a, ha, rfl⟩ x hx
    rcases hx with hx | hx
    · exact VonNeumannAlgebra.mem_commutant_iff.mp
        (conjugationOperator_mem_commutant M p.conjugation p.vector
          p.conjugation_algebraVector p.cyclic ⟨a, hRM ha⟩) x hx
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact p.right_commutes_orbitProjection hRM ⟨a, ha⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonBasicConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equality of the basic constructions from a shared right action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N R : VonNeumannAlgebra H}

theorem StandardTracialPosition.common_basicConstruction
    (p : StandardTracialPosition M) (q : StandardTracialPosition N)
    (hsame : p.vector = q.vector) (hRM : R ≤ M) (hRN : R ≤ N)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant) :
    Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
      {(Generator.vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection})) =
    Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
      {(Generator.vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection})) := by
  have hrightEq : conjugateRightAlgebra p.conjugation p.conjugation_involutive R =
      conjugateRightAlgebra q.conjugation q.conjugation_involutive R := by
    ext T
    constructor
    · rintro ⟨r, hr, he⟩
      exact ⟨r, hr, (p.right_action_eq q hsame hRM hRN hright r hr).symm.trans he⟩
    · rintro ⟨r, hr, he⟩
      exact ⟨r, hr, (p.right_action_eq q hsame hRM hRN hright r hr).trans he⟩
  have hN : Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
      {(Generator.vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection}) =
      (conjugateRightAlgebra q.conjugation q.conjugation_involutive R : Set (H →L[ℂ] H)) := by
    rw [hsame]
    exact q.basicConstruction_commutant hRN
  rw [p.basicConstruction_commutant hRM, hN, hrightEq]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonPositionConstants
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Numerical bounds for the constructed common tracial position -/

namespace KadisonKastler

theorem commonPosition_tolerance_lt {γ : ℝ} (hγ : 0 < γ)
    (hsmall : γ < 174 / 1000000000000000) :
    69000000000 * γ < 50948 * Real.sqrt γ := by
  have hs := Real.sq_sqrt hγ.le
  have hr := Real.sqrt_nonneg γ
  have hs' : Real.sqrt γ < 1 / 2000000 := by nlinarith
  have hc : 69000000000 * Real.sqrt γ < 50948 := by linarith
  have h := mul_lt_mul_of_pos_right hc (Real.sqrt_pos.mpr hγ)
  nlinarith

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateRightIrreducibility
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedModularPreparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearInclusionDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalizing strict near-inclusion approximants -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- An algebra approximant can be normalized into its unit ball with at
most twice the original error. -/
theorem exists_unitBall_approx_of_algebra_approx
    {x y : H →L[ℂ] H} (hx : ‖x‖ ≤ 1) (hy : y ∈ N) :
    ∃ z ∈ unitBall N, ‖x - z‖ ≤ 2 * ‖x - y‖ := by
  by_cases hy1 : ‖y‖ ≤ 1
  · exact ⟨y, ⟨hy, hy1⟩, by nlinarith [norm_nonneg (x - y)]⟩
  have hypos : 0 < ‖y‖ := by linarith
  let z : H →L[ℂ] H := (‖y‖⁻¹ : ℂ) • y
  have hznorm : ‖z‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hypos)
  have hyz : ‖y - z‖ = ‖y‖ - 1 := by
    have hi : 0 ≤ 1 - ‖y‖⁻¹ := by
      have ht : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hypos).mpr (lt_of_not_ge hy1).le
      linarith
    have he : y - z = ((1 - ‖y‖⁻¹ : ℝ) : ℂ) • y := by
      simp only [z, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
        sub_smul, one_smul]
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hypos.ne']
  have hnorm : ‖y‖ - 1 ≤ ‖x - y‖ := by
    have ht := norm_add_le (y - x) x
    rw [sub_add_cancel, norm_sub_rev] at ht
    linarith
  refine ⟨z, ⟨N.toStarSubalgebra.smul_mem hy _, hznorm.le⟩, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub x y z).trans (by rw [hyz]; linarith)

/-- The published strict near-inclusion convention controls the closed
unit balls with the factor two from normalization. -/
theorem exists_unitBall_approx_of_nearInclusion {γ : ℝ}
    (h : NearInclusion M N γ) {x : H →L[ℂ] H} (hx : x ∈ unitBall M) :
    ∃ y ∈ unitBall N, ‖x - y‖ < 2 * γ := by
  obtain ⟨γ', hγ', happrox⟩ := h
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff ⟨0, zero_mem N⟩).mp
    ((happrox x hx).trans_lt hγ')
  obtain ⟨z, hz, hxz⟩ := exists_unitBall_approx_of_algebra_approx hx.2 hy
  have hxy' : ‖x - y‖ < γ := by simpa only [dist_eq_norm] using hxy
  exact ⟨z, hz, hxz.trans_lt (by linarith)⟩

theorem kkDistance_le_two_mul_of_nearInclusions {γ : ℝ} (hγ : 0 ≤ γ)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    kkDistance M N ≤ 2 * γ := by
  apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx_of_nearInclusion hMN hx
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy.le⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx_of_nearInclusion hNM hx
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy.le⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommonStandardPosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The standard tracial neighbor after the two matrix inclusions -/

namespace KadisonKastler

noncomputable section

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N R : VonNeumannAlgebra H}

theorem exists_matrix_common_standardPosition
    (p : StandardTracialPosition M) (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : IsII1Factor N.toStarSubalgebra)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (hgap : kkDistance M N < 1 / 2)
    (hgap' : kkDistance M.commutant N.commutant < 1 / 2) :
    ∃ q : StandardTracialPosition N, q.vector = p.vector ∧
      Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
        {(vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection})) =
      Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
        {(vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection})) := by
  have hEM (n : ℕ) : (E n).algebra ≤ M.toStarSubalgebra := by
    intro x hx
    apply hRM
    rw [hR]
    exact subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (E n).algebra) n) hx)
  have hi : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
    simpa only [← hR] using relative_irreducibility_of_near_increasing_matrices
      M N d E hmono hEM (by simpa only [← hR] using hirr) hgap
  let F := fun n => conjugateMatrixUnits p.conjugation p.conjugation_involutive (E n)
  have hS : conjugateRightAlgebra p.conjugation p.conjugation_involutive R =
      generatedVonNeumannAlgebra (⨆ n, (F n).algebra) := by
    rw [hR]
    exact conjugateRightAlgebra_generated_matrixStages _ _ d E
  have hSM : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ M.commutant := by
    rw [← p.conjugate_algebra_eq_commutant]
    exact conjugateRightAlgebra_mono _ _ hRM
  have hFM (n : ℕ) : (F n).algebra ≤ M.commutant.toStarSubalgebra := by
    intro x hx
    apply hSM
    rw [hS]
    exact subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (F n).algebra) n) hx)
  have hiS := relative_irreducibility_commutant_of_conjugation
    p.conjugation p.conjugation_involutive R M p.conjugate_algebra_eq_commutant hirr
  have hi' : ∀ T ∈ N.commutant,
      (∀ r ∈ conjugateRightAlgebra p.conjugation p.conjugation_involutive R,
        r * T = T * r) → ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
    simpa only [← hS] using relative_irreducibility_of_near_increasing_matrices
      M.commutant N.commutant d F (conjugateMatrixUnits_mono _ _ d E hmono)
      hFM (by simpa only [← hS] using hiS) hgap'
  obtain ⟨q, hq⟩ := exists_neighbor_standardTracialPosition p hRM hRN hN hright hi hi'
  exact ⟨q, hq, p.common_basicConstruction q hq.symm hRM hRN hright⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommonPositionData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common tracial position from the constructed matrix correction -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N R : VonNeumannAlgebra H} {L P C : VonNeumannAlgebra K}

theorem exists_commonPositionData_of_matrix_cyclic_neighbor_oai
    (hRM : R ≤ M) (hRN : R ≤ N) (hCL : C ≤ L) (hCP : C ≤ P)
    (eM : Algebra M ≃⋆ₐ[ℂ] Algebra L) (eN : Algebra N ≃⋆ₐ[ℂ] Algebra P)
    (eR : Algebra R ≃⋆ₐ[ℂ] Algebra C)
    (heM : ∀ r, eM (coordinateInclusion hRM r) = coordinateInclusion hCL (eR r))
    (heN : ∀ r, eN (coordinateInclusion hRN r) = coordinateInclusion hCP (eR r))
    (p : StandardTracialPosition L) (hP : IsII1Factor P.toStarSubalgebra)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (K →L[ℂ] K))
    (hmono : Monotone (fun n => (E n).algebra))
    (hC : C = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hirr : ∀ T ∈ L, (∀ r ∈ C, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : K →L[ℂ] K))
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 174 / 1000000000000000)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ)
    (hcomp : ∀ (a : Algebra M) (b : Algebra N), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖(eM a).val - (eN b).val‖ ≤ 400000000 * γ + ‖a.val - b.val‖)
    (hcommNear : NearInclusion L.commutant P.commutant (405000000 * γ))
    (hcommGap : kkDistance L.commutant P.commutant ≤ 810000000 * γ) :
    Nonempty (CommonTracialPositionData M N R hRM hRN γ K) := by
  let : Nontrivial K := nontrivial_of_ne p.vector 0 (by
    intro h
    have hn := p.vector_norm
    rw [h, norm_zero] at hn
    exact zero_ne_one hn)
  have hLP := nearInclusion_of_representation_comparison eM eN hγ hcomp hMN
  have hPL := reverse_nearInclusion_of_representation_comparison eM eN hγ hcomp hNM
  have hdist : kkDistance L P ≤ 2 * (400000000 * γ + 2 * γ) :=
    kkDistance_le_two_mul_of_nearInclusions (by positivity) hLP hPL
  obtain ⟨w, hwC, hCQ, hright, hwn⟩ := exists_matrix_right_alignment p hCL hCP d E
    hmono hC (by positivity : 0 ≤ 405000000 * γ) (by linarith) hcommNear
  let Q := unitaryConjugateAlgebra (star w) P
  have hw : ‖(w : K →L[ℂ] K) - 1‖ ≤ 34020000000 * γ := by linarith
  have hLQ : kkDistance L Q < 1 / 2 := by
    have h := preparedPair_second_correction_gap L P w
    change kkDistance L Q ≤ _ at h
    linarith
  have hLQ' : kkDistance L.commutant Q.commutant < 1 / 2 := by
    have h := preparedPair_second_correction_commutant_gap L P w
    change kkDistance L.commutant Q.commutant ≤ _ at h
    linarith
  have hQ : IsII1Factor Q.toStarSubalgebra := unitaryConjugateAlgebra_isII1 (star w) hP
  obtain ⟨q, hq, hbasic⟩ := exists_matrix_common_standardPosition p hCL hCQ hQ
    d E hmono hC hirr hright hLQ hLQ'
  let f := eN.trans (unitaryConjugateEquiv (star w) P)
  have hf : ∀ (a : Algebra M) (b : Algebra N), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖(eM a).val - (f b).val‖ ≤ 68440000000 * γ + ‖a.val - b.val‖ := by
    intro a b ha hb
    have h := conjugated_representation_comparison eM eN hcomp w hw a b ha hb
    change ‖(eM a).val - (f b).val‖ ≤ _ at h
    linarith
  have hnL : NearInclusion L Q (69000000000 * γ) := by
    obtain ⟨δ, hδ, happ⟩ := nearInclusion_of_representation_comparison eM f hγ hf hMN
    exact ⟨δ, by linarith, happ⟩
  have hnQ : NearInclusion Q L (69000000000 * γ) := by
    obtain ⟨δ, hδ, happ⟩ := reverse_nearInclusion_of_representation_comparison eM f hγ hf hNM
    exact ⟨δ, by linarith, happ⟩
  refine ⟨{
    left := L
    right := Q
    common := C
    common_le_left := hCL
    common_le_right := hCQ
    leftEquiv := eM
    rightEquiv := f
    commonEquiv := eR
    left_restrict := heM
    right_restrict := ?_
    leftPosition := p
    rightPosition := q
    same_vector := hq.symm
    tolerance := 69000000000 * γ
    tolerance_nonneg := by positivity
    tolerance_lt := commonPosition_tolerance_lt hγ hsmall
    near_left := hnL
    near_right := hnQ
    comparison := ?_
    same_basicConstruction := hbasic }⟩
  · intro r
    apply Subtype.ext
    change unitaryConj (star w) (eN (coordinateInclusion hRN r)).val = (eR r).val
    rw [heN]
    exact unitaryConj_eq_self_of_mem_commutant (star_mem hwC) (eR r).property
  · intro a b ha hb
    have h := hf a b ha hb
    linarith

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.exists_commonPositionData_of_matrix_cyclic_neighbor_oai.{u} := @OAI.KadisonKastler.exists_commonPositionData_of_matrix_cyclic_neighbor_oai.{u}
