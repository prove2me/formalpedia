-- Prove2me | solution 1 for OAI.KadisonKastler.exists_selfAdjoint_split_of_factor_commutant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:57:48.913557+00:00
-- url     : https://prove2.me/submissions/41f3367a-9d8e-48a6-bf91-3720fe907d6f

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Set
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K071
import Theorems.Thm_OAI_KadisonKastler_CuntzFamily_upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability
import Theorems.Thm_OAI_KadisonKastler_TypeIIIFactor_exists_projection_coordinates_of_projection_countability
import Theorems.Thm_OAI_KadisonKastler_exists_selfAdjoint_split_of_finite_commutant_corner
import Theorems.Thm_OAI_KadisonKastler_mem_commutant_of_commutes_projections

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

theorem unitaryConj_sub (v : unitary (H →L[ℂ] H)) (x y : H →L[ℂ] H) :
    unitaryConj v (x - y) = unitaryConj v x - unitaryConj v y := by
  simp [unitaryConj, mul_sub, sub_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianDerivationAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Abelian averaging of a spatial derivation implementer

A spatial derivation preserving a von Neumann algebra also preserves its
commutant. Averaging over any commuting unitary subgroup of the commutant
keeps the same derivation, preserves the norm bound, and makes the
implementer commute with that subgroup. This is the abelian averaging
step in the spatial splitting argument.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutator_mem_commutant_of_preserves
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (b : H →L[ℂ] H) (hb : b ∈ M.commutant) :
    T * b - b * T ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have hab := VonNeumannAlgebra.mem_commutant_iff.mp hb a ha
  have hDb := VonNeumannAlgebra.mem_commutant_iff.mp hb _ (hT a ha)
  calc
    a * (T * b - b * T) = (T * a) * b - a * b * T -
        ((T * a - a * T) * b) := by noncomm_ring
    _ = (T * a) * b - a * b * T - b * (T * a - a * T) := by rw [hDb]
    _ = T * (a * b) - b * T * a := by
      simp only [mul_sub, ← mul_assoc, ← hab]
      abel
    _ = (T * b - b * T) * a := by rw [hab]; noncomm_ring

theorem unitaryConj_sub_mem_commutant_of_preserves
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (u : unitary (H →L[ℂ] H)) (hu : u.val ∈ M.commutant) :
    unitaryConj u T - T ∈ M.commutant := by
  have hc := commutator_mem_commutant_of_preserves M T hT u.val hu
  have he : unitaryConj u T - T = -(T * u.val - u.val * T) * star u.val := by
    dsimp [unitaryConj]
    rw [neg_mul, sub_mul, mul_assoc T, Unitary.mul_star_self_of_mem u.property, mul_one]
    noncomm_ring
  rw [he]
  exact M.commutant.mul_mem (M.commutant.neg_mem hc)
    (M.commutant.toStarSubalgebra.star_mem' hu)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WOTDistanceSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weak operator separation and operator-norm distance

A dual estimate on weak-operator continuous functionals annihilating a
closed subspace gives strict norm approximants in that subspace.
-/

namespace KadisonKastler

open scoped Pointwise

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wotNormBall_compact (r : ℝ) : IsCompact (wotNormBall (H := H) r) := by
  let M : VonNeumannAlgebra H :=
    { toStarSubalgebra := StarSubalgebra.centralizer ℂ (∅ : Set (H →L[ℂ] H))
      centralizer_centralizer' := Set.centralizer_centralizer_centralizer _ }
  have he : Generator.Tracial.weakOperatorBall M r = wotNormBall (H := H) r := by
    ext T
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      change T.toCLM ∈ StarSubalgebra.centralizer ℂ (∅ : Set (H →L[ℂ] H))
      simp [StarSubalgebra.mem_centralizer_iff]
  rw [← he]
  exact Generator.Tracial.weakOperatorBall_isCompact M r

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalSpatialImplementer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Minimum distance for bounded self-adjoint spatial implementers

The bounded family of self-adjoint implementers of the same derivation is
weak-operator compact. Its distance from the self-adjoint part of the
algebra is attained. This is the compactness step of Sakai's spatial
splitting argument (Ann. Math. 83 (1966), Lemma 2, p.274).
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wot_isSelfAdjoint_isClosed :
    IsClosed {T : H →WOT[ℂ] H | IsSelfAdjoint T.toCLM} := by
  have he : {T : H →WOT[ℂ] H | IsSelfAdjoint T.toCLM} = {T | star T = T} := by
    ext T
    constructor
    · intro h
      exact DFunLike.ext _ _ (fun x => congrArg (fun A : H →L[ℂ] H => A x) h.star_eq)
    · intro h
      exact ContinuousLinearMap.ext (fun x => congrArg (fun A : H →WOT[ℂ] H => A x) h)
  rw [he]
  exact isClosed_eq continuous_star continuous_id

theorem wot_norm_lowerSemicontinuous :
    LowerSemicontinuous (fun T : H →WOT[ℂ] H => ‖T.toCLM‖) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  exact (wotNormBall_compact r).isClosed

theorem wot_vonNeumann_isClosed (M : VonNeumannAlgebra H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ M} := by
  have he : {T : H →WOT[ℂ] H | T.toCLM ∈ M} =
      {T | ∀ a : M.commutant.toStarSubalgebra, ∀ x y : H,
        inner ℂ (a.val.adjoint y) (T x) = inner ℂ y (T (a.val x))} := by
    ext T
    constructor
    · intro h a x y
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact congrArg (inner ℂ y) (congrArg (fun R : H →L[ℂ] H => R x)
        (VonNeumannAlgebra.mem_commutant_iff.mp a.property T.toCLM h).symm)
    · intro h
      rw [← VonNeumannAlgebra.commutant_commutant M]
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro a ha
      ext x
      apply ext_inner_left ℂ
      intro y
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMapWOT.toCLM_apply] using
        h ⟨a, ha⟩ x y
  rw [he]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun a => isClosed_iInter (fun x => isClosed_iInter (fun y =>
    isClosed_eq (continuous_inner_apply continuous_id x (a.val.adjoint y))
      (continuous_inner_apply continuous_id (a.val x) y))))

theorem boundedSelfAdjointImplementers_compact (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) : IsCompact (boundedSelfAdjointImplementers M T) := by
  have hc : IsClosed {S : H →WOT[ℂ] H | S.toCLM - T ∈ M.commutant} :=
    (wot_vonNeumann_isClosed M.commutant).preimage
      (continuous_id.sub continuous_const)
  have he : boundedSelfAdjointImplementers M T =
      wotNormBall ‖T‖ ∩ {S | IsSelfAdjoint S.toCLM} ∩
        {S | S.toCLM - T ∈ M.commutant} := by
    ext S
    simp only [boundedSelfAdjointImplementers, wotNormBall, Set.mem_ofPred_eq,
      Set.mem_inter_iff]
    tauto
  rw [he]
  exact ((wotNormBall_compact ‖T‖).inter_right wot_isSelfAdjoint_isClosed).inter_right hc

theorem exists_minimal_selfAdjoint_spatial_implementer
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ X S : H →L[ℂ] H, X ∈ M ∧ IsSelfAdjoint X ∧ IsSelfAdjoint S ∧
      ‖S‖ ≤ ‖T‖ ∧ S - T ∈ M.commutant ∧
      ∀ Y V : H →L[ℂ] H, Y ∈ M → IsSelfAdjoint Y → IsSelfAdjoint V →
        ‖V‖ ≤ ‖T‖ → V - T ∈ M.commutant → ‖X - S‖ ≤ ‖Y - V‖ := by
  let A : Set (H →WOT[ℂ] H) :=
    Generator.Tracial.weakOperatorBall M (2 * ‖T‖) ∩
      {X | IsSelfAdjoint X.toCLM}
  let K := boundedSelfAdjointImplementers M T
  have hA : IsCompact A :=
    (Generator.Tracial.weakOperatorBall_isCompact M _).inter_right
      wot_isSelfAdjoint_isClosed
  have hK : IsCompact K := boundedSelfAdjointImplementers_compact M T
  have hz : (0 : H →WOT[ℂ] H) ∈ A := by
    exact ⟨⟨M.zero_mem, by simp⟩, IsSelfAdjoint.zero _⟩
  have ht : ofCLM T ∈ K := by
    exact ⟨hT, le_rfl, by simp only [sub_self]; exact M.commutant.zero_mem⟩
  have hl : LowerSemicontinuous
      (fun p : (H →WOT[ℂ] H) × (H →WOT[ℂ] H) => ‖p.1.toCLM - p.2.toCLM‖) :=
    wot_norm_lowerSemicontinuous.comp (continuous_fst.sub continuous_snd)
  obtain ⟨p, hp, hmin⟩ := (hl.lowerSemicontinuousOn (A ×ˢ K)).exists_isMinOn
    (Set.prod_nonempty_iff.mpr ⟨⟨0, hz⟩, ⟨ofCLM T, ht⟩⟩) (hA.prod hK)
  have hmin' := isMinOn_iff.mp hmin
  have hbound : ‖p.1.toCLM - p.2.toCLM‖ ≤ ‖T‖ := by
    simpa only [ofCLM_toCLM, toCLM_zero, zero_sub, norm_neg] using
      hmin' (0, ofCLM T) (show (0, ofCLM T) ∈ A ×ˢ K from ⟨hz, ht⟩)
  refine ⟨p.1.toCLM, p.2.toCLM, hp.1.1.1, hp.1.2, hp.2.1, hp.2.2.1,
    hp.2.2.2, ?_⟩
  intro Y V hYM hY hV hnV hVT
  by_cases hnY : ‖Y‖ ≤ 2 * ‖T‖
  · exact hmin' (ofCLM Y, ofCLM V) (show (ofCLM Y, ofCLM V) ∈ A ×ˢ K from
      ⟨⟨⟨hYM, hnY⟩, hY⟩, ⟨hV, hnV, hVT⟩⟩)
  · have hn := norm_sub_norm_le Y V
    exact hbound.trans (by linarith)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalResidualFamily
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The convex family of minimum-distance spatial residuals

For a minimizing pair, the residuals with no larger norm form a convex
set invariant under the unitaries of the commutant. Every member has
exactly the minimum norm. A strict norm decrease inside this set is
therefore impossible.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem boundedSpatialResiduals_convex (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) : Convex ℝ (boundedSpatialResiduals M T X r) := by
  intro C hC D hD a b ha hb hab
  have he : X - (a • C + b • D) = a • (X - C) + b • (X - D) := by
    calc
      _ = (a + b) • X - (a • C + b • D) := by rw [hab, one_smul]
      _ = _ := by module
  have heT : X - (a • C + b • D) - T =
      a • (X - C - T) + b • (X - D - T) := by
    rw [he]
    calc
      _ = a • (X - C) + b • (X - D) - (a + b) • T := by rw [hab, one_smul]
      _ = _ := by module
  refine ⟨?_, ?_, ?_, ?_⟩
  · change star (a • C + b • D) = a • C + b • D
    simp only [star_add, star_smul, star_trivial, hC.1.star_eq, hD.1.star_eq]
  · have hc := (convex_closedBall (0 : H →L[ℂ] H) r)
      (show C ∈ Metric.closedBall 0 r by simpa only [Metric.mem_closedBall, dist_zero_right] using hC.2.1)
      (show D ∈ Metric.closedBall 0 r by simpa only [Metric.mem_closedBall, dist_zero_right] using hD.2.1) ha hb hab
    simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  · rw [he]
    have hc := (convex_closedBall (0 : H →L[ℂ] H) ‖T‖)
      (show X - C ∈ Metric.closedBall 0 ‖T‖ by simpa only [Metric.mem_closedBall, dist_zero_right] using hC.2.2.1)
      (show X - D ∈ Metric.closedBall 0 ‖T‖ by simpa only [Metric.mem_closedBall, dist_zero_right] using hD.2.2.1) ha hb hab
    simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  · rw [heT]
    exact M.commutant.add_mem
      ((M.commutant.toStarSubalgebra.restrictScalars ℝ).smul_mem hC.2.2.2 a)
      ((M.commutant.toStarSubalgebra.restrictScalars ℝ).smul_mem hD.2.2.2 b)

theorem boundedSpatialResiduals_conjugate (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) (hX : X ∈ M)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M.commutant)
    (C : H →L[ℂ] H) (hC : C ∈ boundedSpatialResiduals M T X r) :
    unitaryConj u C ∈ boundedSpatialResiduals M T X r := by
  have hXu : X * (u : H →L[ℂ] H) = (u : H →L[ℂ] H) * X :=
    VonNeumannAlgebra.mem_commutant_iff.mp hu X hX
  have hfix : unitaryConj u X = X := by
    change (u : H →L[ℂ] H) * X * star (u : H →L[ℂ] H) = X
    rw [← hXu, mul_assoc, u.property.2, mul_one]
  have he : X - unitaryConj u C = unitaryConj u (X - C) := by
    rw [unitaryConj_sub, hfix]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change star ((u : H →L[ℂ] H) * C * star (u : H →L[ℂ] H)) = _
    simp only [star_mul, star_star, hC.1.star_eq, unitaryConj, mul_assoc]
  · simpa only [norm_unitaryConj] using hC.2.1
  · rw [he, norm_unitaryConj]
    exact hC.2.2.1
  · have hd := unitaryConj_sub_mem_commutant_of_preserves M T hT u hu
    have hm : unitaryConj u (X - C - T) ∈ M.commutant :=
      M.commutant.mul_mem (M.commutant.mul_mem hu hC.2.2.2)
        (M.commutant.toStarSubalgebra.star_mem' hu)
    have hh : X - unitaryConj u C - T =
        unitaryConj u (X - C - T) + (unitaryConj u T - T) := by
      rw [he]
      simp only [unitaryConj_sub]
      abel
    rw [hh]
    exact M.commutant.add_mem hm hd

theorem boundedSpatialResiduals_norm_eq (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) (hX : IsSelfAdjoint X)
    (hmin : ∀ V : H →L[ℂ] H, IsSelfAdjoint V → ‖V‖ ≤ ‖T‖ →
      V - T ∈ M.commutant → r ≤ ‖X - V‖)
    (C : H →L[ℂ] H) (hC : C ∈ boundedSpatialResiduals M T X r) : ‖C‖ = r := by
  apply le_antisymm hC.2.1
  have hh := hmin (X - C) (hX.sub hC.1) hC.2.2.1 hC.2.2.2
  simpa only [sub_sub_cancel] using hh

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialProjectionCorners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial derivations and off-diagonal projection corners -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem boundedSpatialResiduals_preserves_commutant (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) (hX : X ∈ M)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (C : H →L[ℂ] H) (hC : C ∈ boundedSpatialResiduals M T X r)
    (w : H →L[ℂ] H) (hw : w ∈ M.commutant) :
    C * w - w * C ∈ M.commutant := by
  have hXw := VonNeumannAlgebra.mem_commutant_iff.mp hw X hX
  have hTc := commutator_mem_commutant_of_preserves M T hT w hw
  let Z := X - C - T
  have hZ : Z ∈ M.commutant := hC.2.2.2
  have he : C * w - w * C = -(T * w - w * T) - (Z * w - w * Z) := by
    dsimp [Z]
    simp only [sub_mul, mul_sub, hXw]
    abel
  rw [he]
  exact M.commutant.sub_mem (M.commutant.neg_mem hTc)
    (M.commutant.sub_mem (M.commutant.mul_mem hZ hw) (M.commutant.mul_mem hw hZ))

theorem CuntzFamily.offDiagonal_mem_of_preserves (S : CuntzFamily (Fin 2) H)
    (N : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ N)
    (C : H →L[ℂ] H) (hC : ∀ a ∈ N, C * a - a * C ∈ N)
    (i j : Fin 2) (hij : i ≠ j) : S.matrix C i j ∈ N := by
  have hm := N.mul_mem (N.toStarSubalgebra.star_mem' (hS i)) (hC (S.entry j) (hS j))
  change star (S.entry i) * C * S.entry j ∈ N.toSubalgebra
  simpa only [mul_sub, ← mul_assoc, S.orthogonal, ite_eq_right hij, zero_mul, sub_zero]
    using hm

theorem CuntzFamily.firstRange_commutes_of_corner_zero (S : CuntzFamily (Fin 2) H)
    (C : H →L[ℂ] H) (hC : IsSelfAdjoint C) (hc : S.matrix C 0 1 = 0) :
    Commute (S.entry 0 * star (S.entry 0)) C := by
  let p := S.entry 0 * star (S.entry 0)
  let q := S.entry 1 * star (S.entry 1)
  have hsum : p + q = 1 := by simpa only [Fin.sum_univ_two] using S.total
  have hpq : p * C * q = 0 := by
    calc
      p * C * q = S.entry 0 * (S.matrix C 0 1) * star (S.entry 1) := by
        simp only [p, q, matrix, mul_assoc]
      _ = 0 := by rw [hc, mul_zero, zero_mul]
  have hqp : q * C * p = 0 := by
    simpa only [star_mul, star_star, hC.star_eq, star_zero, p, q, mul_assoc]
      using congrArg star hpq
  show p * C = C * p
  calc
    p * C = p * C * (p + q) := by rw [hsum, mul_one]
    _ = p * C * p := by rw [mul_add, hpq, add_zero]
    _ = (p + q) * C * p := by rw [add_mul, add_mul, hqp, add_zero]
    _ = C * p := by rw [hsum, one_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIICommutantSpatialSplit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial splitting when the commutant is a separably acting type III factor

This is the type III commutant step of Sakai's spatial innerness proof.
Compact minimization, finite unitary averages and spectral projection
comparison supply every part of the argument.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_split_of_typeIII_commutant_of_projection_countability
    (M : VonNeumannAlgebra H) (hN : TypeIIIFactor M.commutant)
    (hFamilies : HasCountableProjectionFamilies M.commutant)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  obtain ⟨X, S, hXM, hXsa, hSsa, hSn, hST, hmin⟩ :=
    exists_minimal_selfAdjoint_spatial_implementer M T hTsa
  let r := ‖X - S‖
  let C := X - S
  let K := boundedSpatialResiduals M T X r
  have hC : C ∈ K := by
    refine ⟨hXsa.sub hSsa, le_rfl, ?_, ?_⟩
    · simpa only [C, sub_sub_cancel] using hSn
    · simpa only [C, sub_sub_cancel] using hST
  have hK : Convex ℝ K := boundedSpatialResiduals_convex M T X r
  have hinv (w : unitary (Algebra M.commutant)) (V : H →L[ℂ] H) (hV : V ∈ K) :
      unitaryConj (ambientAlgebraUnitary w) V ∈ K :=
    boundedSpatialResiduals_conjugate M T X r hXM hT (ambientAlgebraUnitary w)
      (w : Algebra M.commutant).property V hV
  have hself (V : H →L[ℂ] H) (hV : V ∈ K) : IsSelfAdjoint V := hV.1
  have hnorm (V : H →L[ℂ] H) (hV : V ∈ K) : ‖V‖ = r :=
    boundedSpatialResiduals_norm_eq M T X r hXsa
      (fun W hW hWn hWT => hmin X W hXM hXsa hW hWn hWT) V hV
  have hpreserve := boundedSpatialResiduals_preserves_commutant M T X r hXM hT C hC
  have hCN : C ∈ M.commutant.commutant := by
    apply mem_commutant_of_commutes_projections M.commutant C
    intro p
    by_cases hp : p.val = 0
    · rw [hp]
      exact Commute.zero_right _
    by_cases hp1 : p.val = 1
    · rw [hp1]
      exact Commute.one_right _
    obtain ⟨F, hF, hFp, _⟩ :=
      hN.exists_projection_coordinates_of_projection_countability hFamilies p hp hp1
    have hcorner : F.matrix C 0 1 = 0 :=
      F.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability
        M.commutant hN hFamilies hF K hK hinv
        hself r hnorm C hC
        (F.offDiagonal_mem_of_preserves M.commutant hF C hpreserve 0 1 (by decide))
    have hh := F.firstRange_commutes_of_corner_zero C hC.1 hcorner
    rw [hFp] at hh
    exact hh.symm
  have hCM : C ∈ M := by
    simpa only [VonNeumannAlgebra.commutant_commutant] using hCN
  have hSM : S ∈ M := by
    change S ∈ M.toSubalgebra
    have hh := M.sub_mem hXM hCM
    simpa only [C, sub_sub_cancel] using hh
  refine ⟨S, hSM, hSsa, hSn, ?_⟩
  change T - S ∈ M.commutant.toSubalgebra
  simpa only [neg_sub] using M.commutant.neg_mem hST

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorSpatialSplit
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial splitting for factors with countably decomposable commutant -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_split_of_factor_commutant_oai
    [Nontrivial H] (M : VonNeumannAlgebra H) (hN : ScalarCenter M.commutant)
    (hFamilies : HasCountableProjectionFamilies M.commutant)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  classical
  by_cases hfinite : ∃ p : Algebra M.commutant, IsStarProjection p ∧ p ≠ 0 ∧
      FiniteProjectionIn M.commutant p
  · obtain ⟨p, hp, hp0, hpf⟩ := hfinite
    let q : AlgebraProjection M.commutant := ⟨p, hp⟩
    let E := typeIIIInitialSpace q
    have hEq : p.val = E.starProjection := typeIIIInitialSpace_projection q
    have hE : E.starProjection ∈ M.commutant := hEq ▸ p.property
    have hE0 : E.starProjection ≠ 0 := by
      intro h
      exact hp0 (Subtype.ext (hEq.trans h))
    have hf : FiniteProjectionIn M.commutant ⟨E.starProjection, hE⟩ := by
      have he : (⟨E.starProjection, hE⟩ : Algebra M.commutant) = p := Subtype.ext hEq.symm
      rwa [he]
    exact exists_selfAdjoint_split_of_finite_commutant_corner E M hN hE hE0 hf T hTsa hT
  · have hIII : TypeIIIFactor M.commutant := {
      nonzero := _root_.one_ne_zero
      factor := hN
      purelyInfinite := by
        intro p hp hf
        by_contra hp0
        exact hfinite ⟨p, hp, hp0, hf⟩ }
    exact exists_selfAdjoint_split_of_typeIII_commutant_of_projection_countability
      M hIII hFamilies T hTsa hT

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_selfAdjoint_split_of_factor_commutant_oai.{u_1} := @OAI.KadisonKastler.exists_selfAdjoint_split_of_factor_commutant_oai.{u_1}
