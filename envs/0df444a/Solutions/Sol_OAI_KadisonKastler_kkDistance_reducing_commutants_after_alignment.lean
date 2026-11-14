-- Prove2me | solution 1 for OAI.KadisonKastler.kkDistance_reducing_commutants_after_alignment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:26:07.317177+00:00
-- url     : https://prove2.me/submissions/577c6d97-4bc2-421a-b0f4-678c422e50d3

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.RootsOfUnity.Complex
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
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K014
import Definitions.Def_Q260K071
import Theorems.Thm_OAI_KadisonKastler_finiteFactor_commutant_approx_of_gap
import Theorems.Thm_OAI_KadisonKastler_nearInclusion_reducing_commutants_after_alignment

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RepresentedCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.coe_cornerUnitary _root_.OAI.KadisonKastler.complement_mul_cornerExtension _root_.OAI.KadisonKastler.cornerExtension_mul_complement _root_.OAI.KadisonKastler.cornerExtension_mul_starProjection _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.starProjection_mul_cornerExtension _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerFactorStructure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factor and finite-isometry structure of represented corners

Countable full matrix units identify the original algebra with the actual
amplification of its first corner. A central corner operator therefore
inflates to a central ambient operator. Finiteness of the first projection
also passes directly to the represented corner by extension by zero.
No trace or semifinite decomposition is assumed in these arguments.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

omit [CompleteSpace H] in
/-- Extension by zero is faithful, even when the original representation is
not the standard tracial representation. -/
theorem cornerExtension_injective : Function.Injective (cornerExtension E) := by
  intro T S h
  have he := congrArg (cornerCompression E) h
  simpa only [cornerCompression_extension] using he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearInclusionDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingCommutantCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant on a reducing subspace is the represented corner -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

omit [CompleteSpace H] in
theorem cornerExtension_mul_reducing (S : E →L[ℂ] E) (T : H →L[ℂ] H)
    (hT : E.starProjection * T = T * E.starProjection) :
    cornerExtension E (S * cornerCompression E T) = cornerExtension E S * T := by
  rw [cornerExtension_mul, cornerExtension_compression]
  calc
    cornerExtension E S * (E.starProjection * T * E.starProjection) =
        cornerExtension E S * T * E.starProjection := by
      rw [← mul_assoc, ← mul_assoc, cornerExtension_mul_starProjection]
    _ = cornerExtension E S * (E.starProjection * T) := by rw [mul_assoc, hT]
    _ = cornerExtension E S * T := by rw [← mul_assoc, cornerExtension_mul_starProjection]

omit [CompleteSpace H] in
theorem reducing_mul_cornerExtension (T : H →L[ℂ] H) (S : E →L[ℂ] E)
    (hT : E.starProjection * T = T * E.starProjection) :
    cornerExtension E (cornerCompression E T * S) = T * cornerExtension E S := by
  rw [cornerExtension_mul, cornerExtension_compression]
  calc
    E.starProjection * T * E.starProjection * cornerExtension E S =
        E.starProjection * T * cornerExtension E S := by
      rw [mul_assoc (E.starProjection * T), starProjection_mul_cornerExtension]
    _ = T * E.starProjection * cornerExtension E S := by rw [hT]
    _ = T * cornerExtension E S := by rw [mul_assoc, starProjection_mul_cornerExtension]

omit [CompleteSpace H] in
theorem commutes_corner_iff (T : H →L[ℂ] H) (S : E →L[ℂ] E)
    (hT : E.starProjection * T = T * E.starProjection) :
    Commute (cornerCompression E T) S ↔ Commute T (cornerExtension E S) := by
  constructor
  · intro h
    have hh := congrArg (cornerExtension E) h.eq
    rw [reducing_mul_cornerExtension E T S hT, cornerExtension_mul_reducing E S T hT] at hh
    exact hh
  · intro h
    apply cornerExtension_injective
    rw [reducing_mul_cornerExtension E T S hT, cornerExtension_mul_reducing E S T hT]
    exact h.eq

/-- The full commutant of the restricted algebra is exactly the corner
of the original commutant, with extension by zero identifying operators. -/
theorem commutant_reducingClosure (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M.commutant) :
    (generatedVonNeumannAlgebra (commutantReducingHom E M hE).range).commutant =
      representedCorner E M.commutant hE := by
  apply VonNeumannAlgebra.ext
  intro S
  rw [mem_representedCorner]
  constructor
  · intro hS
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hS
      (commutantReducingHom E M hE ⟨a, ha⟩)
      (subset_generatedVonNeumannAlgebra _ ⟨⟨a, ha⟩, rfl⟩)
    exact (commutes_corner_iff E a S
      (VonNeumannAlgebra.mem_commutant_iff.mp hE a ha).symm).mp hc
  · intro hS
    have hs : S ∈ Set.centralizer
        (Set.range (fun b : Algebra M => commutantReducingHom E M hE b)) := by
      rintro a ⟨b, rfl⟩
      exact ((commutes_corner_iff E b.val S
        (VonNeumannAlgebra.mem_commutant_iff.mp hE b.val b.property).symm).mpr
          (VonNeumannAlgebra.mem_commutant_iff.mp hS b.val b.property)).eq
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    change a ∈ (generatedVonNeumannAlgebra
      (commutantReducingHom E M hE).range : Set (E →L[ℂ] E)) at ha
    rw [generatedVonNeumannAlgebra_coe] at ha
    exact (ha S hs).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingCommutantNear
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutant approximation after aligning a reducing subspace

The finite-factor estimate is applied before moving the neighbor. This
keeps the error linear in the original gap, with no repeated amplification
constant after the unitary correction.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem cornerCompression_mem_reducing_commutant
    (M : VonNeumannAlgebra H) (hp : E.starProjection ∈ M.commutant)
    {T : H →L[ℂ] H} (hT : T ∈ M.commutant) :
    cornerCompression E T ∈
      (generatedVonNeumannAlgebra (commutantReducingHom E M hp).range).commutant := by
  rw [commutant_reducingClosure]
  apply (mem_representedCorner E M.commutant hp _).mpr
  rw [cornerExtension_compression]
  exact M.commutant.mul_mem (M.commutant.mul_mem hp hT) hp

variable [TopologicalSpace.SeparableSpace H]

theorem reducing_commutant_reverse_approx_after_alignment
    (M N : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hpM : E.starProjection ∈ M.commutant)
    (u : unitary (H →L[ℂ] H))
    (hpN : E.starProjection ∈ (unitaryConjugateAlgebra (star u) N).commutant)
    {γ : ℝ} (hγ : 0 < γ) (hgap : kkDistance M N < 2 * γ)
    (hu : ‖(u : H →L[ℂ] H) - 1‖ ≤ 200000000 * γ)
    (T : E →L[ℂ] E)
    (hT : T ∈ (generatedVonNeumannAlgebra
      (commutantReducingHom E (unitaryConjugateAlgebra (star u) N) hpN).range).commutant)
    (hnT : ‖T‖ ≤ 1) :
    ∃ D ∈ (generatedVonNeumannAlgebra (commutantReducingHom E M hpM).range).commutant,
      ‖D - T‖ < 404000000 * γ := by
  have hExt : cornerExtension E T ∈ (unitaryConjugateAlgebra (star u) N).commutant := by
    rw [commutant_reducingClosure] at hT
    exact (mem_representedCorner E _ hpN T).mp hT
  let S := unitaryConj u (cornerExtension E T)
  have hS : S ∈ N.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hExt
      (unitaryConj (star u) a) ⟨a, ha, rfl⟩
    have he := congrArg (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) hc
    rw [map_mul, map_mul] at he
    have hinv : unitaryConj u (unitaryConj (star u) a) = a := by
      simpa only [star_star] using unitaryConj_star_unitaryConj (star u) a
    simpa only [show ∀ X : H →L[ℂ] H,
      (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) X = unitaryConj u X from fun _ => rfl,
      hinv] using he
  have hnS : ‖S‖ ≤ 1 := by
    change ‖unitaryConj u (cornerExtension E T)‖ ≤ 1
    simpa only [norm_unitaryConj, norm_cornerExtension] using hnT
  obtain ⟨D, hD, hDS⟩ := finiteFactor_commutant_approx_of_gap M N hM
    (by positivity : 0 < 2 * γ) hgap S hS hnS
  refine ⟨cornerCompression E D, cornerCompression_mem_reducing_commutant E M hpM hD, ?_⟩
  have hSE : ‖S - cornerExtension E T‖ ≤ 400000000 * γ := by
    have hn := norm_unitaryConj_sub_le u (cornerExtension E T)
    rw [norm_cornerExtension] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by norm_num)) (norm_nonneg T)).trans
        (by nlinarith))
  have he : cornerCompression E D - T = cornerCompression E (D - cornerExtension E T) := by
    rw [map_sub, cornerCompression_extension]
  rw [he]
  apply (norm_cornerCompression_le E _).trans_lt
  have hd := norm_sub_le_norm_sub_add_norm_sub D S (cornerExtension E T)
  linarith

theorem reverse_nearInclusion_reducing_commutants_after_alignment
    (M N : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hpM : E.starProjection ∈ M.commutant)
    (u : unitary (H →L[ℂ] H))
    (hpN : E.starProjection ∈ (unitaryConjugateAlgebra (star u) N).commutant)
    {γ : ℝ} (hγ : 0 < γ) (hgap : kkDistance M N < 2 * γ)
    (hu : ‖(u : H →L[ℂ] H) - 1‖ ≤ 200000000 * γ) :
    NearInclusion
      (generatedVonNeumannAlgebra
        (commutantReducingHom E (unitaryConjugateAlgebra (star u) N) hpN).range).commutant
      (generatedVonNeumannAlgebra (commutantReducingHom E M hpM).range).commutant
      (405000000 * γ) := by
  refine ⟨404000000 * γ, by linarith, ?_⟩
  intro T hT
  obtain ⟨D, hD, hDT⟩ := reducing_commutant_reverse_approx_after_alignment E M N hM hpM
    u hpN hγ hgap hu T hT.1 hT.2
  exact (Metric.infDist_le_dist_of_mem hD).trans
    (by simpa only [dist_eq_norm, norm_sub_rev] using hDT.le)

theorem kkDistance_reducing_commutants_after_alignment_oai
    (M N : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hpM : E.starProjection ∈ M.commutant)
    (u : unitary (H →L[ℂ] H))
    (hpN : E.starProjection ∈ (unitaryConjugateAlgebra (star u) N).commutant)
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 3200000000)
    (hgap : kkDistance M N < 2 * γ)
    (hu : ‖(u : H →L[ℂ] H) - 1‖ ≤ 200000000 * γ) :
    kkDistance
      (generatedVonNeumannAlgebra (commutantReducingHom E M hpM).range).commutant
      (generatedVonNeumannAlgebra
        (commutantReducingHom E (unitaryConjugateAlgebra (star u) N) hpN).range).commutant ≤
      810000000 * γ := by
  have hf := nearInclusion_reducing_commutants_after_alignment E M N hN hpM
    u hpN hγ hsmall hgap hu
  have hr := reverse_nearInclusion_reducing_commutants_after_alignment E M N hM hpM
    u hpN hγ hgap hu
  have h := kkDistance_le_two_mul_of_nearInclusions (by positivity) hf hr
  nlinarith

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.kkDistance_reducing_commutants_after_alignment_oai.{u_1} := @OAI.KadisonKastler.kkDistance_reducing_commutants_after_alignment_oai.{u_1}
