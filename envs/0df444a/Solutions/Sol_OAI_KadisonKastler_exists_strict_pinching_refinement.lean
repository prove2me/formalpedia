-- Prove2me | solution 1 for OAI.KadisonKastler.exists_strict_pinching_refinement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:05:47.112773+00:00
-- url     : https://prove2.me/submissions/c18c03e5-5ef1-4b56-b1e0-fc3cdf4aafde

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
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
import Mathlib.Analysis.Normed.Algebra.Exponential
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
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dimension.Finite
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
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
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
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Equicontinuity
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
import Definitions.Def_Q260K037
import Theorems.Thm_OAI_KadisonKastler_nearly_full_corner_projection_witness

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionNormDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Squared-norm decompositions for nested projections -/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projection_apply_norm_le {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using P.le_of_opNorm_le (hP.norm_le P) x

theorem nested_projection_reverse {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hPR : P * R = P) :
    R * P = P := by
  have h := congrArg star hPR
  simpa only [star_mul, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq] using h

theorem nested_projection_norm_sq_eq {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hPR : P * R = P) (x : H) :
    ‖P x‖ ^ 2 + ‖(R - P) x‖ ^ 2 = ‖R x‖ ^ 2 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (R - P) = 0 := by
    rw [mul_sub, hPR, hP.isIdempotentElem.eq, sub_self]
  have hi : inner ℂ (P x) ((R - P) x) = 0 := by
    rw [← P.adjoint_inner_right, hs]
    change inner ℂ x ((P * (R - P)) x) = 0
    rw [hz, zero_apply, inner_zero_right]
  calc
    _ = ‖P x + (R - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi).symm
    _ = ‖R x‖ ^ 2 := by simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionCommutatorEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The energy removed by a two-sided projection cut

For commuting left and right projections, the diagonal cut is an
orthogonal projection. Its discarded squared norm is exactly the
squared norm of their difference acting on the vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pairedProjectionCut_isProjection {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) :
    IsStarProjection (pairedProjectionCut p q) := by
  have hc₁ : Commute (1 - p) q := (Commute.one_left q).sub_left hc
  have hc₂ : Commute (1 - p) (1 - q) := (Commute.one_right _).sub_right hc₁
  apply (hp.mul hq hc).add (hp.one_sub.mul hq.one_sub hc₂)
  calc
    (p * q) * ((1 - p) * (1 - q)) =
        p * (q * (1 - p)) * (1 - q) := by simp only [mul_assoc]
    _ = (p * (1 - p)) * (q * (1 - q)) := by rw [← hc₁.eq]; simp only [mul_assoc]
    _ = 0 := by rw [hp.mul_one_sub_self,zero_mul]

theorem pairedProjectionCut_complement {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) :
    (p - q) * (p - q) = 1 - pairedProjectionCut p q := by
  simp only [pairedProjectionCut,mul_sub,sub_mul,mul_one,one_mul,
    hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,← hc.eq]
  abel

theorem pairedProjectionCut_discarded_norm {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) (ξ : H) :
    ‖(1 - pairedProjectionCut p q) ξ‖ = ‖(p - q) ξ‖ := by
  let C := 1 - pairedProjectionCut p q
  let D := p - q
  have hC : IsStarProjection C := (pairedProjectionCut_isProjection hp hq hc).one_sub
  have hD : IsSelfAdjoint D := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hsC : C.adjoint = C := hC.isSelfAdjoint.star_eq
  have hsD : D.adjoint = D := hD.star_eq
  have hsq : ‖C ξ‖ ^ 2 = ‖D ξ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),← C.adjoint_inner_right,
      ← D.adjoint_inner_right,hsC,hsD]
    change (inner ℂ ξ ((C * C) ξ)).re = (inner ℂ ξ ((D * D) ξ)).re
    rw [hC.isIdempotentElem.eq]
    exact congrArg (fun T : H →L[ℂ] H => (inner ℂ ξ (T ξ)).re)
      (pairedProjectionCut_complement hp hq hc).symm
  change ‖C ξ‖ = ‖D ξ‖
  nlinarith [norm_nonneg (C ξ),norm_nonneg (D ξ)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveVectorPinching
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pinching positive vectors directly in the original representation

The matching two-sided cut preserves the positive cone and faithfulness,
centralizes the chosen projection, and has exactly the original
left-right projection gap as its displacement.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ in
theorem positiveVectorPinch_eq (p : AlgebraProjection M) (η : H) :
    positiveVectorPinch J p η = modularQuadratic J p.val η +
      modularQuadratic J (1-p.val) η := by
  change (p.val.val * conjugationOperator J p.val.val +
      (1-p.val.val) * (1-conjugationOperator J p.val.val)) η = _
  have he : conjugationOperator J (1-p.val).val = 1-conjugationOperator J p.val.val := by
    change conjugationOperator J (1-p.val.val) = _
    rw [conjugationOperator_sub,conjugationOperator_one J hJ]
  rw [add_apply]
  simp only [modularQuadratic,he]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerProjectionRefinement
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Energy gained by refining one two-sided corner

Splitting q into p and q-p removes exactly the p-commutator energy
inside qJq. These identities are the local step in Haagerup's
projection-family amplification argument.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem modularQuadratic_projection (p : AlgebraProjection M) :
    IsStarProjection (modularQuadratic J p.val) := by
  constructor
  · change modularQuadratic J p.val*modularQuadratic J p.val=modularQuadratic J p.val
    rw [modularQuadratic_mul J hJ hright,p.property.isIdempotentElem.eq]
  · change star (modularQuadratic J p.val)=modularQuadratic J p.val
    rw [modularQuadratic_star J hJ hright,p.property.isSelfAdjoint.star_eq]

include hJ in
theorem pairedProjectionCut_eq_quadratics (p : AlgebraProjection M) :
    pairedProjectionCut p.val.val (conjugationOperator J p.val.val)=
      modularQuadratic J p.val+modularQuadratic J (1-p.val) := by
  ext ξ
  exact positiveVectorPinch_eq J hJ p ξ

include hJ hright in
theorem refinedCornerProjection_mul_left (q p : AlgebraProjection M) (hpq : p ≤ q) :
    modularQuadratic J q.val*pairedProjectionCut p.val.val (conjugationOperator J p.val.val)=
      refinedCornerProjection J q p := by
  rw [pairedProjectionCut_eq_quadratics J hJ,mul_add,
    modularQuadratic_mul J hJ hright,modularQuadratic_mul J hJ hright,hpq,
    mul_sub,mul_one,hpq]
  rfl

include hJ hright in
theorem refinedCornerProjection_mul_right (q p : AlgebraProjection M) (hpq : p ≤ q) :
    pairedProjectionCut p.val.val (conjugationOperator J p.val.val)*modularQuadratic J q.val=
      refinedCornerProjection J q p := by
  rw [pairedProjectionCut_eq_quadratics J hJ,add_mul,
    modularQuadratic_mul J hJ hright,modularQuadratic_mul J hJ hright,
    projection_mul_of_le hpq,sub_mul,one_mul,projection_mul_of_le hpq]
  rfl

include hJ hright in
theorem refinedCornerProjection_isProjection (q p : AlgebraProjection M) (hpq : p ≤ q) :
    IsStarProjection (refinedCornerProjection J q p) := by
  have hc : Commute (modularQuadratic J q.val)
      (pairedProjectionCut p.val.val (conjugationOperator J p.val.val)) :=
    (refinedCornerProjection_mul_left J hJ hright q p hpq).trans
      (refinedCornerProjection_mul_right J hJ hright q p hpq).symm
  have hp := p.property.map M.toStarSubalgebra.subtype
  have hr := (conjugateAlgebraProjection M M.commutant J hJ hright p).property.map
    M.commutant.toStarSubalgebra.subtype
  have hpr := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  rw [← refinedCornerProjection_mul_left J hJ hright q p hpq]
  exact (modularQuadratic_projection J hJ hright q).mul
    (pairedProjectionCut_isProjection hp hr hpr) hc

include hJ hright in
theorem refinedCornerProjection_nested (q p : AlgebraProjection M) (hpq : p ≤ q) :
    refinedCornerProjection J q p*modularQuadratic J q.val=refinedCornerProjection J q p := by
  rw [← refinedCornerProjection_mul_right J hJ hright q p hpq,mul_assoc,
    (modularQuadratic_projection J hJ hright q).isIdempotentElem.eq]

include hJ hright in
theorem refinedCornerProjection_discarded_norm (q p : AlgebraProjection M) (hpq : p ≤ q) (ξ : H) :
    ‖(modularQuadratic J q.val-refinedCornerProjection J q p) ξ‖=
      ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val ξ)‖ := by
  have hp := p.property.map M.toStarSubalgebra.subtype
  have hr := (conjugateAlgebraProjection M M.commutant J hJ hright p).property.map
    M.commutant.toStarSubalgebra.subtype
  have hpr := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  rw [← refinedCornerProjection_mul_right J hJ hright q p hpq]
  calc
    _ = ‖((1-pairedProjectionCut p.val.val (conjugationOperator J p.val.val))*
        modularQuadratic J q.val) ξ‖ := by rw [sub_mul,one_mul]
    _ = _ := pairedProjectionCut_discarded_norm hp hr hpr (modularQuadratic J q.val ξ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerLossBound
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Cost of removing a subprojection from a symmetric corner

For a conjugation-fixed vector, removing p from q costs at most twice
its left p-mass inside the old two-sided corner.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem two_projection_union_norm_sq_le {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (R : H →L[ℂ] H) (ξ : H) :
    ‖(1-(1-P)*(1-R)) ξ‖^2 ≤ ‖P ξ‖^2+‖R ξ‖^2 := by
  have he : 1-(1-P)*(1-R)=P+(1-P)*R := by
    rw [mul_sub,mul_one]
    abel
  rw [he,add_apply]
  have hi : inner ℂ (P ξ) (((1-P)*R) ξ)=0 := by
    have hs : P.adjoint=P := hP.isSelfAdjoint.star_eq
    rw [← P.adjoint_inner_right,hs]
    change inner ℂ ξ ((P*((1-P)*R)) ξ)=0
    rw [← mul_assoc,hP.mul_one_sub_self,zero_mul,zero_apply,inner_zero_right]
  have hn : ‖P ξ+((1-P)*R) ξ‖^2=‖P ξ‖^2+‖((1-P)*R) ξ‖^2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
  rw [hn]
  exact add_le_add le_rfl
    (pow_le_pow_left₀ (norm_nonneg _) (projection_apply_norm_le hP.one_sub (R ξ)) 2)

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hright in
theorem modularQuadratic_projection_fixed (q : AlgebraProjection M) (ξ : H) (hξ : J ξ=ξ) :
    J (modularQuadratic J q.val ξ)=modularQuadratic J q.val ξ := by
  have he := VonNeumannAlgebra.mem_commutant_iff.mp (hright q.val) q.val.val q.val.property
  change J (q.val.val (J (q.val.val (J ξ))))=q.val.val (J (q.val.val (J ξ)))
  rw [hξ]
  have hh := congrArg (fun T : H →L[ℂ] H => T ξ) he
  change q.val.val (J (q.val.val (J ξ)))=J (q.val.val (J (q.val.val ξ))) at hh
  simpa only [hξ] using hh.symm

include hJ hright in
theorem cornerProjection_loss_bound (q p : AlgebraProjection M) (hpq : p ≤ q)
    (ξ : H) (hξ : J ξ=ξ) :
    ‖(modularQuadratic J q.val-modularQuadratic J (q.val-p.val)) ξ‖^2 ≤
      2*‖p.val.val (modularQuadratic J q.val ξ)‖^2 := by
  let w := modularQuadratic J q.val ξ
  have hw := modularQuadratic_projection_fixed J hright q ξ hξ
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have he : modularQuadratic J (1-p.val)*modularQuadratic J q.val=
      modularQuadratic J (q.val-p.val) := by
    rw [modularQuadratic_mul J hJ hright,sub_mul,one_mul,projection_mul_of_le hpq]
  have hq : conjugationOperator J (1-p.val).val=1-conjugationOperator J p.val.val := by
    change conjugationOperator J (1-p.val.val)=_
    rw [conjugationOperator_sub,conjugationOperator_one J hJ]
  have hh : (modularQuadratic J q.val-modularQuadratic J (q.val-p.val)) ξ=
      (1-(1-p.val.val)*(1-conjugationOperator J p.val.val)) w := by
    rw [← he]
    change w-modularQuadratic J (1-p.val) w=_
    rw [modularQuadratic,hq]
    rfl
  rw [hh]
  have hn : ‖conjugationOperator J p.val.val w‖=‖p.val.val w‖ := by
    change ‖J (p.val.val (J w))‖=_
    rw [hw,J.norm_map]
  have hb := two_projection_union_norm_sq_le hp (conjugationOperator J p.val.val) w
  rw [hn] at hb
  nlinarith only [hb]

include hJ hright in
theorem cornerProjection_residual_bound (q p : AlgebraProjection M) (hpq : p ≤ q)
    (ξ : H) (hξ : J ξ=ξ) :
    ‖(1-modularQuadratic J (q.val-p.val)) ξ‖^2 ≤
      ‖(1-modularQuadratic J q.val) ξ‖^2+
      2*‖p.val.val (modularQuadratic J q.val ξ)‖^2 := by
  have hsub : IsStarProjection (q.val-p.val) := p.property.sub_of_mul_eq_left q.property
    (projection_mul_of_le hpq)
  let r : AlgebraProjection M := ⟨q.val-p.val,hsub⟩
  have hn : modularQuadratic J r.val*modularQuadratic J q.val=modularQuadratic J r.val := by
    rw [modularQuadratic_mul J hJ hright]
    change modularQuadratic J ((q.val-p.val)*q.val)=_
    rw [sub_mul,q.property.isIdempotentElem.eq,projection_mul_of_le hpq]
  have he := nested_projection_norm_sq_eq (modularQuadratic_projection J hJ hright q).one_sub
    (show (1-modularQuadratic J q.val)*(1-modularQuadratic J r.val)=
      1-modularQuadratic J q.val by
      have hn' := nested_projection_reverse (modularQuadratic_projection J hJ hright r)
        (modularQuadratic_projection J hJ hright q) hn
      rw [sub_mul,one_mul,mul_sub,mul_one,hn']
      abel) ξ
  have hd : (1-modularQuadratic J r.val)-(1-modularQuadratic J q.val)=
      modularQuadratic J q.val-modularQuadratic J r.val := by abel
  rw [hd] at he
  have hb := cornerProjection_loss_bound J hJ hright q p hpq ξ hξ
  change _+‖(modularQuadratic J q.val-modularQuadratic J (q.val-p.val)) ξ‖^2=_ at he
  linarith only [he,hb]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartialPinchingRefinement
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Adding one cut to a partial pinching

Already selected orthogonal corners are left fixed. Refining the remaining
corner increases the residual squared norm by exactly the local commutator
energy. This is the additive identity used by the maximal-family argument.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem orthogonal_projection_mul_reverse {A B : H →L[ℂ] H}
    (hA : IsStarProjection A) (hB : IsStarProjection B) (hAB : A*B=0) : B*A=0 := by
  have he := congrArg star hAB
  simpa only [star_mul,hA.isSelfAdjoint.star_eq,hB.isSelfAdjoint.star_eq,star_zero] using he

theorem orthogonal_sum_nested {A B C : H →L[ℂ] H}
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hAB : A*B=0) (hCB : C*B=C) : (A+C)*(A+B)=A+C := by
  have hBA := orthogonal_projection_mul_reverse hA hB hAB
  have hCA : C*A=0 := by
    calc
      _ = (C*B)*A := by rw [hCB]
      _ = 0 := by rw [mul_assoc,hBA,mul_zero]
  rw [add_mul,mul_add,mul_add,hA.isIdempotentElem.eq,hAB,hCA,hCB,add_zero,zero_add]

theorem nested_projection_residual_energy {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hPR : P*R=P) (ξ : H) :
    ‖(1-P) ξ‖^2=‖(1-R) ξ‖^2+‖(R-P) ξ‖^2 := by
  have hRP := nested_projection_reverse hP hR hPR
  have hn : (1-R)*(1-P)=1-R := by
    rw [sub_mul,one_mul,mul_sub,mul_one,hRP]
    abel
  have he := nested_projection_norm_sq_eq hR.one_sub hn ξ
  have hd : (1-P)-(1-R)=R-P := by abel
  rw [hd] at he
  exact he.symm

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem partialPinching_refinement_isProjection (A : H →L[ℂ] H)
    (hA : IsStarProjection A) (q p : AlgebraProjection M) (hpq : p ≤ q)
    (hAq : A*modularQuadratic J q.val=0) :
    IsStarProjection (A+refinedCornerProjection J q p) := by
  apply hA.add (refinedCornerProjection_isProjection J hJ hright q p hpq)
  calc
    A*refinedCornerProjection J q p =
        A*(modularQuadratic J q.val*pairedProjectionCut p.val.val
          (conjugationOperator J p.val.val)) := by
      rw [refinedCornerProjection_mul_left J hJ hright q p hpq]
    _ = 0 := by rw [← mul_assoc,hAq,zero_mul]

include hJ hright in
theorem partialPinching_refinement_energy (A : H →L[ℂ] H)
    (hA : IsStarProjection A) (q p : AlgebraProjection M) (hpq : p ≤ q)
    (hAq : A*modularQuadratic J q.val=0) (ξ : H) :
    ‖(1-(A+refinedCornerProjection J q p)) ξ‖^2 =
      ‖(1-(A+modularQuadratic J q.val)) ξ‖^2+
      ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val ξ)‖^2 := by
  have hq := modularQuadratic_projection J hJ hright q
  have he := nested_projection_residual_energy
    (partialPinching_refinement_isProjection J hJ hright A hA q p hpq hAq)
    (hA.add hq hAq)
    (orthogonal_sum_nested hA hq hAq (refinedCornerProjection_nested J hJ hright q p hpq)) ξ
  have hd : (A+modularQuadratic J q.val)-(A+refinedCornerProjection J q p)=
      modularQuadratic J q.val-refinedCornerProjection J q p := by abel
  rwa [hd,refinedCornerProjection_discarded_norm J hJ hright q p hpq] at he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PinchingRefinementInvariants
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two inequalities preserved by projection-family refinement

The total corner loss is charged to the test-vector displacement; the
reference-vector displacement stays a prescribed small proportion of it.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem partialPinching_refinement_preserves
    (A : H →L[ℂ] H) (hA : IsStarProjection A)
    (q p : AlgebraProjection M) (hpq : p ≤ q)
    (hAq : A*modularQuadratic J q.val=0)
    (ξ η : H) (hξ : J ξ=ξ) (hη : J η=η) (C δ : ℝ)
    (hwide : ‖(1-modularQuadratic J q.val) ξ‖^2+
        ‖(1-modularQuadratic J q.val) η‖^2 ≤
      C*‖(1-(A+modularQuadratic J q.val)) η‖^2)
    (hsmall : ‖(1-(A+modularQuadratic J q.val)) ξ‖^2 ≤
      δ*‖(1-(A+modularQuadratic J q.val)) η‖^2)
    (hmass : 2*(‖p.val.val (modularQuadratic J q.val ξ)‖^2+
        ‖p.val.val (modularQuadratic J q.val η)‖^2) ≤
      C*‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val η)‖^2)
    (hdefect : ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val ξ)‖^2 ≤
      δ*‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val η)‖^2) :
    (‖(1-modularQuadratic J (q.val-p.val)) ξ‖^2+
        ‖(1-modularQuadratic J (q.val-p.val)) η‖^2 ≤
      C*‖(1-(A+refinedCornerProjection J q p)) η‖^2) ∧
    (‖(1-(A+refinedCornerProjection J q p)) ξ‖^2 ≤
      δ*‖(1-(A+refinedCornerProjection J q p)) η‖^2) := by
  have hξloss := cornerProjection_residual_bound J hJ hright q p hpq ξ hξ
  have hηloss := cornerProjection_residual_bound J hJ hright q p hpq η hη
  have heξ := partialPinching_refinement_energy J hJ hright A hA q p hpq hAq ξ
  have heη := partialPinching_refinement_energy J hJ hright A hA q p hpq hAq η
  constructor
  · rw [heη,mul_add]
    linarith only [hξloss,hηloss,hwide,hmass]
  · rw [heξ,heη,mul_add]
    exact add_le_add hsmall hdefect

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrictPinchingRefinement
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A strict admissible refinement of every nearly full remainder

Both quantitative invariants survive the split, and the test-vector
energy increases strictly. This is the local contradiction for a maximal
orthogonal projection family.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.strictPinchingRealInner
theorem exists_strict_pinching_refinement_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (A : H →L[ℂ] H) (hA : IsStarProjection A) (q : AlgebraProjection M)
    (hAq : A*modularQuadratic J q.val=0) (δ : ℝ) (hδ : 0 < δ)
    (hwide : ‖(1-modularQuadratic J q.val) ξ‖^2+
        ‖(1-modularQuadratic J q.val) η‖^2 ≤
      131072*‖(1-(A+modularQuadratic J q.val)) η‖^2)
    (hsmall : ‖(1-(A+modularQuadratic J q.val)) ξ‖^2 ≤
      δ*‖(1-(A+modularQuadratic J q.val)) η‖^2)
    (hgap : 131072*‖(1-(A+modularQuadratic J q.val)) η‖^2 ≤ 1/16) :
    ∃ p : AlgebraProjection M, p.val≠0 ∧ p≤q ∧
      IsStarProjection (A+refinedCornerProjection J q p) ∧
      (‖(1-modularQuadratic J (q.val-p.val)) ξ‖^2+
          ‖(1-modularQuadratic J (q.val-p.val)) η‖^2 ≤
        131072*‖(1-(A+refinedCornerProjection J q p)) η‖^2) ∧
      (‖(1-(A+refinedCornerProjection J q p)) ξ‖^2 ≤
        δ*‖(1-(A+refinedCornerProjection J q p)) η‖^2) ∧
      ‖(1-(A+modularQuadratic J q.val)) η‖^2 <
        ‖(1-(A+refinedCornerProjection J q p)) η‖^2 := by
  obtain ⟨p,hp,hpq,hm,hd⟩ := nearly_full_corner_projection_witness J hJ hright hleft
    ξ hξ huξ hsep hpos hIII hremote η hη huη horth q (hwide.trans hgap) hδ
  have he (z : H) : centralVectorDefect J z p.val.val=
      (p.val.val-conjugationOperator J p.val.val) z := by
    rw [centralVectorDefect_apply]
    have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
    rw [hs]
    rfl
  simp only [he] at hm hd
  have hmass : 2*(‖p.val.val (modularQuadratic J q.val ξ)‖^2+
      ‖p.val.val (modularQuadratic J q.val η)‖^2) ≤
      131072*‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val η)‖^2 := by
    linarith only [hm]
  have hinv := partialPinching_refinement_preserves J hJ hright A hA q p hpq hAq
    ξ η hξ hη 131072 δ hwide hsmall hmass hd.le
  refine ⟨p,hp,hpq,partialPinching_refinement_isProjection J hJ hright A hA q p hpq hAq,
    hinv.1,hinv.2,?_⟩
  rw [partialPinching_refinement_energy J hJ hright A hA q p hpq hAq η]
  have hpos' : 0 < ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val η)‖^2 := by
    nlinarith only [hm,sq_nonneg ‖p.val.val (modularQuadratic J q.val ξ)‖,
      sq_nonneg ‖p.val.val (modularQuadratic J q.val η)‖]
  linarith only [hpos']

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_strict_pinching_refinement_oai.{u_1} := @OAI.KadisonKastler.exists_strict_pinching_refinement_oai.{u_1}
