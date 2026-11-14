-- Prove2me | solution 1 for OAI.KadisonKastler.nearly_full_corner_projection_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:05:48.352541+00:00
-- url     : https://prove2.me/submissions/16f09b6a-5f1b-431e-877d-a7cb38959420

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
import Theorems.Thm_OAI_KadisonKastler_TypeIIIFactor_exists_isometry_onto_projection
import Theorems.Thm_OAI_KadisonKastler_positive_corner_projection_witness

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

theorem projection_complement_inner {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    inner ℂ (P x) ((1 - P) x) = 0 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self]
  rw [← P.adjoint_inner_right, hs]
  change inner ℂ x ((P * (1 - P)) x) = 0
  rw [hz, zero_apply, inner_zero_right]

theorem projection_norm_sq_decomposition {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := by
  calc
    _ = ‖P x + (1 - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
          (projection_complement_inner hP x)).symm
    _ = ‖x‖ ^ 2 := by simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerAngleBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform angle bound in a nearly full Hilbert corner

A projection which loses little of two orthogonal unit vectors keeps
both vectors nonzero and keeps their normalized angle away from zero.
The determinant estimate avoids introducing trigonometric functions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projection_corner_inner_bound {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (ξ η : H) (hη : ‖η‖=1) (horth : inner ℂ ξ η=0) :
    ‖inner ℂ (P ξ) (P η)‖ ≤ ‖(1-P) ξ‖ := by
  have hs : P.adjoint=P := hP.isSelfAdjoint.star_eq
  have he : inner ℂ (P ξ) (P η)= -(inner ℂ ((1-P) ξ) η) := by
    rw [← P.adjoint_inner_right,hs]
    change inner ℂ ξ ((P*P) η)=_
    rw [hP.isIdempotentElem.eq]
    have hh : inner ℂ ((1-P) ξ) η = inner ℂ ξ η-inner ℂ (P ξ) η := by
      change inner ℂ (ξ-P ξ) η=_
      rw [inner_sub_left]
    rw [hh,horth]
    have ht := P.adjoint_inner_right ξ η
    rw [hs] at ht
    simpa only [zero_sub,neg_neg] using ht
  rw [he,norm_neg]
  simpa only [hη,mul_one] using norm_inner_le_norm ((1-P) ξ) η

theorem projection_corner_angle_determinant {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (ξ η : H) (hξ : ‖ξ‖=1) (hη : ‖η‖=1)
    (horth : inner ℂ ξ η=0)
    (hsmall : ‖(1-P) ξ‖^2+‖(1-P) η‖^2 ≤ 1/16) :
    0 < ‖P ξ‖ ∧ 0 < ‖P η‖ ∧
      1/2 ≤ ‖P ξ‖^2*‖P η‖^2-(inner ℂ (P ξ) (P η)).re^2 := by
  have hx := projection_norm_sq_decomposition hP ξ
  have hy := projection_norm_sq_decomposition hP η
  rw [hξ] at hx
  rw [hη] at hy
  have hb := (Complex.abs_re_le_norm (inner ℂ (P ξ) (P η))).trans
    (projection_corner_inner_bound hP ξ η hη horth)
  have hb2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hb
  rw [sq_abs] at hb2
  have hprod := mul_nonneg (sq_nonneg ‖(1-P) ξ‖) (sq_nonneg ‖(1-P) η‖)
  have hdet : 1/2 ≤ ‖P ξ‖^2*‖P η‖^2-(inner ℂ (P ξ) (P η)).re^2 := by
    nlinarith only [hx,hy,hsmall,hb2,hprod,sq_nonneg ‖(1-P) ξ‖,sq_nonneg ‖(1-P) η‖]
  refine ⟨?_,?_,hdet⟩
  · nlinarith only [hx,hsmall,sq_nonneg ‖(1-P) η‖,norm_nonneg (P ξ)]
  · nlinarith only [hy,hsmall,sq_nonneg ‖(1-P) ξ‖,norm_nonneg (P η)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The cone generated by modular quadratic vectors

The definition uses actual vectors `a J a J ξ`, finite positive combinations,
and norm closure. Its invariance is algebraic. Positivity of the reference
pairing is kept explicit here and proved for the polar Tomita conjugation
in `TomitaPositivePairing`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.instInnerProductSpaceReal_solutions
theorem modularQuadratic_mem_positiveCone (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (a : Algebra M) :
    modularQuadratic J a ξ ∈ modularPositiveCone (M := M) J ξ :=
  subset_closure (ConvexCone.subset_hull ⟨a,rfl⟩)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveReal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular conjugation fixes the generated positive cone -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem reference_mem_modularPositiveCone
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (ξ : H) :
    ξ ∈ modularPositiveCone (M := M) J ξ := by
  have h := modularQuadratic_mem_positiveCone J ξ (1 : Algebra M)
  simpa only [modularQuadratic,OneMemClass.coe_one,conjugationOperator_one J hJ,
    one_mul,one_apply_eq_self] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerProjectionRefinement
attribute [-instance] _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizedCornerGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalized angles in nearly full corners -/

namespace KadisonKastler

open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem inner_normalize_re (x y : H) :
    (inner ℂ x y).re=‖x‖*‖y‖*(inner ℂ (normalize x) (normalize y)).re := by
  calc
    _ = (inner ℂ (‖x‖ • normalize x) (‖y‖ • normalize y)).re := by
      rw [norm_smul_normalize,norm_smul_normalize]
    _ = _ := by
      change (inner ℂ ((‖x‖ : ℂ) • normalize x) ((‖y‖ : ℂ) • normalize y)).re=_
      rw [inner_smul_left,inner_smul_right]
      simp only [Complex.conj_ofReal,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      ring

omit [CompleteSpace H] in
theorem normalized_angle_lower (x y : H) (hx : x≠0) (hy : y≠0)
    (hnx : ‖x‖≤1) (hny : ‖y‖≤1)
    (hdet : 1/2 ≤ ‖x‖^2*‖y‖^2-(inner ℂ x y).re^2) :
    1/2 ≤ 1-(inner ℂ (normalize x) (normalize y)).re^2 := by
  let c := (inner ℂ (normalize x) (normalize y)).re
  let P := ‖x‖^2*‖y‖^2
  have hab : |c|≤1 := by
    exact (Complex.abs_re_le_norm _).trans (by
      simpa only [norm_normalize hx,norm_normalize hy,mul_one] using
        norm_inner_le_norm (normalize x) (normalize y))
  have hc : c^2≤1 := by nlinarith only [(sq_le_sq₀ (abs_nonneg c) (by norm_num : (0:ℝ)≤1)).mpr hab,sq_abs c]
  have hP : P≤1 := by
    have hxx : ‖x‖^2≤1 := by nlinarith only [norm_nonneg x,hnx]
    have hyy : ‖y‖^2≤1 := by nlinarith only [norm_nonneg y,hny]
    exact (mul_le_mul hxx hyy (sq_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have he : (inner ℂ x y).re^2=P*c^2 := by
    rw [inner_normalize_re]
    dsimp only [P,c]
    ring
  have hh := mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hc)
  change 1/2≤1-c^2
  change 1/2≤P-(inner ℂ x y).re^2 at hdet
  rw [he] at hdet
  nlinarith only [hh,hdet]

omit [CompleteSpace H] in
theorem normalized_angle_noncollinear (x y : H) (hx : x≠0) (_hy : y≠0)
    (hangle : 1/2 ≤ 1-(inner ℂ (normalize x) (normalize y)).re^2) :
    normalize y≠normalize x ∧ normalize y≠-normalize x := by
  have hself : inner ℂ (normalize x) (normalize x)=1 := by
    rw [inner_self_eq_norm_sq_to_K,norm_normalize hx]
    norm_num
  constructor
  · intro he
    rw [he,hself] at hangle
    norm_num at hangle
  · intro he
    rw [he,inner_neg_right,hself] at hangle
    norm_num at hangle

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularIsometryCorner
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Isometric coordinates in a two-sided modular corner

An algebra isometry induces an isometry on the Hilbert space by `v J v J`.
Projection sandwiches intertwine both left and right actions, preserving
the commutator norms used in projection refinement.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ in
theorem modularQuadratic_one : modularQuadratic (M := M) J 1=1 := by
  change (1 : H →L[ℂ] H)*conjugationOperator J 1=1
  rw [conjugationOperator_one J hJ,one_mul]

include hJ hright in
theorem modularQuadratic_isometry (v : Algebra M) (hv : star v*v=1) :
    Isometry (modularQuadratic J v) := by
  apply (modularQuadratic J v).isometry_iff_adjoint_comp_self.mpr
  change star (modularQuadratic J v)*modularQuadratic J v=1
  rw [modularQuadratic_star J hJ hright,modularQuadratic_mul J hJ hright,
    hv,modularQuadratic_one J hJ]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCornerNormalization
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalization of the concrete two-sided corner coordinates -/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem modularQuadratic_isometry_inner (v : Algebra M) (hv : star v*v=1) (x y : H) :
    inner ℂ (modularQuadratic J v x) (modularQuadratic J v y)=inner ℂ x y :=
  (modularQuadratic J v).inner_map_map_iff_adjoint_comp_self.mpr
    ((modularQuadratic J v).isometry_iff_adjoint_comp_self.mp
      (modularQuadratic_isometry J hJ hright v hv)) x y

include hJ hright in
theorem modularCorner_pullback_norm (v : Algebra M) (hv : star v*v=1)
    (q : AlgebraProjection M) (hq : v*star v=q.val) (x : H) :
    ‖modularQuadratic J (star v) x‖=‖modularQuadratic J q.val x‖ := by
  calc
    _ = ‖modularQuadratic J v (modularQuadratic J (star v) x)‖ :=
      ((modularQuadratic_isometry J hJ hright v hv).norm_map_of_map_zero (map_zero _) _).symm
    _ = _ := by
      change ‖(modularQuadratic J v*modularQuadratic J (star v)) x‖=_
      rw [modularQuadratic_mul J hJ hright,hq]

include hJ hright in
theorem modularCorner_push_normalize (v : Algebra M) (hv : star v*v=1)
    (q : AlgebraProjection M) (hq : v*star v=q.val) (x : H) :
    modularQuadratic J v (normalize (modularQuadratic J (star v) x))=
      normalize (modularQuadratic J q.val x) := by
  change modularQuadratic J v (‖modularQuadratic J (star v) x‖⁻¹ •
    modularQuadratic J (star v) x)=‖modularQuadratic J q.val x‖⁻¹ • modularQuadratic J q.val x
  rw [ContinuousLinearMap.map_smul_of_tower,modularCorner_pullback_norm J hJ hright v hv q hq]
  congr 1
  change (modularQuadratic J v*modularQuadratic J (star v)) x=_
  rw [modularQuadratic_mul J hJ hright,hq]

include hJ hright in
theorem modularCorner_normalized_inner (v : Algebra M) (hv : star v*v=1)
    (q : AlgebraProjection M) (hq : v*star v=q.val) (x y : H) :
    inner ℂ (normalize (modularQuadratic J (star v) x))
        (normalize (modularQuadratic J (star v) y))=
      inner ℂ (normalize (modularQuadratic J q.val x)) (normalize (modularQuadratic J q.val y)) := by
  rw [← modularCorner_push_normalize J hJ hright v hv q hq x,
    ← modularCorner_push_normalize J hJ hright v hv q hq y,
    modularQuadratic_isometry_inner J hJ hright v hv]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnnormalizedProjectionWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Returning the projection estimates to the original corner vectors -/

namespace KadisonKastler

open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_apply_normalize_sq (T : H →L[ℂ] H) (x : H) :
    ‖T x‖^2=‖x‖^2*‖T (normalize x)‖^2 := by
  calc
    _ = ‖T (‖x‖ • normalize x)‖^2 := by rw [norm_smul_normalize]
    _ = _ := by
      rw [ContinuousLinearMap.map_smul_of_tower,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x),mul_pow]

theorem projection_witness_unnormalize
    (J : H ≃ₗᵢ⋆[ℂ] H) (x y : H) (p : H →L[ℂ] H)
    (hx : ‖x‖≤1) (hy : ‖y‖≤1) (hy' : 1/2≤‖y‖^2)
    (θ δ : ℝ) (hθ : 1/2≤θ) (hδ : 0 < δ)
    (hm : θ*(‖p (normalize x)‖^2+‖p (normalize y)‖^2) <
      16384*‖centralVectorDefect J (normalize y) p‖^2)
    (hd : ‖centralVectorDefect J (normalize x) p‖^2 <
      (δ/2)*‖centralVectorDefect J (normalize y) p‖^2) :
    ‖p x‖^2+‖p y‖^2 < 65536*‖centralVectorDefect J y p‖^2 ∧
      ‖centralVectorDefect J x p‖^2 < δ*‖centralVectorDefect J y p‖^2 := by
  let D : H →L[ℂ] H := p-conjugationOperator J (star p)
  have he (z : H) : centralVectorDefect J z p=D z := rfl
  simp only [he] at hm hd ⊢
  have hxx : ‖x‖^2≤1 := by nlinarith only [norm_nonneg x,hx]
  have hyy : ‖y‖^2≤1 := by nlinarith only [norm_nonneg y,hy]
  have hpx := norm_apply_normalize_sq p x
  have hpy := norm_apply_normalize_sq p y
  have hDx := norm_apply_normalize_sq D x
  have hDy := norm_apply_normalize_sq D y
  have hpx' : ‖p x‖^2≤‖p (normalize x)‖^2 := by
    rw [hpx]
    exact mul_le_of_le_one_left (sq_nonneg _) hxx
  have hpy' : ‖p y‖^2≤‖p (normalize y)‖^2 := by
    rw [hpy]
    exact mul_le_of_le_one_left (sq_nonneg _) hyy
  have hDx' : ‖D x‖^2≤‖D (normalize x)‖^2 := by
    rw [hDx]
    exact mul_le_of_le_one_left (sq_nonneg _) hxx
  have hDy' : ‖D (normalize y)‖^2≤2*‖D y‖^2 := by
    have hh := mul_le_mul_of_nonneg_right hy' (sq_nonneg ‖D (normalize y)‖)
    rw [← hDy] at hh
    linarith only [hh]
  constructor
  · have hmass := sq_nonneg ‖p (normalize x)‖
    have hmass' := sq_nonneg ‖p (normalize y)‖
    have hθmass := mul_le_mul_of_nonneg_right hθ (add_nonneg hmass hmass')
    have hn : ‖p (normalize x)‖^2+‖p (normalize y)‖^2 <
        32768*‖D (normalize y)‖^2 := by linarith only [hθmass,hm]
    linarith only [hpx',hpy',hn,hDy']
  · have hh := mul_le_mul_of_nonneg_left hDy' (show 0≤δ/2 by positivity)
    nlinarith only [hDx',hd,hh]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearlyFullCornerWitness
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform projection witness in every nearly full corner

The constant is independent of the corner. The hypotheses are the actual
positive reference and the all-vector remote coisometries already constructed
in the spatial two-ratio product.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.nearlyFullRealInner
theorem nearly_full_corner_projection_witness_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (q : AlgebraProjection M)
    (hsmall : ‖(1-modularQuadratic J q.val) ξ‖^2+
      ‖(1-modularQuadratic J q.val) η‖^2≤1/16)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M, p.val≠0 ∧ p≤q ∧
      ‖p.val.val (modularQuadratic J q.val ξ)‖^2+
        ‖p.val.val (modularQuadratic J q.val η)‖^2 <
        65536*‖centralVectorDefect J (modularQuadratic J q.val η) p.val.val‖^2 ∧
      ‖centralVectorDefect J (modularQuadratic J q.val ξ) p.val.val‖^2 <
        δ*‖centralVectorDefect J (modularQuadratic J q.val η) p.val.val‖^2 := by
  let P := modularQuadratic J q.val
  have hP : IsStarProjection P := modularQuadratic_projection J hJ hright q
  obtain ⟨hx,hy,hdet⟩ := projection_corner_angle_determinant hP ξ η huξ huη horth hsmall
  have hnx : ‖P ξ‖≤1 := (projection_apply_norm_le hP ξ).trans_eq huξ
  have hny : ‖P η‖≤1 := (projection_apply_norm_le hP η).trans_eq huη
  have hq : q.val≠0 := by
    intro he
    have hP0 : P=0 := by
      change modularQuadratic J q.val=0
      rw [he]
      rfl
    rw [hP0,zero_apply,norm_zero] at hx
    exact (lt_irrefl 0) hx
  obtain ⟨v,hv,hvq⟩ := hIII.exists_isometry_onto_projection q.val q.property hq
  let x := modularQuadratic J (star v) ξ
  let y := modularQuadratic J (star v) η
  have hxn : x≠0 := norm_ne_zero_iff.mp (ne_of_gt (by
    simpa only [x,modularCorner_pullback_norm J hJ hright v hv q hvq] using hx))
  have hyn : y≠0 := norm_ne_zero_iff.mp (ne_of_gt (by
    simpa only [y,modularCorner_pullback_norm J hJ hright v hv q hvq] using hy))
  have hang := normalized_angle_lower (P ξ) (P η) (norm_pos_iff.mp hx)
    (norm_pos_iff.mp hy) hnx hny hdet
  have hinner := modularCorner_normalized_inner J hJ hright v hv q hvq ξ η
  have hang' : 1/2≤1-(inner ℂ (normalize x) (normalize y)).re^2 := by
    change 1/2≤1-(inner ℂ (normalize (modularQuadratic J (star v) ξ))
      (normalize (modularQuadratic J (star v) η))).re^2
    rw [hinner]
    exact hang
  obtain ⟨hne,hne'⟩ := normalized_angle_noncollinear x y hxn hyn hang'
  obtain ⟨p,hp,hpq,hm,hd⟩ := positive_corner_projection_witness J hJ hright hleft
    ξ hξ hpos ξ (reference_mem_modularPositiveCone J hJ ξ) hsep
    (by rw [← norm_pos_iff,huξ]; norm_num) hIII hremote q v hv hvq η hη hyn hne hne'
    (half_pos hδ)
  simp only [modularCorner_push_normalize J hJ hright v hv q hvq,hinner] at hm hd
  have hY : 1/2≤‖P η‖^2 := by
    have hX : ‖P ξ‖^2≤1 := by nlinarith only [hnx,norm_nonneg (P ξ)]
    have hh := mul_le_of_le_one_left (sq_nonneg ‖P η‖) hX
    nlinarith only [hdet,hh,sq_nonneg (inner ℂ (P ξ) (P η)).re]
  exact ⟨p,hp,hpq,projection_witness_unnormalize J (P ξ) (P η) p.val.val
    hnx hny hY _ δ hang hδ hm hd⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.nearly_full_corner_projection_witness_oai.{u_1} := @OAI.KadisonKastler.nearly_full_corner_projection_witness_oai.{u_1}
