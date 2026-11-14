-- Prove2me | solution 1 for OAI.KadisonKastler.projectionFamilyPinching_insert
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:31:51.450193+00:00
-- url     : https://prove2.me/submissions/101bad65-4aa9-494c-ab88-ec81285bdeee

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
import Definitions.Def_Q260K044

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
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartialPinchingRefinement
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilySpaces
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Closed spaces attached to a family of projection cuts

The remaining left corner and the simultaneous commutation space are
intersections of concrete operator kernels. Their projections therefore
exist also for infinite families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamilyPinching_isProjection (J : H ≃ₗᵢ⋆[ℂ] H)
    (S : Set (AlgebraProjection M)) : IsStarProjection (projectionFamilyPinching J S) :=
  ⟨Submodule.isIdempotentElem_starProjection _,isSelfAdjoint_starProjection _⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyCorner
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The remaining corner inside a family pinching

The quadratic remainder projection is contained in the simultaneous
commutation projection, including for infinite projection families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamily_left_annihilate (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hp : p∈S) : p.val.val*(projectionFamilyRemainder S).val.val=0 := by
  ext x
  exact (mem_projectionFamilyRemainderSpace S _).mp
    (Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace S).toSubmodule x) p hp

theorem projectionFamily_right_annihilate (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hp : p∈S) : (projectionFamilyRemainder S).val.val*p.val.val=0 := by
  have he := congrArg star (projectionFamily_left_annihilate S p hp)
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  have hq : star (projectionFamilyRemainder S).val.val=(projectionFamilyRemainder S).val.val :=
    congrArg Subtype.val (projectionFamilyRemainder S).property.isSelfAdjoint.star_eq
  simpa only [star_mul,star_zero,hs,hq] using he

theorem orthogonal_modularQuadratic_annihilate
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (p q : AlgebraProjection M) (hpq : p.val.val*q.val.val=0) :
    p.val.val*modularQuadratic J q.val=0 ∧
      conjugationOperator J p.val.val*modularQuadratic J q.val=0 := by
  constructor
  · change p.val.val*(q.val.val*conjugationOperator J q.val.val)=0
    rw [← mul_assoc,hpq,zero_mul]
  · have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) q.val.val q.val.property
    change conjugationOperator J p.val.val*(q.val.val*conjugationOperator J q.val.val)=0
    rw [← mul_assoc,← hc,mul_assoc,← conjugationOperator_mul J hJ,hpq]
    have hz : conjugationOperator J (0 : H →L[ℂ] H)=0 := by ext x; exact map_zero J
    rw [hz,mul_zero]

theorem projectionFamily_quadratic_mem_commutation
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) (x : H) :
    modularQuadratic J (projectionFamilyRemainder S).val x ∈ projectionFamilyCommutationSpace J S := by
  rw [mem_projectionFamilyCommutationSpace]
  intro p hp
  have hh := orthogonal_modularQuadratic_annihilate J hJ hright p (projectionFamilyRemainder S)
    (projectionFamily_left_annihilate S p hp)
  have h1 := congrArg (fun T : H →L[ℂ] H => T x) hh.1
  have h2 := congrArg (fun T : H →L[ℂ] H => T x) hh.2
  exact h1.trans h2.symm

theorem projectionFamilyPinching_quadratic
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) :
    projectionFamilyPinching J S*modularQuadratic J (projectionFamilyRemainder S).val=
      modularQuadratic J (projectionFamilyRemainder S).val := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (projectionFamily_quadratic_mem_commutation J hJ hright S x)

theorem projectionFamilyCommutationSpace_conjugate
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (S : Set (AlgebraProjection M)) {x : H}
    (hx : x ∈ projectionFamilyCommutationSpace J S) :
    J x ∈ projectionFamilyCommutationSpace J S := by
  rw [mem_projectionFamilyCommutationSpace] at hx ⊢
  intro p hp
  have he := congrArg J (hx p hp)
  change J (p.val.val x)=J (J (p.val.val (J x))) at he
  rw [hJ] at he
  change p.val.val (J x)=J (p.val.val (J (J x)))
  rw [hJ]
  exact he.symm

theorem projectionFamily_remainder_central
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) {x : H}
    (hx : x ∈ projectionFamilyCommutationSpace J S) :
    (projectionFamilyRemainder S).val.val x=
      conjugationOperator J (projectionFamilyRemainder S).val.val x := by
  let q := projectionFamilyRemainder S
  have haux (y : H) (hy : y ∈ projectionFamilyCommutationSpace J S) :
      conjugationOperator J q.val.val (q.val.val y)=q.val.val y := by
    have hmem : J (q.val.val y) ∈ projectionFamilyRemainderSpace S := by
      rw [mem_projectionFamilyRemainderSpace]
      intro p hp
      have hc := congrArg (fun T : H →L[ℂ] H => T y)
        (VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) q.val.val q.val.property)
      change q.val.val (conjugationOperator J p.val.val y)=
        conjugationOperator J p.val.val (q.val.val y) at hc
      have hyp := (mem_projectionFamilyCommutationSpace J S y).mp hy p hp
      have hz := congrArg (fun T : H →L[ℂ] H => T y) (projectionFamily_right_annihilate S p hp)
      change q.val.val (p.val.val y)=0 at hz
      calc
        p.val.val (J (q.val.val y)) = J (conjugationOperator J p.val.val (q.val.val y)) := by
          change _=J (J (p.val.val (J (q.val.val y))))
          rw [hJ]
        _ = J (q.val.val (conjugationOperator J p.val.val y)) := by rw [← hc]
        _ = 0 := by rw [← hyp,hz,map_zero]
    have hf : q.val.val (J (q.val.val y))=J (q.val.val y) :=
      Submodule.starProjection_eq_self_iff.mpr hmem
    change J (q.val.val (J (q.val.val y)))=q.val.val y
    rw [hf,hJ]
  have ha := haux x hx
  have hb := congrArg J (haux (J x) (projectionFamilyCommutationSpace_conjugate J hJ S hx))
  change J (J (q.val.val (J (q.val.val (J x)))))=J (q.val.val (J x)) at hb
  rw [hJ] at hb
  have hc := congrArg (fun T : H →L[ℂ] H => T x)
    (VonNeumannAlgebra.mem_commutant_iff.mp (hright q.val) q.val.val q.val.property)
  exact ha.symm.trans (hc.symm.trans hb)

theorem projectionFamily_remainder_mul_pinching
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) :
    (projectionFamilyRemainder S).val.val*projectionFamilyPinching J S=
      modularQuadratic J (projectionFamilyRemainder S).val := by
  let q := projectionFamilyRemainder S
  let R := projectionFamilyPinching J S
  have hRQ : R*modularQuadratic J q.val=modularQuadratic J q.val :=
    projectionFamilyPinching_quadratic J hJ hright S
  have hQR : modularQuadratic J q.val*R=modularQuadratic J q.val := by
    have he := congrArg star hRQ
    have hRs : star R=R := (projectionFamilyPinching_isProjection J S).isSelfAdjoint.star_eq
    simpa only [star_mul,hRs,
      (modularQuadratic_projection J hJ hright q).isSelfAdjoint.star_eq] using he
  ext x
  have hx : R x ∈ projectionFamilyCommutationSpace J S :=
    Submodule.starProjection_apply_mem _ _
  have hc := projectionFamily_remainder_central J hJ hright S hx
  have hi := congrArg (fun a : Algebra M => a.val (R x)) q.property.isIdempotentElem.eq
  have he : modularQuadratic J q.val (R x)=q.val.val (R x) := by
    change q.val.val (conjugationOperator J q.val.val (R x))=q.val.val (R x)
    rw [← hc]
    exact hi
  exact he.symm.trans (congrArg (fun T : H →L[ℂ] H => T x) hQR)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyCut
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Adding a projection from the remaining corner -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem pairedProjectionCut_fixed_iff {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) (x : H) :
    pairedProjectionCut p q x=x ↔ p x=q x := by
  have hn := pairedProjectionCut_discarded_norm hp hq hc x
  constructor
  · intro he
    have hz : (1-pairedProjectionCut p q) x=0 := by
      change x-pairedProjectionCut p q x=0
      rw [he,sub_self]
    rw [hz,norm_zero] at hn
    exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)
  · intro he
    have hz : (p-q) x=0 := sub_eq_zero.mpr he
    rw [hz,norm_zero] at hn
    have hh := norm_eq_zero.mp hn
    change x-pairedProjectionCut p q x=0 at hh
    exact (sub_eq_zero.mp hh).symm

theorem projectionFamily_conjugate_remainder_mul_pinching
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) :
    conjugationOperator J (projectionFamilyRemainder S).val.val*projectionFamilyPinching J S=
      modularQuadratic J (projectionFamilyRemainder S).val := by
  ext x
  have hx : projectionFamilyPinching J S x ∈ projectionFamilyCommutationSpace J S :=
    Submodule.starProjection_apply_mem _ _
  have he := projectionFamily_remainder_central J hJ hright S hx
  exact he.symm.trans (congrArg (fun T : H →L[ℂ] H => T x)
    (projectionFamily_remainder_mul_pinching J hJ hright S))

theorem projectionFamily_subprojection_mul_pinching
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) (p : AlgebraProjection M)
    (hpq : p≤projectionFamilyRemainder S) :
    p.val.val*projectionFamilyPinching J S=
      p.val.val*modularQuadratic J (projectionFamilyRemainder S).val ∧
    conjugationOperator J p.val.val*projectionFamilyPinching J S=
      conjugationOperator J p.val.val*modularQuadratic J (projectionFamilyRemainder S).val := by
  let q := projectionFamilyRemainder S
  let R := projectionFamilyPinching J S
  let Q := modularQuadratic J q.val
  have hp : p.val.val*q.val.val=p.val.val := congrArg Subtype.val (projection_mul_of_le hpq)
  have hrightq : conjugationOperator J q.val.val*R=Q :=
    projectionFamily_conjugate_remainder_mul_pinching J hJ hright S
  have hp' : conjugationOperator J p.val.val*conjugationOperator J q.val.val=
      conjugationOperator J p.val.val := by
    rw [← conjugationOperator_mul J hJ,hp]
  constructor
  · change p.val.val*R=p.val.val*Q
    calc
      _ = (p.val.val*q.val.val)*R := by rw [hp]
      _ = _ := by rw [mul_assoc,projectionFamily_remainder_mul_pinching J hJ hright S]
  · change conjugationOperator J p.val.val*R=conjugationOperator J p.val.val*Q
    calc
      _ = (conjugationOperator J p.val.val*conjugationOperator J q.val.val)*R := by rw [hp']
      _ = _ := by rw [mul_assoc,hrightq]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyInsert
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The remaining corner after one additional projection -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem mem_projectionFamilyCommutationSpace_insert (J : H ≃ₗᵢ⋆[ℂ] H)
    (S : Set (AlgebraProjection M)) (p : AlgebraProjection M) (x : H) :
    x ∈ projectionFamilyCommutationSpace J (insert p S) ↔
      x ∈ projectionFamilyCommutationSpace J S ∧ p.val.val x=conjugationOperator J p.val.val x := by
  simp only [mem_projectionFamilyCommutationSpace,Set.mem_insert_iff,forall_eq_or_imp]
  exact and_comm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyPinchingInsert
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Exact pinching refinement for an infinite family -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamilySelectedPart_isProjection
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) : IsStarProjection (projectionFamilySelectedPart J S) :=
  (modularQuadratic_projection J hJ hright (projectionFamilyRemainder S)).sub_of_mul_eq_right
    (projectionFamilyPinching_isProjection J S) (projectionFamilyPinching_quadratic J hJ hright S)

theorem projectionFamilySelectedPart_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) :
    projectionFamilySelectedPart J S*modularQuadratic J (projectionFamilyRemainder S).val=0 := by
  rw [projectionFamilySelectedPart,sub_mul,projectionFamilyPinching_quadratic J hJ hright,
    (modularQuadratic_projection J hJ hright (projectionFamilyRemainder S)).isIdempotentElem.eq,sub_self]

theorem projectionFamilyPinching_insert_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) (p : AlgebraProjection M)
    (hpq : p≤projectionFamilyRemainder S) :
    projectionFamilyPinching J (insert p S)=projectionFamilySelectedPart J S+
      refinedCornerProjection J (projectionFamilyRemainder S) p := by
  let q := projectionFamilyRemainder S
  let R := projectionFamilyPinching J S
  let A := projectionFamilySelectedPart J S
  let C := pairedProjectionCut p.val.val (conjugationOperator J p.val.val)
  let U := projectionFamilyPinching J (insert p S)
  have hA : IsStarProjection A := projectionFamilySelectedPart_isProjection J hJ hright S
  have hAQ : A*modularQuadratic J q.val=0 := projectionFamilySelectedPart_orthogonal J hJ hright S
  have hpa := projectionFamily_subprojection_mul_pinching J hJ hright S p hpq
  have hpA : p.val.val*A=0 := by
    change p.val.val*(R-modularQuadratic J q.val)=0
    rw [mul_sub,hpa.1,sub_self]
  have hjpA : conjugationOperator J p.val.val*A=0 := by
    change conjugationOperator J p.val.val*(R-modularQuadratic J q.val)=0
    rw [mul_sub,hpa.2,sub_self]
  have hCA : C*A=A := by
    have hj : (1-conjugationOperator J p.val.val)*A=A := by
      rw [sub_mul,one_mul,hjpA,sub_zero]
    have hp' : (1-p.val.val)*A=A := by rw [sub_mul,one_mul,hpA,sub_zero]
    change (p.val.val*conjugationOperator J p.val.val+
      (1-p.val.val)*(1-conjugationOperator J p.val.val))*A=A
    rw [add_mul,mul_assoc,hjpA,mul_zero,zero_add,mul_assoc,hj,hp']
  have hCR : C*R=A+refinedCornerProjection J q p := by
    have he : R=A+modularQuadratic J q.val := by dsimp only [A,projectionFamilySelectedPart,R,q]; abel
    rw [he,mul_add,hCA,refinedCornerProjection_mul_right J hJ hright q p hpq]
  have hCRp : IsStarProjection (C*R) := by
    rw [hCR]
    exact partialPinching_refinement_isProjection J hJ hright A hA q p hpq hAQ
  have hp := p.property.map M.toStarSubalgebra.subtype
  have hjp := (conjugateAlgebraProjection M M.commutant J hJ hright p).property.map
    M.commutant.toStarSubalgebra.subtype
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  have hCp : IsStarProjection C := pairedProjectionCut_isProjection hp hjp hcomm
  have hRp : IsStarProjection R := projectionFamilyPinching_isProjection J S
  have hRC : R*C=C*R := by
    have he := hCRp.isSelfAdjoint.star_eq
    simpa only [star_mul,hCp.isSelfAdjoint.star_eq,hRp.isSelfAdjoint.star_eq] using he
  have hUprod : U*(C*R)=C*R := by
    ext x
    change (projectionFamilyCommutationSpace J (insert p S)).toSubmodule.starProjection
      (C (R x))=C (R x)
    apply Submodule.starProjection_eq_self_iff.mpr
    change C (R x) ∈ projectionFamilyCommutationSpace J (insert p S)
    rw [mem_projectionFamilyCommutationSpace_insert]
    constructor
    · have he := congrArg (fun T : H →L[ℂ] H => T x) hRC
      change R (C x)=C (R x) at he
      rw [← he]
      exact Submodule.starProjection_apply_mem _ _
    · apply (pairedProjectionCut_fixed_iff hp hjp hcomm _).mp
      exact congrArg (fun T : H →L[ℂ] H => T (R x)) hCp.isIdempotentElem.eq
  have hprodU : (C*R)*U=U := by
    ext x
    have hx := (mem_projectionFamilyCommutationSpace_insert J S p _).mp
      (Submodule.starProjection_apply_mem (projectionFamilyCommutationSpace J (insert p S)).toSubmodule x)
    have hr : R (U x)=U x := Submodule.starProjection_eq_self_iff.mpr hx.1
    have hc : C (U x)=U x := (pairedProjectionCut_fixed_iff hp hjp hcomm _).mpr hx.2
    change C (R (U x))=U x
    rw [hr,hc]
  have hprodU' : (C*R)*U=C*R := by
    have he := congrArg star hUprod
    have hUp : IsStarProjection U := projectionFamilyPinching_isProjection J (insert p S)
    simpa only [star_mul,hCRp.isSelfAdjoint.star_eq,hUp.isSelfAdjoint.star_eq] using he
  exact hprodU.symm.trans (hprodU'.trans hCR)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.projectionFamilyPinching_insert_oai.{u_1} := @OAI.KadisonKastler.projectionFamilyPinching_insert_oai.{u_1}
