-- Prove2me | solution 1 for OAI.KadisonKastler.exists_uniform_pinching_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:31:49.9832+00:00
-- url     : https://prove2.me/submissions/9f7c6a4e-7229-44e8-bd5f-cddca66c3f2d

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
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Theorems.Thm_OAI_KadisonKastler_exists_strict_pinching_refinement
import Theorems.Thm_OAI_KadisonKastler_projectionFamilyPinching_insert

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerProjectionRefinement
attribute [-instance] _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_DecreasingProjectionLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong limits of decreasing closed-subspace projections

Applied to the commutation subspaces and remaining corners of a chain
of orthogonal projection families.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem decreasing_closed_projection_tendsto {ι : Type*} [Preorder ι]
    (K : ι → ClosedSubmodule ℂ H) (hK : Antitone K) (x : H) :
    Tendsto (fun i => (K i).toSubmodule.starProjection x) atTop
      (𝓝 ((⨅ i, K i).toSubmodule.starProjection x)) := by
  let U (i : ι) : Submodule ℂ H := (K i)ᗮ.toSubmodule
  have hU : Monotone U := fun _ _ hij => ClosedSubmodule.orthogonal_le (hK hij)
  have hs : (⨆ i, U i).topologicalClosure=(⨆ i, (K i)ᗮ).toSubmodule := by
    exact (ClosedSubmodule.toSubmodule_iSup (fun i => (K i)ᗮ)).symm
  have hoo (L : ClosedSubmodule ℂ H) : Lᗮᗮ=L := by
    ext z
    change z ∈ L.toSubmoduleᗮᗮ ↔ z ∈ L.toSubmodule
    rw [Submodule.orthogonal_orthogonal]
  have hi : (⨆ i, (K i)ᗮ)=(⨅ i, K i)ᗮ := by
    have hh := congrArg ClosedSubmodule.orthogonal
      (ClosedSubmodule.iInf_orthogonal (fun i => (K i)ᗮ))
    simpa only [hoo] using hh.symm
  have ht := Submodule.starProjection_tendsto_closure_iSup U hU x
  have hs' : (⨆ i, U i).topologicalClosure=((⨅ i, K i)ᗮ).toSubmodule := hs.trans (congrArg _ hi)
  have hp : (⨆ i, U i).topologicalClosure.starProjection=
      ((⨅ i, K i)ᗮ).toSubmodule.starProjection := by
    congr 1
  rw [hp] at ht
  have he (L : ClosedSubmodule ℂ H) : Lᗮ.toSubmodule.starProjection x=
      x-L.toSubmodule.starProjection x := by
    change L.toSubmoduleᗮ.starProjection x=x-L.toSubmodule.starProjection x
    rw [Submodule.starProjection_orthogonal]
    rfl
  simp only [U,he] at ht
  have hc : Tendsto (fun _ : ι => x) atTop (𝓝 x) := tendsto_const_nhds
  simpa only [sub_sub_cancel] using hc.sub ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularIsometryCorner
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem projectionFamilyRemainderSpace_antitone :
    Antitone (projectionFamilyRemainderSpace (M := M)) := by
  intro S T hST x hx
  rw [mem_projectionFamilyRemainderSpace] at hx ⊢
  exact fun p hp => hx p (hST hp)

theorem projectionFamilyCommutationSpace_antitone (J : H ≃ₗᵢ⋆[ℂ] H) :
    Antitone (projectionFamilyCommutationSpace (M := M) J) := by
  intro S T hST x hx
  rw [mem_projectionFamilyCommutationSpace] at hx ⊢
  exact fun p hp => hx p (hST hp)

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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongAnalyticApply
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Applying a locally bounded strongly holomorphic operator field -/

namespace KadisonKastler

open Filter
open scoped Topology

variable {X E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A locally bounded strong operator limit can be evaluated on converging vectors. -/
theorem tendsto_strong_apply {l : Filter X} {A : X → E →L[ℂ] F} {A₀ : E →L[ℂ] F}
    (hA : ∀ y, Tendsto (fun s => A s y) l (𝓝 (A₀ y)))
    {B : ℝ} (hB : ∀ᶠ s in l, ‖A s‖ ≤ B)
    {x : X → E} {x₀ : E} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun s => A s (x s)) l (𝓝 (A₀ x₀)) := by
  have hzero : Tendsto (fun s => A s (x s - x₀)) l (𝓝 0) := by
    apply squeeze_zero_norm' (hB.mono fun s hs =>
      ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _)))
    have hz : Tendsto (fun s => ‖x s - x₀‖) l (𝓝 0) := by
      simpa using (hx.sub_const x₀).norm
    simpa using hz.const_mul B
  convert hzero.add (hA x₀) using 1
  · funext s
    rw [map_sub, sub_add_cancel]
  · rw [zero_add]

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyLimits
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong limits for increasing families of projection tests -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamilyRemainderSpace_iUnion {ι : Type*}
    (S : ι → Set (AlgebraProjection M)) :
    projectionFamilyRemainderSpace (⋃ i, S i)=⨅ i, projectionFamilyRemainderSpace (S i) := by
  ext x
  change x ∈ projectionFamilyRemainderSpace (⋃ i, S i) ↔
    x ∈ (⨅ i, projectionFamilyRemainderSpace (S i) : ClosedSubmodule ℂ H)
  rw [mem_projectionFamilyRemainderSpace,ClosedSubmodule.mem_iInf]
  constructor
  · intro hx i
    rw [mem_projectionFamilyRemainderSpace]
    exact fun p hp => hx p (Set.mem_iUnion.mpr ⟨i,hp⟩)
  · intro hx p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    exact (mem_projectionFamilyRemainderSpace (S i) x).mp (hx i) p hi

theorem projectionFamilyCommutationSpace_iUnion {ι : Type*}
    (J : H ≃ₗᵢ⋆[ℂ] H) (S : ι → Set (AlgebraProjection M)) :
    projectionFamilyCommutationSpace J (⋃ i, S i)=⨅ i, projectionFamilyCommutationSpace J (S i) := by
  ext x
  change x ∈ projectionFamilyCommutationSpace J (⋃ i, S i) ↔
    x ∈ (⨅ i, projectionFamilyCommutationSpace J (S i) : ClosedSubmodule ℂ H)
  rw [mem_projectionFamilyCommutationSpace,ClosedSubmodule.mem_iInf]
  constructor
  · intro hx i
    rw [mem_projectionFamilyCommutationSpace]
    exact fun p hp => hx p (Set.mem_iUnion.mpr ⟨i,hp⟩)
  · intro hx p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    exact (mem_projectionFamilyCommutationSpace J (S i) x).mp (hx i) p hi

theorem projectionFamilyRemainder_tendsto {ι : Type*} [Preorder ι]
    (S : ι → Set (AlgebraProjection M)) (hS : Monotone S) (x : H) :
    Tendsto (fun i => (projectionFamilyRemainder (S i)).val.val x) atTop
      (𝓝 ((projectionFamilyRemainder (⋃ i, S i)).val.val x)) := by
  have hK : Antitone (fun i => projectionFamilyRemainderSpace (S i)) :=
    projectionFamilyRemainderSpace_antitone.comp_monotone hS
  have ht := decreasing_closed_projection_tendsto _ hK x
  have hp : (⨅ i, projectionFamilyRemainderSpace (S i)).toSubmodule.starProjection=
      (projectionFamilyRemainderSpace (⋃ i, S i)).toSubmodule.starProjection := by
    congr 1
    exact congrArg ClosedSubmodule.toSubmodule (projectionFamilyRemainderSpace_iUnion S).symm
  rw [hp] at ht
  exact ht

theorem projectionFamilyPinching_tendsto {ι : Type*} [Preorder ι]
    (J : H ≃ₗᵢ⋆[ℂ] H) (S : ι → Set (AlgebraProjection M)) (hS : Monotone S) (x : H) :
    Tendsto (fun i => projectionFamilyPinching J (S i) x) atTop
      (𝓝 (projectionFamilyPinching J (⋃ i, S i) x)) := by
  have hK : Antitone (fun i => projectionFamilyCommutationSpace J (S i)) :=
    (projectionFamilyCommutationSpace_antitone J).comp_monotone hS
  have ht := decreasing_closed_projection_tendsto _ hK x
  have hp : (⨅ i, projectionFamilyCommutationSpace J (S i)).toSubmodule.starProjection=
      (projectionFamilyCommutationSpace J (⋃ i, S i)).toSubmodule.starProjection := by
    congr 1
    exact congrArg ClosedSubmodule.toSubmodule (projectionFamilyCommutationSpace_iUnion J S).symm
  rw [hp] at ht
  exact ht

theorem projectionFamilyQuadratic_tendsto {ι : Type*} [Preorder ι]
    (J : H ≃ₗᵢ⋆[ℂ] H) (S : ι → Set (AlgebraProjection M)) (hS : Monotone S) (x : H) :
    Tendsto (fun i => modularQuadratic J (projectionFamilyRemainder (S i)).val x) atTop
      (𝓝 (modularQuadratic J (projectionFamilyRemainder (⋃ i, S i)).val x)) := by
  have hn (i : ι) : ‖(projectionFamilyRemainder (S i)).val.val‖≤1 :=
    ((projectionFamilyRemainder (S i)).property.map M.toStarSubalgebra.subtype).norm_le _
  have ht := J.continuous.continuousAt.tendsto.comp
    (projectionFamilyRemainder_tendsto S hS (J x))
  exact tendsto_strong_apply (projectionFamilyRemainder_tendsto S hS)
    (Filter.Eventually.of_forall hn) ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyAdmissible
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Closed quantitative constraints on projection families -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamilyAdmissible_iUnion {ι : Type*} [Preorder ι]
    [NeBot (atTop : Filter ι)] (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (δ : ℝ)
    (S : ι → Set (AlgebraProjection M)) (hS : Monotone S)
    (h : ∀ i, ProjectionFamilyAdmissible J ξ η δ (S i)) :
    ProjectionFamilyAdmissible J ξ η δ (⋃ i, S i) := by
  have hQ (z : H) : Tendsto
      (fun i => ‖(1-modularQuadratic J (projectionFamilyRemainder (S i)).val) z‖^2) atTop
      (𝓝 (‖(1-modularQuadratic J (projectionFamilyRemainder (⋃ i, S i)).val) z‖^2)) := by
    have hc : Tendsto (fun _ : ι => z) atTop (𝓝 z) := tendsto_const_nhds
    have ht := (hc.sub (projectionFamilyQuadratic_tendsto J S hS z)).norm.pow 2
    simpa only [sub_apply,one_apply_eq_self] using ht
  have hR (z : H) : Tendsto
      (fun i => ‖(1-projectionFamilyPinching J (S i)) z‖^2) atTop
      (𝓝 (‖(1-projectionFamilyPinching J (⋃ i, S i)) z‖^2)) := by
    have hc : Tendsto (fun _ : ι => z) atTop (𝓝 z) := tendsto_const_nhds
    have ht := (hc.sub (projectionFamilyPinching_tendsto J S hS z)).norm.pow 2
    simpa only [sub_apply,one_apply_eq_self] using ht
  constructor
  · exact le_of_tendsto_of_tendsto ((hQ ξ).add (hQ η)) ((hR η).const_mul 131072)
      (Eventually.of_forall fun i => (h i).1)
  · exact le_of_tendsto_of_tendsto (hR ξ) ((hR η).const_mul δ)
      (Eventually.of_forall fun i => (h i).2)

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

theorem mem_projectionFamilyRemainderSpace_insert (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (x : H) :
    x ∈ projectionFamilyRemainderSpace (insert p S) ↔
      x ∈ projectionFamilyRemainderSpace S ∧ p.val.val x=0 := by
  simp only [mem_projectionFamilyRemainderSpace,Set.mem_insert_iff,forall_eq_or_imp]
  exact and_comm

theorem projectionFamilyRemainder_insert (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hpq : p≤projectionFamilyRemainder S) :
    (projectionFamilyRemainder (insert p S)).val=(projectionFamilyRemainder S).val-p.val := by
  let q := projectionFamilyRemainder S
  let r := AlgebraProjection.remainder p q hpq
  let q' := projectionFamilyRemainder (insert p S)
  have hrq : q.val.val*r.val.val=r.val.val :=
    congrArg Subtype.val (AlgebraProjection.remainder_le p q hpq)
  have hpr : p.val.val*r.val.val=0 :=
    congrArg Subtype.val (AlgebraProjection.remainder_orthogonal p q hpq)
  have hqr : q'.val.val*r.val.val=r.val.val := by
    ext x
    change (projectionFamilyRemainderSpace (insert p S)).toSubmodule.starProjection
      (r.val.val x)=r.val.val x
    apply Submodule.starProjection_eq_self_iff.mpr
    change r.val.val x ∈ projectionFamilyRemainderSpace (insert p S)
    rw [mem_projectionFamilyRemainderSpace_insert]
    constructor
    · have he := congrArg (fun T : H →L[ℂ] H => T x) hrq
      change q.val.val (r.val.val x)=r.val.val x at he
      rw [← he]
      exact Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace S).toSubmodule _
    · exact congrArg (fun T : H →L[ℂ] H => T x) hpr
  have hrq' : r.val.val*q'.val.val=q'.val.val := by
    ext x
    have hx := (mem_projectionFamilyRemainderSpace_insert S p _).mp
      (Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace (insert p S)).toSubmodule x)
    have he : q.val.val (q'.val.val x)=q'.val.val x :=
      Submodule.starProjection_eq_self_iff.mpr hx.1
    have hz : p.val.val (q'.val.val x)=0 := hx.2
    change q.val.val (q'.val.val x)-p.val.val (q'.val.val x)=q'.val.val x
    rw [he,hz,sub_zero]
  have hrq'' : r.val.val*q'.val.val=r.val.val := by
    have he := congrArg star hqr
    have hsr : star r.val.val=r.val.val := congrArg Subtype.val r.property.isSelfAdjoint.star_eq
    have hsq : star q'.val.val=q'.val.val := congrArg Subtype.val q'.property.isSelfAdjoint.star_eq
    simpa only [star_mul,hsr,hsq] using he
  exact Subtype.ext (hrq'.symm.trans hrq'')

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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyMaximal
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Maximal admissible orthogonal projection families

Chain unions retain the two quantitative inequalities by strong convergence
of the constructed kernel projections.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamilyRemainder_empty :
    (projectionFamilyRemainder (∅ : Set (AlgebraProjection M))).val=1 := by
  apply Subtype.ext
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  change x ∈ projectionFamilyRemainderSpace (∅ : Set (AlgebraProjection M))
  rw [mem_projectionFamilyRemainderSpace]
  simp

theorem projectionFamilyPinching_empty (J : H ≃ₗᵢ⋆[ℂ] H) :
    projectionFamilyPinching J (∅ : Set (AlgebraProjection M))=1 := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  change x ∈ projectionFamilyCommutationSpace J (∅ : Set (AlgebraProjection M))
  rw [mem_projectionFamilyCommutationSpace]
  simp

theorem admissibleOrthogonalFamily_empty (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ η : H) (δ : ℝ) : AdmissibleOrthogonalFamily (M := M) J ξ η δ ∅ := by
  refine ⟨by simp,by simp,?_⟩
  unfold ProjectionFamilyAdmissible
  rw [projectionFamilyRemainder_empty,modularQuadratic_one J hJ,projectionFamilyPinching_empty]
  simp

theorem exists_maximal_admissibleOrthogonalFamily
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (ξ η : H) (δ : ℝ) :
    ∃ S : Set (AlgebraProjection M), Maximal (AdmissibleOrthogonalFamily J ξ η δ) S := by
  apply zorn_subset
  intro C hC hc
  by_cases hne : C.Nonempty
  · let : Nonempty C := hne.to_subtype
    let : IsDirected C (·≤·) := ⟨by
      intro a b
      rcases hc.total a.property b.property with hab | hba
      · exact ⟨b,hab,le_rfl⟩
      · exact ⟨a,le_rfl,hba⟩⟩
    have hAdm : ProjectionFamilyAdmissible J ξ η δ (⋃₀ C) := by
      have hh := projectionFamilyAdmissible_iUnion J ξ η δ (fun i : C => i.val)
        (fun _ _ hij => hij) (fun i => (hC i.property).2.2)
      have he : (⋃ i : C, i.val)=⋃₀ C := by ext p; simp
      rwa [he] at hh
    refine ⟨⋃₀ C,⟨?_,?_,hAdm⟩,fun S hS => Set.subset_sUnion_of_mem hS⟩
    · rintro p ⟨S,hS,hp⟩
      exact (hC hS).1 p hp
    · rintro p ⟨S,hS,hp⟩ q ⟨T,hT,hq⟩ hpq
      rcases hc.total hS hT with hST | hTS
      · exact (hC hT).2.1 (hST hp) hq hpq
      · exact (hC hS).2.1 hp (hTS hq) hpq
  · refine ⟨∅,admissibleOrthogonalFamily_empty J hJ ξ η δ,?_⟩
    intro S hS
    exact False.elim (hne ⟨S,hS⟩)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformPinchingGap
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform test-vector gap for an admissible projection family

A maximal admissible family cannot have a small gap: its remaining corner
would admit the strict refinement already constructed. This is the
projection-family amplification of the local Haagerup witness.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.uniformPinchingRealInner
theorem maximal_admissibleFamily_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (δ : ℝ) (hδ : 0 < δ) (S : Set (AlgebraProjection M))
    (hS : Maximal (AdmissibleOrthogonalFamily J ξ η δ) S) :
    1/16 < 131072*‖(1-projectionFamilyPinching J S) η‖^2 := by
  by_contra hn
  have hgap := le_of_not_gt hn
  let q := projectionFamilyRemainder S
  let A := projectionFamilySelectedPart J S
  have hR : A+modularQuadratic J q.val=projectionFamilyPinching J S := by
    dsimp only [A,projectionFamilySelectedPart,q]
    abel
  obtain ⟨p,hp,hpq,_hproj,hwide,hsmall,hstrict⟩ := exists_strict_pinching_refinement
    J hJ hright hleft ξ hξ huξ hsep hpos hIII hremote η hη huη horth
    A (projectionFamilySelectedPart_isProjection J hJ hright S) q
    (projectionFamilySelectedPart_orthogonal J hJ hright S) δ hδ
    (by rw [hR]; exact hS.prop.2.2.1)
    (by rw [hR]; exact hS.prop.2.2.2) (by rwa [hR])
  have hnew : AdmissibleOrthogonalFamily J ξ η δ (insert p S) := by
    refine ⟨?_,?_,?_⟩
    · intro r hr
      rcases hr with rfl | hr
      · exact hp
      · exact hS.prop.1 r hr
    · apply hS.prop.2.1.insert
      intro r hr _
      have hrq : r.val*q.val=0 := Subtype.ext (projectionFamily_left_annihilate S r hr)
      have hpq' : q.val*p.val=p.val := hpq
      have hrp : r.val*p.val=0 := by
        calc
          _ = r.val*(q.val*p.val) := by rw [hpq']
          _ = 0 := by rw [← mul_assoc,hrq,zero_mul]
      have hpr : p.val*r.val=0 := by
        have he := congrArg star hrp
        simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
          r.property.isSelfAdjoint.star_eq,star_zero] using he
      exact ⟨hpr,hrp⟩
    · unfold ProjectionFamilyAdmissible
      rw [projectionFamilyRemainder_insert S p hpq,
        projectionFamilyPinching_insert J hJ hright S p hpq]
      exact ⟨hwide,hsmall⟩
  have heq : insert p S=S := Set.Subset.antisymm (hS.2 hnew (Set.subset_insert p S))
    (Set.subset_insert p S)
  have heR := projectionFamilyPinching_insert J hJ hright S p hpq
  rw [heq] at heR
  rw [hR,← heR] at hstrict
  exact (lt_irrefl _) hstrict

theorem exists_uniform_pinching_gap_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Set (AlgebraProjection M), AdmissibleOrthogonalFamily J ξ η δ S ∧
      1/16 < 131072*‖(1-projectionFamilyPinching J S) η‖^2 := by
  obtain ⟨S,hS⟩ := exists_maximal_admissibleOrthogonalFamily (M := M) J hJ ξ η δ
  exact ⟨S,hS.prop,maximal_admissibleFamily_gap J hJ hright hleft ξ hξ huξ hsep hpos
    hIII hremote η hη huη horth δ hδ S hS⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_uniform_pinching_gap_oai.{u_1} := @OAI.KadisonKastler.exists_uniform_pinching_gap_oai.{u_1}
