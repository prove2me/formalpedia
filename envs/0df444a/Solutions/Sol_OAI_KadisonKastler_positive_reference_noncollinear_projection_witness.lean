-- Prove2me | solution 1 for OAI.KadisonKastler.positive_reference_noncollinear_projection_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:07:48.9888+00:00
-- url     : https://prove2.me/submissions/cad88013-801b-4e38-a351-7758bb7d24c6

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
import Definitions.Def_Q260K042
import Theorems.Thm_OAI_KadisonKastler_ModularConjugationData_symmetric_projection_witness
import Theorems.Thm_OAI_KadisonKastler_positive_reference_haagerup_witnesses
import Theorems.Thm_OAI_KadisonKastler_tomitaPolarConjugation_eq_of_quadratic_positive

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateOutwardCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Two-vector projection cuts in the original algebra -/

namespace KadisonKastler

open MeasureTheory Finset Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] {M : VonNeumannAlgebra H}

theorem centralVectorDefect_projection (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : H) (p : AlgebraProjection M) :
    centralVectorDefect J ξ p.val.val=(p.val.val-conjugationOperator J p.val.val) ξ := by
  rw [centralVectorDefect_apply,
    show star p.val.val=p.val.val from congrArg Subtype.val p.property.isSelfAdjoint.star_eq]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AngledProjectionWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection witnesses away from the reference line

The orthogonal-vector witness extends to a real unit-circle combination.
The squared sine is kept as a multiplier, so no trigonometric conventions
or division by a small angle enter the subsequent corner argument.
This is the local estimate in Haagerup, Acta Math.158(1987), Lemma2.14.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

omit [CompleteSpace H] in
theorem norm_real_combination_sq_le (x y : H) (c s : ℝ) (hcs : c^2+s^2 ≤ 1) :
    ‖c • x+s • y‖^2 ≤ ‖x‖^2+‖y‖^2 := by
  have hn := norm_add_le (c • x) (s • y)
  simp only [norm_smul,Real.norm_eq_abs] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ |c| * ‖x‖+|s| * ‖y‖)).mpr hn
  have hd := sq_nonneg (|s| * ‖x‖-|c| * ‖y‖)
  have hc := mul_nonneg (sub_nonneg.mpr hcs) (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖))
  nlinarith only [hs,hd,hc,sq_abs c,sq_abs s]

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem norm_sub_sq_le_two (x y : H) :
    ‖x-y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
  have hn := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_sub_le x y)
  nlinarith only [hn,sq_nonneg (‖x‖-‖y‖)]

omit [CompleteSpace H] in
theorem real_combination_defect_lower (T : H →L[ℂ] H) (ξ ζ : H) (c s : ℝ)
    (hcs : c^2+s^2 ≤ 1)
    (hsmall : ‖T ξ‖^2 < s^2/8*‖T ζ‖^2) :
    s^2*‖T ζ‖^2 < 4*‖T (c • ξ+s • ζ)‖^2 := by
  have he : s • T ζ = T (c • ξ+s • ζ)-c • T ξ := by
    rw [map_add,ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.map_smul_of_tower]
    abel
  have hn := norm_sub_sq_le_two (T (c • ξ+s • ζ)) (c • T ξ)
  rw [← he] at hn
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hn
  have hcx : c^2*‖T ξ‖^2 ≤ ‖T ξ‖^2 := by
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith only [hcs,sq_nonneg s])
  nlinarith only [hn,hcx,hsmall]

variable [TopologicalSpace.SeparableSpace H]

theorem ModularConjugationData.angled_projection_witness
    (d : ModularConjugationData M Ω) (hM : TypeIIIFactor M)
    (h : HaagerupCommutatorWitnesses d) (hcyc : DenseRange (algebraVectorMap M Ω))
    (ζ : H) (hζ : d.conjugation ζ=ζ) (hunit : ‖ζ‖=1) (horth : inner ℂ Ω ζ=0)
    (c s : ℝ) (hcs : c^2+s^2 ≤ 1) (hs : 0 < s)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      s^2*(‖p.val.val Ω‖^2+‖p.val.val (c • Ω+s • ζ)‖^2) <
        16384*‖centralVectorDefect d.conjugation (c • Ω+s • ζ) p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        δ*‖centralVectorDefect d.conjugation (c • Ω+s • ζ) p.val.val‖^2 := by
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  obtain ⟨p,hp,hm,hd⟩ := d.symmetric_projection_witness hM h hcyc ζ hζ hunit horth
    (α := s^2/8*min 1 δ)
    (mul_pos (div_pos hs2 (by norm_num : (0 : ℝ)<8)) (lt_min (by norm_num) hδ))
  let T : H →L[ℂ] H := p.val.val-conjugationOperator d.conjugation p.val.val
  have hdΩ : ‖centralVectorDefect d.conjugation Ω p.val.val‖=‖T Ω‖ :=
    congrArg norm (centralVectorDefect_projection d.conjugation Ω p)
  have hdζ : ‖centralVectorDefect d.conjugation ζ p.val.val‖=‖T ζ‖ :=
    congrArg norm (centralVectorDefect_projection d.conjugation ζ p)
  have hdη : ‖centralVectorDefect d.conjugation (c • Ω+s • ζ) p.val.val‖=
      ‖T (c • Ω+s • ζ)‖ :=
    congrArg norm (centralVectorDefect_projection d.conjugation (c • Ω+s • ζ) p)
  rw [hdΩ,hdζ] at hd
  rw [hdζ] at hm
  have hsmall : ‖T Ω‖^2 < s^2/8*‖T ζ‖^2 := hd.trans_le (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (by positivity) (min_le_left _ _)) (sq_nonneg _))
  have hsmallδ : ‖T Ω‖^2 < δ*s^2/8*‖T ζ‖^2 := hd.trans_le (by
    calc
      _ ≤ (s^2/8*δ)*‖T ζ‖^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)) (sq_nonneg _)
      _ = _ := by ring)
  have hlower := real_combination_defect_lower T Ω ζ c s hcs hsmall
  have hmass : ‖p.val.val (c • Ω+s • ζ)‖^2 ≤ ‖p.val.val Ω‖^2+‖p.val.val ζ‖^2 := by
    rw [map_add,ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower]
    exact norm_real_combination_sq_le _ _ c s hcs
  refine ⟨p,hp,?_,?_⟩
  · rw [hdη]
    have hmass' : ‖p.val.val Ω‖^2+‖p.val.val (c • Ω+s • ζ)‖^2 < 4096*‖T ζ‖^2 := by
      nlinarith only [hm,hmass,sq_nonneg ‖p.val.val ζ‖]
    have hmuls := mul_lt_mul_of_pos_left hmass' hs2
    nlinarith only [hmuls,hlower]
  · rw [hdΩ,hdη]
    have hmulδ := mul_lt_mul_of_pos_left hlower hδ
    nlinarith only [hsmallδ,hmulδ]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
theorem modularQuadratic_preserves_positiveCone
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a : Algebra M) {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    modularQuadratic J a η ∈ modularPositiveCone (M := M) J ξ := by
  let C := ConvexCone.hull ℝ (Set.range (fun b : Algebra M => modularQuadratic J b ξ))
  have hC : C ≤ C.comap ((modularQuadratic J a).restrictScalars ℝ).toLinearMap := by
    apply ConvexCone.hull_min
    rintro _ ⟨b,rfl⟩
    change modularQuadratic J a (modularQuadratic J b ξ) ∈ C
    change (modularQuadratic J a * modularQuadratic J b) ξ ∈ C
    rw [modularQuadratic_mul J hJ hright]
    exact ConvexCone.subset_hull ⟨a*b,rfl⟩
  exact map_mem_closure (modularQuadratic J a).continuous hη (fun _ hx => hC hx)

theorem modularPositiveCone_acute
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) (hζ : ζ ∈ modularPositiveCone (M := M) J ξ) :
    0 ≤ inner ℝ η ζ := by
  let C := ConvexCone.hull ℝ (Set.range (fun a : Algebra M => modularQuadratic J a ξ))
  have hgen (a b : Algebra M) :
      0 ≤ inner ℝ (modularQuadratic J a ξ) (modularQuadratic J b ξ) := by
    rw [real_inner_eq_re_inner,← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint,modularQuadratic_star J hJ hright]
    change 0 ≤ (inner ℂ ξ ((modularQuadratic J (star a) * modularQuadratic J b) ξ)).re
    rw [modularQuadratic_mul J hJ hright]
    exact hpos (star a*b)
  have hleft (b : Algebra M) : C ≤ realInnerHalfspace (modularQuadratic J b ξ) := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact hgen a b
  have hh (υ : H) (hυ : υ ∈ C) : C ≤ realInnerHalfspace υ := by
    apply ConvexCone.hull_min
    rintro _ ⟨b,rfl⟩
    change 0 ≤ inner ℝ (modularQuadratic J b ξ) υ
    rw [real_inner_comm]
    exact hleft b hυ
  have hhclosed (υ : H) : IsClosed {v : H | 0 ≤ inner ℝ v υ} :=
    isClosed_le continuous_const (continuous_id.inner continuous_const)
  have hηC (υ : H) (hυ : υ ∈ C) : 0 ≤ inner ℝ η υ :=
    closure_minimal (fun _ hx => hh υ hυ hx) (hhclosed υ) hη
  rw [real_inner_comm]
  apply closure_minimal (s := (C : Set H)) ?_ (hhclosed η) hζ
  intro υ hυ
  change 0 ≤ inner ℝ υ η
  rw [real_inner_comm]
  exact hηC υ hυ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveReal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem modularPositiveCone_fixed
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) : J η = η := by
  have hgen (a : Algebra M) : J (modularQuadratic J a ξ) = modularQuadratic J a ξ := by
    have he : J (modularQuadratic J a ξ) =
        conjugationOperator J a.val (a.val ξ) := by
      change J (a.val (J (a.val (J ξ)))) = J (a.val (J (a.val ξ)))
      rw [hξ]
    rw [he]
    exact congrArg (fun T : H →L[ℂ] H => T ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp (hright a) a.val a.property).symm
  have hh : ConvexCone.hull ℝ (Set.range (fun a : Algebra M => modularQuadratic J a ξ)) ≤
      conjugationFixedCone J := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact hgen a
  exact closure_minimal (fun _ h => hh h)
    (isClosed_eq J.continuous continuous_id) hη

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveReferenceCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Changing the cyclic reference inside the same positive cone

The quadratic positivity and the generated cone are unchanged when the
reference is replaced by a cyclic vector in that cone. These are the
reference-transport facts needed for projection-family amplification.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.positiveReferenceRealInner
variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ=ξ)
  (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))

include hJ hright hpos in
theorem positiveCone_quadratic_nonneg {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) (a : Algebra M) :
    0 ≤ inner ℝ η (modularQuadratic J a η) :=
  modularPositiveCone_acute J hJ hright ξ hpos hη
    (modularQuadratic_preserves_positiveCone J hJ hright ξ a hη)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveReferenceModular
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The polar conjugation is unchanged at positive cyclic references

The old quadratic cone supplies positivity at the new reference. The
proved uniqueness theorem then identifies its constructed conjugation.
-/

namespace KadisonKastler

noncomputable section

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.positiveReferenceModularRealInner
omit [TopologicalSpace.SeparableSpace H] in
theorem positiveCone_quadratic_complex_nonneg
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) (a : Algebra M) :
    0 ≤ inner ℂ η (modularQuadratic J a η) := by
  have hηJ := modularPositiveCone_fixed J hright ξ hξ hη
  have hQa := modularPositiveCone_fixed J hright ξ hξ
    (modularQuadratic_preserves_positiveCone J hJ hright ξ a hη)
  have hc := conjugateIsometry_inner J η (modularQuadratic J a η)
  rw [hηJ,hQa] at hc
  have him := congrArg Complex.im hc
  simp only [Complex.star_def,Complex.conj_im] at him
  constructor
  · exact positiveCone_quadratic_nonneg J hJ hright ξ hpos hη a
  · change (0 : ℝ)=(inner ℂ η (modularQuadratic J a η)).im
    linarith

theorem positiveCone_polar_conjugation
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η))
    (hcyc : DenseRange (algebraVectorMap M η)) :
    tomitaPolarConjugation J η hsep hcyc=J :=
  tomitaPolarConjugation_eq_of_quadratic_positive J hJ hright hleft η
    (modularPositiveCone_fixed J hright ξ hξ hη) hsep hcyc
    (positiveCone_quadratic_complex_nonneg J hJ hright ξ hξ hpos hη)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SymmetricVectorAngle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Orthogonal decomposition of two symmetric unit vectors -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

omit [CompleteSpace H] in
theorem conjugateIsometry_real_smul (J : H ≃ₗᵢ⋆[ℂ] H) (r : ℝ) (ξ : H) :
    J (r • ξ)=r • J ξ := by
  change J ((r : ℂ) • ξ)=(r : ℂ) • J ξ
  rw [J.map_smulₛₗ,Complex.conj_ofReal]

omit [CompleteSpace H] in
theorem symmetric_inner_real (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H)
    (hξ : J ξ=ξ) (hη : J η=η) :
    inner ℂ ξ η=((inner ℂ ξ η).re : ℂ) := by
  have he := conjugateIsometry_inner J ξ η
  rw [hξ,hη] at he
  have hi := congrArg Complex.im he
  simp only [Complex.star_def,Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

omit [CompleteSpace H] in
theorem symmetric_unit_angle_decomposition (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H)
    (hξ : J ξ=ξ) (hη : J η=η) (huξ : ‖ξ‖=1) (huη : ‖η‖=1)
    (hne : η ≠ ξ) (hne' : η ≠ -ξ) :
    ∃ (c s : ℝ) (ζ : H), c=(inner ℂ ξ η).re ∧ 0 < s ∧ c^2+s^2=1 ∧
      J ζ=ζ ∧ ‖ζ‖=1 ∧ inner ℂ ξ ζ=0 ∧ η=c • ξ+s • ζ := by
  let c := (inner ℂ ξ η).re
  let z := η-c • ξ
  have hi : inner ℂ ξ z=0 := by
    change inner ℂ ξ (η-(c : ℂ) • ξ)=0
    rw [inner_sub_right,inner_smul_right,symmetric_inner_real J ξ η hξ hη,
      inner_self_eq_norm_sq_to_K,huξ]
    norm_num [c]
  have hzJ : J z=z := by
    dsimp only [z]
    rw [map_sub,conjugateIsometry_real_smul,hη,hξ]
  have hdecomp : η=c • ξ+z := by dsimp only [z]; abel
  have hin : inner ℂ (c • ξ) z=0 := by
    change inner ℂ ((c : ℂ) • ξ) z=0
    rw [inner_smul_left,hi,mul_zero]
  have hsq : ‖c • ξ+z‖^2=‖c • ξ‖^2+‖z‖^2 := by
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • ξ) z hin
  rw [← hdecomp,huη,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,huξ] at hsq
  have hz : z ≠ 0 := by
    intro hz
    have hc : c^2=1^2 := by simpa only [hz,norm_zero,zero_pow (by decide : 2≠0),
      one_pow,mul_one,add_zero] using hsq.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hc with hc | hc
    · apply hne
      simpa only [hc,one_smul,hz,add_zero] using hdecomp
    · apply hne'
      simpa only [hc,neg_smul,one_smul,hz,add_zero] using hdecomp
  let s := ‖z‖
  have hs : 0 < s := norm_pos_iff.mpr hz
  let ζ := s⁻¹ • z
  have hsz : s • ζ=z := by
    dsimp only [ζ]
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  refine ⟨c,s,ζ,rfl,hs,?_,?_,?_,?_,?_⟩
  · change c^2+‖z‖^2=1
    nlinarith only [hsq]
  · dsimp only [ζ]
    rw [conjugateIsometry_real_smul,hzJ]
  · dsimp only [ζ]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    exact inv_mul_cancel₀ hs.ne'
  · change inner ℂ ξ ((s⁻¹ : ℝ) • z)=0
    change inner ℂ ξ (((s⁻¹ : ℝ) : ℂ) • z)=0
    rw [inner_smul_right,hi,mul_zero]
  · rw [hsz]
    exact hdecomp

variable [TopologicalSpace.SeparableSpace H]

theorem ModularConjugationData.noncollinear_projection_witness
    (d : ModularConjugationData M Ω) (hM : TypeIIIFactor M)
    (h : HaagerupCommutatorWitnesses d) (hcyc : DenseRange (algebraVectorMap M Ω))
    (hΩ : ‖Ω‖=1) (η : H) (hη : d.conjugation η=η) (hunit : ‖η‖=1)
    (hne : η ≠ Ω) (hne' : η ≠ -Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      (1-(inner ℂ Ω η).re^2)*(‖p.val.val Ω‖^2+‖p.val.val η‖^2) <
        16384*‖centralVectorDefect d.conjugation η p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        δ*‖centralVectorDefect d.conjugation η p.val.val‖^2 := by
  obtain ⟨c,s,ζ,hc,hs,hcs,hJζ,huζ,horth,he⟩ :=
    symmetric_unit_angle_decomposition d.conjugation Ω η d.fixes_vector hη hΩ hunit hne hne'
  obtain ⟨p,hp,hm,hd⟩ := d.angled_projection_witness hM h hcyc ζ hJζ huζ horth
    c s hcs.le hs hδ
  have hs2 : s^2=1-(inner ℂ Ω η).re^2 := by rw [hc] at hcs; linarith
  rw [← he,hs2] at hm
  rw [← he] at hd
  exact ⟨p,hp,hm,hd⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveReferenceHaagerup
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Haagerup witnesses at positive references

The spatial coisometries scale on every vector. Positivity identifies the
new reference's polar conjugation with the old one, so the constructed
modular-product-state argument applies again at the new reference.
-/

namespace KadisonKastler

open Generator Generator.Tracial UnitalTomsWinter Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.positiveHaagerupRealInner
theorem positive_reference_noncollinear_projection_witness_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖η‖=1)
    (hsep : Function.Injective (algebraVectorMap M η))
    (hcyc : DenseRange (algebraVectorMap M η))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (ζ : H) (hζ : J ζ=ζ) (huζ : ‖ζ‖=1) (hne : ζ≠η) (hne' : ζ≠-η)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M, p.val≠0 ∧
      (1-(inner ℂ η ζ).re^2)*(‖p.val.val η‖^2+‖p.val.val ζ‖^2) <
        16384*‖centralVectorDefect J ζ p.val.val‖^2 ∧
      ‖centralVectorDefect J η p.val.val‖^2 < δ*‖centralVectorDefect J ζ p.val.val‖^2 := by
  let d := constructedModularConjugationData J η hsep hcyc
    (tomitaPolarConjugation_commutant_eq J η hsep hcyc)
  have hd : d.conjugation=J := positiveCone_polar_conjugation
    J hJ hright hleft ξ hξ hpos hη hsep hcyc
  have hw := positive_reference_haagerup_witnesses J hJ hright hleft ξ hξ hpos
    hη hunit hsep hcyc hIII hremote
  simpa only [hd] using d.noncollinear_projection_witness hIII hw hcyc hunit ζ
    (by rwa [hd]) huζ hne hne' hδ

universe u

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.positive_reference_noncollinear_projection_witness_oai.{u_1} := @OAI.KadisonKastler.positive_reference_noncollinear_projection_witness_oai.{u_1}
